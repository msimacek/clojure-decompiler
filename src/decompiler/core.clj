(ns decompiler.core
  (:gen-class :main true)
  (:require [clojure.string :as string]
            [clojure.java.io :as io])
  (:import (org.apache.bcel.classfile ClassParser)
           (org.apache.bcel.generic
             ConstantPoolGen InstructionList
             LoadInstruction StoreInstruction ConstantPushInstruction
             GotoInstruction IfInstruction
             ACONST_NULL ARETURN RETURN DUP LDC LDC_W LDC2_W INVOKESTATIC
             PUTSTATIC GETSTATIC INVOKEVIRTUAL INVOKEINTERFACE IFNULL IF_ACMPEQ)))
(def ^:dynamic *debug* false)

(defn pop-n [stack n] (let [c (count stack)] (subvec stack 0 (- c n))))
(defn peek-n [stack n] (let [c (count stack)] (subvec stack (- c n) c)))
(defn peek-at [stack n] (let [c (count stack)] (nth stack (- c n 1))))

(defn find-method [clazz method]
  (first (filter #(= (.getName %) method) (.getMethods clazz))))

(defn get-instructions [method]
  (-> method .getCode .getCode InstructionList. .getInstructions))

(defn demunge [what]
  (symbol (Compiler/demunge what)))

(defn insn-method [insn pool]
  (str (.getClassName insn pool) \/ (.getMethodName insn pool)))

(defn insn-field [insn pool]
  (str (.getClassName insn pool) \/ (.getFieldName insn pool)))

(defn code->expr [clazz method fields indexed-code stack]
  (let [class-name (.getClassName clazz)
        arg-count (inc (count (.getArgumentTypes method)))
        pool (ConstantPoolGen. (.getConstantPool clazz))]
    (loop [[[index insn] & code] indexed-code
           stack stack
           vars (mapv (fn [n] {:type :arg :index n}) (range arg-count))
           fields fields
           result []]
      (if insn
        (condp instance? insn
          IFNULL (let [target (+ index (.getIndex insn))
                       [[_ get-false-insn] & code] code
                       _ (assert (instance? GETSTATIC get-false-insn))
                       _ (assert (= (insn-field get-false-insn pool) "java.lang.Boolean/FALSE"))
                       [[_ acmpeq-insn] & code] code
                       _ (assert (instance? IF_ACMPEQ acmpeq-insn))
                       condition (peek stack)
                       stack (pop-n stack 2) ; 1 -1 + 2
                       index-op #(fn [[i _]] (% i %2))
                       [false-branch _] (code->expr clazz method fields
                                                    (take-while (index-op < target) code) stack)
                       false-branch (peek false-branch)
                       end (:target false-branch)
                       false-branch (:stack-top false-branch false-branch)
                       [true-branch _] (if end
                                         (code->expr clazz method fields
                                                     (take-while (index-op < end)
                                                                 (drop-while (index-op < target) code))
                                                     stack))
                       expr {:type :if
                             :cond condition
                             :false-branch (peek true-branch)
                             :true-branch false-branch}]
                   (recur (drop-while (index-op < (or end target)) code)
                          (conj stack expr)
                          vars fields
                          (conj result expr)))
          GETSTATIC (recur code
                           (conj stack (cond
                                         (= (.getClassName insn pool) class-name)
                                         (fields (.getFieldName insn pool))
                                         (= (insn-field insn pool) "java.lang.Boolean/TRUE")
                                         {:type :const :value true}
                                         (= (insn-field insn pool) "java.lang.Boolean/FALSE")
                                         {:type :const :value false}
                                         :default {:type :get-field
                                                   :class (.getClassName insn pool)
                                                   :field (.getFieldName insn pool)}))
                           vars fields result)
          PUTSTATIC (if (= (.getClassName insn pool) class-name)
                      (recur code ; TODO putstatic on other objects
                             (pop stack)
                             vars
                             (assoc fields (.getFieldName insn pool) (peek stack))
                             result))
          LoadInstruction (recur code
                                 (conj stack (nth vars (.getIndex insn)))
                                 vars fields result)
          StoreInstruction (let [index (.getIndex insn)
                                 vars (if-let [local (nth vars index nil)]
                                        (if (#{:local :arg} (:type local))
                                          (assoc vars index (assoc local :assign (peek stack))))
                                        (conj vars {:type :local
                                                    :initial (peek stack)
                                                    :index index}))]
                             (recur code (pop stack) vars fields result))
          GotoInstruction (let [expr (if (== (.getIndex insn) (- index))
                                       {:type :recur
                                        :args (subvec vars 1 arg-count)}
                                       {:type :goto
                                        :target (+ index (.getIndex insn))
                                        :stack-top (peek stack)})]
                            [(conj result expr) fields])
          DUP (recur code (conj stack (peek stack)) vars fields result)
          LDC (recur code
                     (conj stack {:type :const :value (.getValue insn pool)})
                     vars fields result)
          LDC_W (recur code ;FIXME copypaste
                       (conj stack {:type :const :value (.getValue insn pool)})
                       vars fields result)
          LDC2_W (recur code ;FIXME copypaste
                        (conj stack {:type :const :value (.getValue insn pool)})
                        vars fields result)
          ACONST_NULL (recur code (conj stack {:type :const :value nil}) vars fields result)
          ConstantPushInstruction (recur code
                                         (conj stack {:type :const
                                                      :value (.getValue insn)})
                                         vars fields result)
          INVOKESTATIC (let [argc (count (.getArgumentTypes insn pool))
                             expr (condp = (insn-method insn pool)
                                    "clojure.lang.RT/var"
                                    {:type :var
                                     :ns (demunge (:value (peek-at stack 1)))
                                     :name (demunge (:value (peek stack)))}
                                    "java.lang.Long/valueOf"
                                    (peek stack)
                                    "java.lang.Double/valueOf"
                                    (peek stack)
                                    "java.lang.Integer/valueOf"
                                    ;may appear when boxing int return from interop
                                    (peek stack)
                                    "clojure.lang.RT/readString"
                                    {:type :const
                                     :value (clojure.lang.RT/readString (:value (peek stack)))}
                                    {:type :invoke-static
                                     :class (.getClassName insn pool)
                                     :method (.getMethodName insn pool)
                                     :args (peek-n stack argc)})]
                         (recur code
                                (conj (pop-n stack argc) expr)
                                vars fields
                                (conj result expr)))
          INVOKEVIRTUAL (if (= (.getMethodName insn pool) "getRawRoot") ; TODO and is var
                          (recur code stack vars fields result) ; we have the var already
                          (recur code stack vars fields result)) ; TODO handle this
          INVOKEINTERFACE (if (= (.getMethodName insn pool) "invoke") ;TODO check type
                            (let [argc (count (.getArgumentTypes insn pool))
                                  argc1 (inc argc)
                                  expr {:type :invoke
                                        :args (peek-n stack argc)
                                        :name (:name (peek-at stack argc))}]
                              (recur code
                                     (conj (pop-n stack argc1) expr)
                                     vars fields
                                     (conj result expr)))
                            (recur code (pop stack) vars fields result)) ; TODO handle interop
          ARETURN [(conj result (peek stack)) fields]
          RETURN [result fields]
          (recur code stack vars fields result))
        [(if (seq stack) (conj result (peek stack)) result) fields]))))

(defn method->expr [clazz method fields]
  (let [insns (get-instructions method)]
    (code->expr clazz method fields
                (map vector (reductions + (cons 0 (map #(.getLength %) insns))) insns) [])))

(defn expr->clojure [exprs]
  (let [expr (if (vector? exprs) (last exprs) exprs)
        args #(map expr->clojure (:args expr))] ; TODO more exprs form `do`
    (condp = (:type expr)
      :const (:value expr)
      :invoke (list* (:name expr) (args))
      :invoke-static (list* (symbol (str (:class expr) \/ (:method expr))) (args))
      :recur (list* 'recur (args))
      :get-field (symbol (str (:class expr) \/ (:field expr)))
      :if (let [c (expr->clojure (:cond expr))
                t (expr->clojure (:true-branch expr))
                f (expr->clojure (:false-branch expr))]
            (if (nil? f)
              (list 'if c t)
              (list 'if c t f)))
      :arg (if-let [assign (:assign expr)]
             (expr->clojure assign)
             (symbol (str "arg" (:index expr)))))))

(defn decompile-fn [clazz]
  (let [[fn-ns fn-name] (map demunge (string/split (.getClassName clazz) #"\$" 2))
        clinit (find-method clazz "<clinit>")
        [_ fields] (method->expr clazz clinit {})
        invoke (find-method clazz "invoke") ;TODO multiple arities
        [exprs _] (method->expr clazz invoke fields)
        _ (when *debug* (println exprs))]
    (list 'defn (symbol fn-name)
          (mapv #(symbol (str "arg" %)) (range 1 (inc (count (.getArgumentTypes invoke)))))
          (expr->clojure exprs))))

(defn decompile-class [clazz]
  "Decompiles single class file"
  (cond
    (= (.getSuperclassName clazz) "clojure.lang.AFunction")
    (decompile-fn clazz)))

(defn get-classes [files]
  "Returns file paths as BCEL's JavaClasses"
  (map #(.parse (ClassParser. %)) files))

(defn decompile-classes [paths]
  "Decopmiles all class files at given paths. Recurses into directories"
  (->> paths
       (mapcat #(file-seq (io/file %)))
       (map str)
       (filter #(.endsWith % ".class"))
       (get-classes)
       (keep decompile-class)))

(defn -main [& paths]
  "Entry point. Decompiles class files given as commandline arguments"
  (println (apply str (decompile-classes paths))))
