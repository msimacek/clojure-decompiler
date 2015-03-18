(ns decompiler.core
  (:gen-class :main true)
  (:require [clojure.string :as string]
            [clojure.java.io :as io]
            [clojure.pprint :refer [pprint]])
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

(defn get-insns [method]
  (-> method .getCode .getCode InstructionList. .getInstructions))

(defn demunge [what]
  (symbol (Compiler/demunge what)))

(defn insn-method [insn pool]
  (str (.getClassName insn pool) \/ (.getMethodName insn pool)))

(defn insn-field [insn pool]
  (str (.getClassName insn pool) \/ (.getFieldName insn pool)))

(defmulti process-insn
  "Processes one or more instructions, producing altered decompilation context,
  appending the decompile expression tree representation into :result key of
  the context.
  Methods take instruction, instruction index and context map, returning
  altered context map."
  (fn [_ insn & _] (class insn)))

(defn process-insns [context]
  (if (seq (:code context))
    (let [[[index insn] & code] (:code context)]
      (recur (process-insn index insn (assoc context :code code))))
    context))

(defmethod process-insn :default [_ _ context] context)

(defmethod process-insn IFNULL
  [index insn {:keys [code stack result pool] :as context}]
  (let [target (+ index (.getIndex insn))
        [[_ get-false-insn] & code] code
        _ (assert (instance? GETSTATIC get-false-insn))
        _ (assert (= (insn-field get-false-insn pool) "java.lang.Boolean/FALSE"))
        [[_ acmpeq-insn] & code] code
        _ (assert (instance? IF_ACMPEQ acmpeq-insn))
        condition (peek stack)
        stack (pop-n stack 2) ; 1 -1 + 2
        index< #(fn [[i _]] (< i %))
        then (process-insns (assoc context
                                   :code (take-while (index< target) code)))
        end (-> then :result peek :target)
        rest-code (drop-while (index< target) code)
        else (process-insns (assoc context
                                   :code (if end
                                           (take-while (index< end) rest-code)
                                           rest-code)))
        expr {:type :if
              :cond condition
              :else (peek (:stack else))
              :then (peek (:stack then))}]
    (assoc context
           :code (if end (drop-while (index< end) code) ())
           :stack (conj stack expr)
           :result (conj result expr))))

(defmethod process-insn LoadInstruction
  [_ insn {:keys [stack vars] :as context}]
  (assoc context
         :stack (conj stack (nth vars (.getIndex insn)))))

(defmethod process-insn GETSTATIC
  [_ insn {:keys [clazz stack pool fields] :as context}]
  (let [class-name (.getClassName clazz)
        expr (cond
               (= (.getClassName insn pool) class-name)
               (fields (.getFieldName insn pool))
               (= (insn-field insn pool) "java.lang.Boolean/TRUE")
               {:type :const :value true}
               (= (insn-field insn pool) "java.lang.Boolean/FALSE")
               {:type :const :value false}
               :default {:type :get-field
                         :class (.getClassName insn pool)
                         :field (.getFieldName insn pool)})]
    (assoc context :stack (conj stack expr))))

(defmethod process-insn PUTSTATIC
  [_ insn {:keys [clazz stack pool fields] :as context}]
  (if (= (.getClassName insn pool) (.getClassName clazz))
    (assoc context
           :stack (pop stack)
           :fields (assoc fields (.getFieldName insn pool) (peek stack)))))

(defmethod process-insn StoreInstruction
  [_ insn {:keys [stack vars] :as context}]
  (let [index (.getIndex insn)]
    (assoc context
           :stack (pop stack)
           :vars (if-let [local (nth vars index nil)]
                       (if (#{:local :arg} (:type local))
                         (assoc vars index (assoc local :assign (peek stack))))
                       (conj vars {:type :local
                                   :initial (peek stack)
                                   :index index})))))

(defmethod process-insn GotoInstruction
  [index insn {:keys [stack vars result arg-count] :as context}]
  (let [expr (if (== (.getIndex insn) (- index))
               {:type :recur
                :args (subvec vars 1 arg-count)}
               {:type :goto
                :target (+ index (.getIndex insn))})]
    (assoc context
           :code nil
           :result (conj result expr)
           :stack (if (= (:type expr) :recur)
                    (conj stack expr)
                    stack)))) ; recur is expression, goto is auxiliary item

(defmethod process-insn DUP
  [_ _ {:keys [stack] :as context}]
  (assoc context :stack (conj stack (peek stack))))

(derive LDC ::ldc-insn)
(derive LDC_W ::ldc-insn)
(derive LDC2_W ::ldc-insn)

(defmethod process-insn ::ldc-insn
  [_ insn {:keys [stack pool] :as context}]
  (assoc context :stack (conj stack {:type :const :value (.getValue insn pool)})))

(defmethod process-insn ConstantPushInstruction
  [_ insn {:keys [stack] :as context}]
  (assoc context :stack (conj stack {:type :const :value (.getValue insn)})))

(defmethod process-insn ACONST_NULL
  [_ insn {:keys [stack] :as context}]
  (assoc context :stack (conj stack {:type :const :value nil})))

(defmethod process-insn INVOKESTATIC
  [_ insn {:keys [stack pool result] :as context}]
  (let [argc (count (.getArgumentTypes insn pool))
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
    (assoc context
           :stack (conj (pop-n stack argc) expr)
           :result (conj result expr))))

(defmethod process-insn INVOKEINTERFACE
  [_ insn {:keys [stack pool result] :as context}]
  ; (if (= (.getMethodName insn pool) "invoke") ;TODO check type
  (let [argc (count (.getArgumentTypes insn pool))
        expr {:type :invoke
              :args (peek-n stack argc)
              :name (:name (peek-at stack argc))}]
    (assoc context
           :stack (conj (pop-n stack (inc argc)) expr)
           :result (conj result expr))))

(defmethod process-insn ARETURN
  [_ insn {:keys [stack result] :as context}]
  (assoc context
         :code nil
         :result (conj result (peek stack))))

(defn get-indexed-insns [method]
  (let [insns (get-insns method)]
    (map vector (reductions + (cons 0 (map #(.getLength %) insns))) insns)))

(defn method->expr [clazz method & {:as context}]
  (let [arg-count (inc (count (.getArgumentTypes method)))
        context (merge {:code (get-indexed-insns method)
                        :stack []
                        :clazz clazz
                        :method method
                        :fields {}
                        :result []
                        :pool (ConstantPoolGen. (.getConstantPool clazz))
                        :arg-count arg-count
                        :vars (mapv (fn [n] {:type :arg :index n}) (range arg-count))}
                       context)]
    (process-insns context)))

(defn letify [exprs]
  (let [expr (if (vector? exprs) (last exprs) exprs)]
    (if (= (:type expr) :local)
      {:type :let
       :body [expr]
       :locals [expr]}
      (if-let [args (:args expr)]
        (let [new-expr (assoc expr :args (map letify args))]
          new-expr)
        expr))))

(defn render-expr [exprs fn-args]
  ((fn render [exprs]
     (let [expr (if (vector? exprs) (last exprs) exprs)
           args (map render (:args expr ()))
           local-name #(symbol (str "local" (- (:index %) (count fn-args))))] ; TODO more exprs form `do`
       (condp = (:type expr)
         :const (:value expr)
         :invoke (list* (:name expr) args)
         :invoke-static (list* (symbol (str (:class expr) \/ (:method expr))) args)
         :recur (list* 'recur args)
         :get-field (symbol (str (:class expr) \/ (:field expr)))
         :let (list 'let
                    (vec (interleave
                           (map local-name (:locals expr))
                           (map #(render (:initial %)) (:locals expr))))
                    (render (:body expr)))
         :local (local-name expr)
         :if (let [c (render (:cond expr))
                   t (render (:then expr))
                   f (render (:else expr))]
               (if (nil? f)
                 (list 'if c t)
                 (list 'if c t f)))
         :arg (if-let [assign (:assign expr)]
                (render assign)
                (symbol (str "arg" (:index expr)))))))
   exprs))

(defn decompile-fn [clazz]
  (let [[fn-ns fn-name] (map demunge (string/split (.getClassName clazz) #"\$" 2))
        clinit (find-method clazz "<clinit>")
        fields (:fields (method->expr clazz clinit))
        invoke (find-method clazz "invoke") ;TODO multiple arities
        exprs (:result (method->expr clazz invoke :fields fields))
        argc (count (.getArgumentTypes invoke))
        args (mapv #(symbol (str "arg" %)) (range 1 (inc argc)))
        _ (when *debug* (pprint exprs))]
    (list 'defn (symbol fn-name) args
          (-> exprs letify (render-expr args)))))

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
