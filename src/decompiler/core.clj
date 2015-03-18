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
  "Processes one or more instructions, producing altered decompilation context.
  Methods take instruction, instruction index and context map, returning
  altered context map."
  (fn [_ insn & _] (class insn)))

(defn process-insns [context]
  (if (seq (:code context))
    (let [[[index insn] & code] (:code context)]
      (recur (process-insn index insn (assoc context :code code))))
    (if (:return context)
      context
      (assoc context :return (peek (:stack context))))))

(defmethod process-insn :default [_ _ context] context)

(defmethod process-insn IFNULL
  [index insn {:keys [code stack statements pool] :as context}]
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
        end (:goto-target then)
        rest-code (drop-while (index< target) code)
        else (process-insns (assoc context
                                   :code (if end
                                           (take-while (index< end) rest-code)
                                           rest-code)))
        expr {:type :if
              :cond condition
              :else (:return else)
              :then (:return then)}]
    (assoc context
           :code (if end (drop-while (index< end) code) ())
           :stack (conj stack expr)
           :statements (conj statements expr))))

(defmethod process-insn LoadInstruction
  [_ insn {:keys [stack vars] :as context}]
  (assoc context
         :stack (conj stack (nth vars (.getIndex insn)))))

(defmethod process-insn GETSTATIC
  [_ insn {:keys [clazz stack pool fields] :as context}]
  (let [class-name (.getClassName clazz)
        const-map {"java.lang.Boolean/TRUE" true
                   "java.lang.Boolean/FALSE" false
                   "clojure.lang.PersistentList/EMPTY" ()
                   "clojure.lang.PersistentVector/EMPTY" []
                   "clojure.lang.PersistentArrayMap/EMPTY" {}
                   "clojure.lang.PersistentHashSet/EMPTY" #{}}
        field (insn-field insn pool)
        expr (cond
               (= (.getClassName insn pool) class-name)
               (fields (.getFieldName insn pool))
               (contains? const-map field)
               {:type :const :value (const-map field)}
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
  [insn-index insn {:keys [stack vars statements] :as context}]
  (let [index (.getIndex insn)
        existing (nth vars index nil)
        local (if (#{:local :arg} (:type existing))
                (assoc existing :assign (peek stack))
                {:type :local
                 :initial (peek stack)
                 :index index})
        vars (if existing
               (assoc vars index local)
               (conj vars local))
        new-context (assoc context
                           :stack (pop stack)
                           :vars (assoc vars index local))]
    (if existing
      ; will recur or do nothing
      new-context
      ; will form let or loop
      (let [inner-context (process-insns new-context)
            inner-expr (:return inner-context)
            inner-is-binding (#{:let :loop} (:type inner-expr))
            locals (if inner-is-binding
                     (cons local (:locals inner-expr))
                     (list local))
            body (if inner-is-binding (:body inner-expr) (:return inner-context))
            binding-type (or (and inner-is-binding (:type inner-expr))
                             (if (= (:target body) (+ insn-index (.getLength insn)))
                               :loop :let))
            body (if (and (= binding-type :loop) (= (:type body) :recur))
                   (assoc body
                          :args (filter #((set (map :index locals)) (:index %))
                                        (:vars body)))
                   body)
            expr {:type binding-type
                  :locals locals
                  :body body}]
        (assoc inner-context
               :code nil ; it's nil already, just making it obvious
               :return expr))))) ; we wrapped the return into let

(defmethod process-insn GotoInstruction
  [index insn {:keys [stack vars statements arg-count] :as context}]
  (if (neg? (.getIndex insn))
    (assoc context
           :code nil
           :return {:type :recur
                    :target (+ index (.getIndex insn))
                    :vars vars
                    ; :args will be overriden if it's a loop
                    :args (subvec vars 1 arg-count)})
    (assoc context
           :code nil
           :goto-target (+ index (.getIndex insn)))))

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
  [_ insn {:keys [stack pool statements] :as context}]
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
           :statements (conj statements expr))))

(defmethod process-insn INVOKEINTERFACE
  [_ insn {:keys [stack pool statements] :as context}]
  ; (if (= (.getMethodName insn pool) "invoke") ;TODO check type
  (let [argc (count (.getArgumentTypes insn pool))
        expr {:type :invoke
              :args (peek-n stack argc)
              :name (:name (peek-at stack argc))}]
    (assoc context
           :stack (conj (pop-n stack (inc argc)) expr)
           :statements (conj statements expr))))

(defmethod process-insn ARETURN
  [_ insn {:keys [stack statements] :as context}]
  (assoc context
         :code nil
         :stack (pop stack)
         :return (peek stack)))

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
                        :statements []
                        :pool (ConstantPoolGen. (.getConstantPool clazz))
                        :arg-count arg-count
                        :vars (mapv (fn [n] {:type :arg :index n}) (range arg-count))}
                       context)]
    (process-insns context)))

(defn render-expr [exprs fn-args]
  ((fn render [exprs]
     (let [expr (if (vector? exprs) (last exprs) exprs)
           args (map render (:args expr ()))
           local-name #(symbol (str "local" (- (:index %) (count fn-args))))
           render-binding (fn [sym expr]
                            (list sym (vec (interleave
                                             (map local-name (:locals expr))
                                             (map #(render (:initial %)) (:locals expr))))
                                  (render (:body expr))))] ; TODO more exprs form `do`
       (condp = (:type expr)
         :const (:value expr)
         :invoke (list* (:name expr) args)
         :invoke-static (list* (symbol (str (:class expr) \/ (:method expr))) args)
         :recur (list* 'recur args)
         :get-field (symbol (str (:class expr) \/ (:field expr)))
         :let (render-binding 'let expr)
         :loop (render-binding 'loop expr)
         :local (if-let [assign (:assign expr)] (render assign) (local-name expr))
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
        return (:return (method->expr clazz invoke :fields fields))
        argc (count (.getArgumentTypes invoke))
        args (mapv #(symbol (str "arg" %)) (range 1 (inc argc)))
        _ (when *debug* (pprint return))]
    (list 'defn (symbol fn-name) args
          (render-expr return args))))

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
