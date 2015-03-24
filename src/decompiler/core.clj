(ns decompiler.core
  (:gen-class :main true)
  (:require [clojure.string :as string]
            [clojure.java.io :as io]
            [clojure.pprint :refer [pprint]])
  (:import (clojure.lang Reflector)
           (org.apache.bcel.classfile ClassParser)
           (org.apache.bcel.generic
             ConstantPoolGen InstructionList Type
             LoadInstruction StoreInstruction ConstantPushInstruction
             GotoInstruction IfInstruction
             ACONST_NULL ARETURN RETURN DUP LDC LDC_W LDC2_W INVOKESTATIC
             PUTSTATIC GETSTATIC INVOKEVIRTUAL INVOKEINTERFACE INVOKESPECIAL
             NEW IFNULL IFEQ IF_ACMPEQ ANEWARRAY AASTORE)))
(def ^:dynamic *debug* false)

(defn pop-n [stack n] (let [c (count stack)] (subvec stack 0 (- c n))))
(defn peek-n [stack n] (let [c (count stack)] (subvec stack (- c n) c)))
(defn peek-at [stack n] (let [c (count stack)] (nth stack (- c n 1))))

(defn assoc* [coll n item] (if (contains? coll n)
                             (assoc coll n item)
                             (recur (conj coll nil) n item)))

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

(defn process-if
  [index insn condition {:keys [code stack statements pool] :as context}]
  (let [target (+ index (.getIndex insn))
        index< #(fn [[i _]] (< i %))
        then (process-insns (assoc context
                                   :code (take-while (index< target) code)))
        end (:goto-target then)
        rest-code (drop-while (index< target) code)
        else (process-insns (assoc context
                                   :code (if end
                                           (take-while (index< end) rest-code)
                                           rest-code)))
        expr (if (and (true? (-> then :return :value))
                      (false? (-> else :return :value)))
               ; not a real if, just boolean boxing
               condition
               ; real if
               {:type :if
                :cond condition
                :else (:return else)
                :then (:return then)})]
    (assoc context
           :code (if end (drop-while (index< end) code) ())
           :stack (conj stack expr)
           :statements (conj statements expr))))


(defmethod process-insn IFEQ
  [index insn {:keys [stack] :as context}]
  (process-if index insn (peek stack) (assoc context :stack (pop stack))))

(defmethod process-insn IFNULL
  [index insn {:keys [code stack statements pool] :as context}]
  (let [[[_ get-false-insn] & code] code
        _ (assert (instance? GETSTATIC get-false-insn))
        _ (assert (= (insn-field get-false-insn pool) "java.lang.Boolean/FALSE"))
        [[_ acmpeq-insn] & code] code
        _ (assert (instance? IF_ACMPEQ acmpeq-insn))]
    (process-if index insn (peek stack)
                (assoc context :stack (pop-n stack 2))))) ; 1 -1 + 2

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

(defn get-expr [e ]
  (condp = (:type e)
    :if (or (get-expr (:then e)) (get-expr (:else e)))
    :let (get-expr (:body e))
    :loop (get-expr (:body e))
    e))

(defn update-expr [e f]
  (condp = (:type e)
    :if (assoc e
               :then (update-expr (:then e) f)
               :else (update-expr (:else e) f))
    :let (assoc e :body (update-expr (:body e) f))
    :loop (assoc e :body (update-expr (:body e) f))
    (f e)))

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
               (assoc* vars index local))
        new-context (assoc context
                           :stack (pop stack)
                           :vars (assoc vars index local))]
    (if existing
      ; will recur or do nothing
      new-context
      ; will form let or loop
      (let [inner-context (process-insns new-context)
            inner-expr (:return inner-context)
            target-index (+ insn-index (.getLength insn))
            recurs (seq ((fn find-recur [e]
                           (condp = (:type e)
                             :if (concat (find-recur (:then e))
                                         (find-recur (:else e)))
                             :let (find-recur (:body e))
                             :loop (find-recur (:body e))
                             :invoke (mapcat find-recur (:args e))
                             :recur (if (= (:target e) target-index) [e])
                             nil)) inner-expr))
            inner-is-binding (#{:let :loop} (:type inner-expr))
            squash (and (not recurs) inner-is-binding)
            binding-type (if squash (:type inner-expr) (if recurs :loop :let))
            locals (if squash
                     (cons local (:locals inner-expr))
                     (list local))
            body (if squash (:body inner-expr) inner-expr)
            recurs (if squash (:recurs inner-expr) recurs)
            expr {:type binding-type
                  :locals locals
                  :body body
                  :recurs recurs}]
        (dorun (map (fn [e]
                      (swap! (:args e) (constantly
                                         (filter
                                           #((set (map :index locals)) (:index %))
                                           (:vars e)))))
                    recurs))
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
                    :args (atom (subvec vars 1 arg-count))})
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

(defmethod process-insn ANEWARRAY
  [_ insn {:keys [stack] :as context}]
  (assoc context
         :stack (conj (pop stack) {:type :array :values (atom [])})))

(defmethod process-insn AASTORE
  [_ insn {:keys [stack] :as context}]
  (let [array (peek-at stack 2)
        idx (:value (peek-at stack 1))
        item (peek stack)]
    (swap! (:values array) #(assoc* % idx item))
    (assoc context
           :stack (pop-n stack 3))))

(def inline-fns {"clojure.lang.Numbers/add" '+
                 "clojure.lang.Numbers/unchecked_add" '+
                 "clojure.lang.Numbers/addP" '+'
                 "clojure.lang.Numbers/minus" '-
                 "clojure.lang.Numbers/unchecked_minus" '-
                 "clojure.lang.Numbers/minusP" '-'
                 "clojure.lang.Numbers/multiply" '*
                 "clojure.lang.Numbers/unchecked_multiply" '*
                 "clojure.lang.Numbers/multiplyP" '*'
                 "clojure.lang.Numbers/divide" '/
                 "clojure.lang.Numbers/gt" '>
                 "clojure.lang.Numbers/lt" '<
                 "clojure.lang.Numbers/equiv" '==
                 "clojure.lang.Numbers/gte" '>=
                 "clojure.lang.Numbers/lte" '<=
                 "clojure.lang.Numbers/isZero" 'zero?
                 "clojure.lang.Numbers/inc" 'inc
                 "clojure.lang.Numbers/unchecked_inc" 'inc
                 "clojure.lang.Numbers/incP" 'inc'
                 "clojure.lang.Numbers/dec" 'dec
                 "clojure.lang.Numbers/unchecked_dec" 'dec
                 "clojure.lang.Numbers/decP" 'dec'
                 "clojure.lang.Numbers/max" 'max
                 "clojure.lang.Numbers/min" 'min
                 "clojure.lang.Numbers/isPos" 'pos?
                 "clojure.lang.Numbers/isNeg" 'neg?
                 "clojure.lang.Numbers/remainder" 'rem
                 "clojure.lang.Numbers/quotient" 'quot
                 "clojure.lang.Numbers/not" 'bit-not
                 "clojure.lang.Numbers/and" 'bit-and
                 "clojure.lang.Numbers/or" 'bit-or
                 "clojure.lang.Numbers/xor" 'bit-xor
                 "clojure.lang.Numbers/andNot" 'bit-and-not
                 "clojure.lang.Numbers/clearBit" 'bit-clear
                 "clojure.lang.Numbers/setBit" 'bit-set
                 "clojure.lang.Numbers/flipBit" 'bit-flip
                 "clojure.lang.Numbers/testBit" 'bit-test
                 "clojure.lang.Numbers/shiftLeft" 'bit-shift-left
                 "clojure.lang.Numbers/shiftRight" 'bit-shift-right
                 "clojure.lang.Numbers/unsignedShiftRight" 'unsigned-bit-shift-right
                 "clojure.lang.Util/equiv" '=
                 "clojure.lang.Util/compare" 'compare
                 "clojure.lang.RT/count" 'count
                 "clojure.lang.RT/nth" 'nth
                 "clojure.lang.RT/get" 'get
                 "clojure.lang.RT/isReduced" 'reduced?})

(defn eliminate-arg-casts [args arg-types]
  (map (fn [arg arg-type]
         (if (and (:is-cast arg)
                  (= arg-type (:primitive-return arg)))
           (-> arg :args first)
           arg))
       args arg-types))

(defmethod process-insn INVOKESTATIC
  [_ insn {:keys [stack pool statements] :as context}]
  (let [arg-types (.getArgumentTypes insn pool)
        argc (count arg-types)
        identical?-variants {true 'true?
                             false 'false?
                             nil 'nil?}
        coll-consts {"clojure.lang.RT/vector" vec
                     "clojure.lang.RT/set" set
                     "clojure.lang.RT/mapUniqueKeys" #(apply hash-map %)}
        no-ops #{"java.lang.Long/valueOf"
                 "java.lang.Double/valueOf"
                 "java.lang.Integer/valueOf"}
        casts (->> '[char short int long float double]
                   (map #(vector % (Reflector/getStaticField Type (string/upper-case %))))
                   (mapcat #(vector (str "clojure.lang.RT/" (first %) "Cast") %))
                   (apply hash-map))
        method-name (insn-method insn pool)
        top (peek stack)
        top-type (:type top)
        default-fn (fn []
                     {:type :invoke-static
                      :class (.getClassName insn pool)
                      :method (.getMethodName insn pool)
                      :args (eliminate-arg-casts (peek-n stack argc) arg-types)})
        expr (condp #(%1 %2) method-name
               #{"clojure.lang.RT/var"}
               {:type :var
                :ns (demunge (:value (peek-at stack 1)))
                :name (demunge (:value (peek stack)))}
               coll-consts
               {:type :const-coll
                :ctor (coll-consts method-name)
                :value @(:values (peek stack))}
               inline-fns
               {:type :invoke
                :ns 'clojure.core
                :name (inline-fns method-name)
                :args (eliminate-arg-casts (peek-n stack argc) arg-types)
                :primitive-return (.getReturnType insn pool)}
               #{"clojure.lang.Numbers/num"}
               top
               casts :>>
               (fn [[cast-sym cast-class]]
                 (cond
                   (:primitive-return top) top
                   :default {:type :invoke
                             :ns 'clojure.core
                             :name cast-sym
                             :args [top]
                             :is-cast true
                             :primitive-return cast-class}))
               #{"clojure.lang.Util/identical"}
               (let [variant (-> stack peek (:value :not-there) identical?-variants)]
                 {:type :invoke
                  :ns 'clojure.core
                  :name (or variant 'identical?)
                  :args (if variant [(peek-at stack 1)] (peek-n stack argc))})
               no-ops
               (peek stack)
               #{"java.lang.Character/valueOf"}
               {:type :const
                :value (-> stack peek :value char)}
               #{"clojure.lang.RT/keyword"}
               {:type :const
                :value (-> stack peek :value keyword)}
               #{"clojure.lang.RT/readString"}
               {:type :const
                :value (clojure.lang.RT/readString (:value (peek stack)))}
               #{"clojure.lang.Reflector/invokeConstructor"}
               (let [for-name-expr (peek-at stack 1)]
                 (if (and (= (:class for-name-expr) "java.lang.Class")
                          (= (:method for-name-expr) "forName")
                          (= (-> for-name-expr :args first :type) :const))
                   {:type :invoke-ctor
                    :args @(:values top)
                    :class (-> for-name-expr :args first :value)}
                    (default-fn)))
               #{"clojure.lang.Reflector/invokeNoArgInstanceMember"}
               (let [method-or-field (peek-at stack 1)
                     instance (peek-at stack 2)]
                 (if (= (:type method-or-field) :const)
                   {:type :invoke-member
                    :args [instance]
                    :member (:value method-or-field)}
                    (default-fn)))
               #{"clojure.lang.Reflector/invokeInstanceMethod"}
               (let [method-name-expr (peek-at stack 1)]
                 (if (= (:type method-name-expr) :const)
                   {:type :invoke-member
                    :args (cons (peek-at stack 2) @(:values top))
                    :member (:value method-name-expr)}
                    (default-fn)))
               (default-fn))]
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

(defmethod process-insn NEW
  [_ insn {:keys [stack pool] :as context}]
  (assoc context
         :stack (conj stack {:type :new
                             :class (.getLoadClassType insn pool)})))

(defmethod process-insn INVOKESPECIAL
  [_ insn {:keys [stack pool statements] :as context}]
  (let [argc (count (.getArgumentTypes insn pool))
        expr {:type :invoke-ctor
              :args (peek-n stack argc)
              :class (.getClassName insn pool)}]
    ;TODO check it's <init>
    (assoc context
           :stack (conj (pop-n stack (+ argc 2)) expr)
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
         :const-coll ((:ctor expr) (map render (:value expr)))
         :invoke (list* (:name expr) args)
         :invoke-static (list* (symbol (str (:class expr) \/ (:method expr))) args)
         :invoke-ctor (list* (symbol (str (:class expr) \.)) args)
         :invoke-member (list* (symbol (str \. (:member expr))) args)
         :recur (list* 'recur (map render @(:args expr)))
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
