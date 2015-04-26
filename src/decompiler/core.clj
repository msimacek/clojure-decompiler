(ns decompiler.core
  (:gen-class :main true)
  (:require [clojure.string :as string]
            [clojure.java.io :as io]
            [clojure.pprint :refer [pprint]]
            [clojure.tools.logging :as log])
  (:import (clojure.lang Reflector)
           (org.apache.bcel.classfile ClassParser)
           (org.apache.bcel.generic
             ConstantPoolGen InstructionList Type Select
             LoadInstruction StoreInstruction ConstantPushInstruction
             GotoInstruction IfInstruction PopInstruction ArithmeticInstruction
             ACONST_NULL ARETURN RETURN DUP LDC LDC_W LDC2_W INVOKESTATIC
             PUTSTATIC GETSTATIC INVOKEVIRTUAL INVOKEINTERFACE INVOKESPECIAL
             NEW IFNULL IFEQ IF_ACMPEQ ANEWARRAY AASTORE GETFIELD LNEG DNEG
             DADD IADD LADD DADD ISUB DSUB DSUB LSUB IMUL DMUL LMUL DMUL IDIV
             DDIV LDIV IREM LREM LAND LOR LXOR ISHL LSHL ISHR LSHR LUSHR IUSHR
             LCMP DCMPG DCMPL IFNE IFGE IFLE IFGT IFLT IF_ICMPNE)))

(def ^:dynamic *debug* false)

(defn pop-n [stack n] (let [c (count stack)] (subvec stack 0 (- c n))))
(defn peek-n [stack n] (let [c (count stack)] (subvec stack (- c n) c)))
(defn peek-at [stack n] (let [c (count stack)] (nth stack (- c n 1))))

(defn assoc* [coll n item] (if (contains? coll n)
                             (assoc coll n item)
                             (recur (conj coll nil) n item)))

(defmacro conj-if
  ([coll condition item] `(let [c# ~coll] (if ~condition (conj c# ~item) c#)))
  ([coll item] `(let [c# ~coll i# ~item] (if i# (conj c# i#) c#))))

(defn find-methods [clazz method]
  (filter #(= (.getName %) method) (.getMethods clazz)))

(defn find-method [clazz method]
  (first (find-methods clazz method)))

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
    (let [[[index insn] & code] (:code context)
          result (try (process-insn index insn (assoc context :code code))
                   (catch Exception e e))]
      (if (instance? Exception result)
        (assoc context :error {:type :error
                               :cause result
                               :insn insn})
        (recur result)))
    (let [top (if-let [r (:return context)]
                r
                (-> context :stack peek))
          top (if-let [p (:preceding-statement top)]
                top
                (assoc top :preceding-statement (:statement context)))]
      (assoc context :return top))))

(defmethod process-insn :default [_ _ context] context)

(defn index< [x] (fn [[i _]] (< i x)))

(defn process-if
  [condition target {:keys [code stack statement pool] :as context}]
  (let [then (process-insns (assoc context
                                   :code (take-while (index< target) code)
                                   :statement nil))
        end (:goto-target then)
        rest-code (drop-while (index< target) code)
        else (process-insns (assoc context
                                   :code (if end
                                           (take-while (index< end) rest-code)
                                           rest-code)
                                   :statement nil))
        then (:return then)
        else (:return else)
        expr (cond
               (and (true? (:value then))
                    (false? (:value else)))
               ; not a real if, just boolean boxing
               condition

               (= (:type then) :case) ;TODO there may be real if around case
               ; case wrapper
               (assoc then :default else)

               :default
               ; real if
               {:type :if
                :cond (dissoc condition :preceding-statement)
                :preceding-statement (:preceding-statement condition statement)
                :else else
                :then then})]
    (assoc context
           :code (if end (drop-while (index< end) code) ())
           :stack (conj stack expr)
           :statement nil)))


(defmethod process-insn IFEQ
  [index insn {:keys [stack] :as context}]
  (process-if (peek stack)
              (+ index (.getIndex insn))
              (assoc context :stack (pop stack))))

(defmethod process-insn IFNULL
  [index insn {:keys [code stack pool] :as context}]
  (let [[[_ get-false-insn] & code] code
        _ (assert (instance? GETSTATIC get-false-insn))
        _ (assert (= (insn-field get-false-insn pool) "java.lang.Boolean/FALSE"))
        [[_ acmpeq-insn] & code] code
        _ (assert (instance? IF_ACMPEQ acmpeq-insn))]
    (process-if (peek stack)
                (+ index (.getIndex insn) 1) ; skip pop
                (assoc context :stack (pop-n stack 2))))) ; 1 -1 + 2

(def predicate-insns
  {[DCMPG IFGE] '<
   [LCMP IFGE] '<
   [LCMP IFNE] '==
   [DCMPG IFGT] '<=
   [LCMP IFGT] '<=
   [LCMP IFLE] '>
   [DCMPL IFLE] '>
   [LCMP IFLT] '>=
   [DCMPL IFLT] '>=
   [DCMPL IFNE] '==})

(def predicate-insns-unary
  {[DCMPL IFNE] 'zero?
   [LCMP IFNE] 'zero?
   [LCMP IFLE] 'pos?
   [DCMPL IFLE] 'pos?
   [LCMP IFGE] 'neg?
   [DCMPG IFGE] 'neg?})

(derive LCMP ::number-predicate)
(derive DCMPL ::number-predicate)
(derive DCMPG ::number-predicate)

(defmethod process-insn ::number-predicate
  [index insn {:keys [code stack] :as context}]
  (let [[[comp-index comp-insn] & code] code
        insn-types [(class insn) (class comp-insn)]
        unary-predicate (and (-> stack peek :value (= 0))
                             (predicate-insns-unary insn-types nil))
        predicate (or unary-predicate
                      (predicate-insns insn-types))
        condition {:type :invoke
                   :args (if unary-predicate [(peek-at stack 1)] (peek-n stack 2))
                   :fn-expr {:type :var
                             :name predicate}}]
        (process-if condition
                    (+ comp-index (.getIndex comp-insn))
                    (assoc context :stack (pop-n stack 2)))))

(defmethod process-insn IF_ICMPNE
  [index insn {:keys [stack] :as context}]
  (process-if {:type :invoke
               :args (peek-n stack 2)
               :fn-expr {:type :var
                         :name '=}}
              (+ index (.getIndex insn))
              (assoc context :stack (pop-n stack 2))))

(defmethod process-insn Select
  [index insn {:keys [stack code] :as context}]
  (let [add-index (partial + index)
        targets (map add-index (.getIndices insn))
        matches (map (fn [x] {:type :const
                              :value x})
                     (.getMatchs insn))
        default-index (add-index (.getIndex insn))
        thens (map #(process-insns
                          (assoc context
                                 :code (drop-while (index< %) code)))
                   targets)
        thens (map (comp :then :return) thens)
        ; end-index (:goto-target (first thens))
        end-index 73
        default (process-insns
                  (assoc context
                         :code (take-while (index< end-index)
                                           (drop-while (index< default-index) code))))
        expr {:type :case
              :branches (map vector matches thens)
              :cond (peek stack)
              :default (:return default)}]
    (assoc context
           :stack (conj (pop stack) expr)
           :code (drop-while (index< end-index) code))))


(def primitive-artihmetic-unary
  {LNEG '-
   DNEG '-})

(def primitive-artihmetic-binary
  {DADD '+
   IADD '+
   LADD '+
   ISUB '-
   DSUB '-
   LSUB '-
   IMUL '*
   LMUL '*
   DMUL '*
   IDIV '/
   DDIV '/
   LDIV 'quot
   IREM 'rem
   LREM 'rem
   LAND 'bit-and
   LOR 'bit-or
   LXOR 'bit-xor
   ISHL 'bit-shift-left
   LSHL 'bit-shift-left
   ISHR 'bit-shift-right
   LSHR 'bit-shift-right
   LUSHR 'unsigned-bit-shift-right
   IUSHR 'unsigned-bit-shift-right})

(defmethod process-insn ArithmeticInstruction
  [_ insn {:keys [stack] :as context}]
  (let [unary-op (primitive-artihmetic-unary (class insn) nil)
        op (or unary-op (primitive-artihmetic-binary (class insn)))
        expr (cond
               unary-op
               {:type :invoke
                :args [(peek stack)]
                :fn-expr {:type :var
                          :name unary-op}}
               (and (-> stack peek :value (= 1))
                      (#{'+ '-} op))
               {:type :invoke
                :args [(peek-at stack 1)]
                :fn-expr {:type :var
                          :name ({'+ 'inc '- 'dec} op)}}
               :default
               {:type :invoke
                :args (peek-n stack 2)
                :fn-expr {:type :var
                          :name op}})]
    (assoc context
           :stack (conj (pop-n stack (if unary-op 1 2)) expr))))

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

(defn find-local-name
  "Find name of local variable that started to be used at given instruction index"
  [method index]
  (let [table (-> method .getLocalVariableTable .getLocalVariableTable)
        local (seq (filter #(= (.getStartPC %) index) table))]
    (if local (-> local first .getName))))

(defmethod process-insn StoreInstruction
  [insn-index insn {:keys [method stack vars statement] :as context}]
  (let [index (.getIndex insn)
        existing (nth vars index nil)
        local (if (#{:local :arg} (:type existing))
                (assoc existing :assign (peek stack))
                {:type :local
                 :initial (peek stack)
                 :index index
                 :name (find-local-name method (+ insn-index (.getLength insn)))})
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
            expr (if (and (= (:type inner-expr) :case)
                          (identical? (:cond inner-expr) local))
                   (assoc inner-expr :cond (:initial local))
                   {:type binding-type
                    :preceding-statement statement
                    :locals locals
                    :body body
                    :recurs recurs})]
        (dorun (map (fn [e]
                      (swap! (:args e) (constantly
                                         (filter
                                           #((set (map :index locals)) (:index %))
                                           (:vars e)))))
                    recurs))
        (assoc inner-context
               :code nil ; it's nil already, just making it obvious
               :return expr
               :statement nil))))) ; we wrapped the return into let

(defmethod process-insn GotoInstruction
  [index insn {:keys [stack vars arg-count] :as context}]
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

(def casts '#{char short int long float double boolean})

(def inline-fns
  (apply assoc {"clojure.lang.Numbers/add" '+
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
                "clojure.lang.RT/isReduced" 'reduced?}
         (mapcat #(vector (str "clojure.lang.RT/" % "Cast") %) casts)))

(defn eliminate-cast [expr target-type]
  (if (and (= (:type expr) :invoke)
           (-> expr :fn-expr :name casts)
           (= (:return-type expr) target-type))
    (-> expr :args first)
    expr))

(defn eliminate-arg-casts [args arg-types]
  (assert (= (count args) (count arg-types)))
  (map eliminate-cast args arg-types))

(defn generic-invoke-expr
  [insn expr argc {:keys [stack pool statement code] :as context}]
  (let [return-type (.getReturnType insn pool)
        is-void (= return-type Type/VOID)
        expr (assoc expr
                    :preceding-statement (:preceding-statement expr statement)
                    :return-type return-type)]
    (assoc context
           :stack (conj (pop-n stack argc) expr)
           :statement nil
           :code (if is-void (rest code) code)))) ; get rid of aconst_null, store this as expression

(defmethod process-insn INVOKESTATIC
  [_ insn {:keys [stack pool statement] :as context}]
  (let [arg-types (.getArgumentTypes insn pool)
        argc (count arg-types)
        identical?-variants {true 'true?
                             false 'false?
                             nil 'nil?}
        coll-consts {"clojure.lang.RT/vector" vec
                     "clojure.lang.RT/set" set
                     "clojure.lang.RT/map" #(apply hash-map %)
                     "clojure.lang.RT/mapUniqueKeys" #(apply hash-map %)}
        boxing #{"java.lang.Long/valueOf"
                 "java.lang.Double/valueOf"
                 "java.lang.Integer/valueOf"
                 "clojure.lang.Numbers/num"}
        method-name (insn-method insn pool)
        args (eliminate-arg-casts (peek-n stack argc) arg-types)
        expr {:type :invoke-static
              :class (.getClassName insn pool)
              :method (.getMethodName insn pool)
              :args args}
        expr (condp #(%1 %2) method-name
               #{"clojure.lang.RT/var"}
               {:type :var
                :ns (demunge (:value (first args)))
                :name (demunge (:value (second args)))}
               coll-consts
               {:type :const-coll
                :ctor (coll-consts method-name)
                :value @(-> args first :values)}
               inline-fns
               {:type :invoke
                :fn-expr {:type :var
                          :ns 'clojure.core
                          :name (inline-fns method-name)}
                :args args
                :return-type (.getReturnType insn pool)}
               #{"clojure.lang.Util/identical"}
               (let [variant (-> args second (:value :not-there) identical?-variants)]
                 {:type :invoke
                  :fn-expr {:type :var
                            :ns 'clojure.core
                            :name  (or variant 'identical?)}
                  :args (if variant [(first args)] args)})
               boxing
               ; We want to skip cast elimination. If there was a cast, it was
               ; explicit, otherwise the compiler wouldn't immediately box it
               ; again for no reason
               (peek stack)
               #{"java.lang.Character/valueOf"}
               (if (-> args first :type (= :const))
                 {:type :const
                  :value (-> args first :value char)}
                 (peek stack))
               #{"clojure.lang.RT/keyword"}
               {:type :const
                :value (keyword (-> args first :value) (-> args second :value))}
               #{"clojure.lang.Symbol/intern"}
               {:type :invoke
                :fn-expr {:type :var
                          :ns 'clojure.core
                          :name 'quote}
                :args [{:type :const
                        :value (symbol (-> args first :value) (-> args second :value))}]}
               #{"clojure.lang.RT/readString"}
               {:type :const
                :value (clojure.lang.RT/readString (-> args first :value))}
               #{"clojure.lang.Reflector/invokeConstructor"}
               (let [for-name-expr (first args)]
                 (if (and (= (:class for-name-expr) "java.lang.Class")
                          (= (:method for-name-expr) "forName")
                          (= (-> for-name-expr :args first :type) :const))
                   {:type :invoke-ctor
                    :args @(-> args second :values)
                    :class (-> for-name-expr :args first :value)}
                   expr))
               #{"clojure.lang.Reflector/invokeStaticMethod"}
               (let [for-name-expr (first args)
                     method-name (second args)]
                 (if (and (= (:class for-name-expr) "java.lang.Class")
                          (= (:method for-name-expr) "forName")
                          (= (-> for-name-expr :args first :type) :const)
                          (= (:type method-name) :const))
                   {:type :invoke-static
                    :method (:value method-name)
                    :args @(-> args (nth 2) :values)
                    :class (-> for-name-expr :args first :value)}
                   expr))
               #{"clojure.lang.Reflector/invokeNoArgInstanceMember"}
               (let [method-or-field (second args)]
                 (if (= (:type method-or-field) :const)
                   {:type :invoke-member
                    :args [(first args)]
                    :member (:value method-or-field)}
                   expr))
               #{"clojure.lang.Reflector/invokeInstanceMethod"}
               (let [method-name-expr (second args)]
                 (if (= (:type method-name-expr) :const)
                   {:type :invoke-member
                    :args (cons (first args) @(-> args (nth 2) :values))
                    :member (:value method-name-expr)}
                   expr))
               expr)
        is-invoke (.startsWith (name (:type expr)) "invoke")]
    (if is-invoke
      (generic-invoke-expr insn expr argc context)
      (assoc context
             :stack (conj (pop-n stack argc) expr)
             :statement nil))))

(defmethod process-insn GETFIELD
  [_ insn {:keys [stack pool] :as context}]
  (let [top (peek stack)
        field-name (.getFieldName insn pool)
        expr (if (and (= (:type top) :arg)
                      (zero? (:index top)))
               {:type :arg
                :name field-name}
               {:type :invoke-member
                :args [top]
                :member field-name})]
    (assoc context
           :stack (conj (pop stack) expr))))

(defmethod process-insn INVOKEINTERFACE
  [_ insn {:keys [stack pool statement code] :as context}]
  (condp = (insn-method insn pool)
    "clojure.lang.IFn/invoke"
    (let [argc (count (.getArgumentTypes insn pool))
          args (peek-n stack argc)
          expr {:type :invoke
                :preceding-statement statement
                :args args
                :fn-expr (peek-at stack argc)}]
      (assoc context
             :stack (conj (pop-n stack (inc argc)) expr)
             :statement nil))
    "clojure.lang.ILookupThunk/get"
    (let [keyword-site (peek-at stack 1)
          _ (assert (= (:class keyword-site) "clojure.lang.KeywordLookupSite"))
          lookup-target (peek stack)
          end-fn (fn [[_ i]]
                   (not (and (instance? INVOKEINTERFACE i)
                             (= (insn-method i pool) "clojure.lang.ILookupThunk/get"))))
          expr {:type :invoke
                :fn-expr (first (:args keyword-site))
                :args [lookup-target]
                :preceding-statement statement}]
      (assoc context
             ; there was a dup_x2 but we left it a no-op
             ; 2 for this fn, 1 more would be consumed by the skipped body
             :stack (conj (pop-n stack 3) expr)
             :statement nil
             :code (rest (drop-while end-fn code))))
    :>> #(throw (IllegalArgumentException. (str "Unknown interface method: " %)))))

(defmethod process-insn NEW
  [_ insn {:keys [stack pool] :as context}]
  (assoc context
         :stack (conj stack {:type :new
                             :class (.getLoadClassType insn pool)})))

(defmethod process-insn INVOKESPECIAL
  [_ insn {:keys [stack pool statement] :as context}]
  (let [arg-types (.getArgumentTypes insn pool)
        argc (count arg-types)
        expr {:type :invoke-ctor
              :preceding-statement statement
              :args (eliminate-arg-casts (peek-n stack argc) arg-types)
              :class (.getClassName insn pool)}]
    ;TODO check it's <init>
    (assoc context
           ; TODO don't assume that the ojectref was dup'ed
           :stack (conj (pop-n stack (+ argc 2)) expr)
           :statement nil)))

(defmethod process-insn INVOKEVIRTUAL
  [_ insn {:keys [stack pool statement] :as context}]
  (condp = (insn-method insn pool)
    "clojure.lang.Var/getRawRoot"
    context
    "clojure.lang.Var/get"
    context
    "clojure.lang.Var/setMeta"
    (assoc context :stack (pop-n stack 2)) ; TODO metadata
    "java.lang.Number/intValue" ; int cast
    context
    "clojure.lang.Var/bindRoot"
    (let [expr {:type :def
                :var (peek-at stack 1)
                :value (-> stack peek (dissoc :preceding-statement))
                :preceding-statement (-> stack peek :preceding-statement)}]
      (assoc context
             :stack (pop-n stack 2)
             :statement expr))
    (let [arg-types (.getArgumentTypes insn pool)
          argc (count arg-types)
          args (cons (peek-at stack argc) (peek-n stack argc))
          expr {:type :invoke-member
                :args (eliminate-arg-casts args (cons Type/OBJECT arg-types))
                :member (.getMethodName insn pool)}]
      (generic-invoke-expr insn expr (inc argc) context))))

(defmethod process-insn PopInstruction
  [_ insn {:keys [stack statement] :as context}]
  (assert (not statement)) ; all statements should have been picked up by invokes
  (assoc context
         :stack (pop stack)
         :statement (if (-> stack peek :type (= :const)) nil (peek stack))))

(defmethod process-insn ARETURN
  [_ insn {:keys [stack] :as context}]
  (assoc context
         :code nil
         :stack (pop stack)
         :return (peek stack)))

(defmethod process-insn RETURN
  [_ insn {:keys [stack statement] :as context}]
  (assoc context
         :code nil
         :statement nil
         :return statement))

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
                        :pool (ConstantPoolGen. (.getConstantPool clazz))
                        :arg-count arg-count
                        :vars (mapv (fn [n] {:type :arg :index n}) (range arg-count))}
                       context)]
    (process-insns context)))

(defn statement-chain [expr]
  (loop [expr expr
         chain nil]
    (if-let [preceding (:preceding-statement expr)]
      (recur preceding (cons expr chain))
      (cons expr chain))))

(defn render-expr [expr fn-map fn-args]
  (letfn
    [(local-name [expr] (symbol (or (:name expr)
                                    (str "local" (- (:index expr) (count fn-args) -1)))))
     (render-single [expr]
       (let [args (map render-chain-do (:args expr ()))]
         (condp = (:type expr)
           :const (:value expr)
           :const-coll ((:ctor expr) (map render-chain-do (:value expr)))
           :invoke (list* (render-chain-do (:fn-expr expr)) args)
           :invoke-static (list* (symbol (str (:class expr) \/ (:method expr))) args)
           :invoke-ctor (if-let [func (fn-map (:class expr))]
                          (render-fn 'fn func (if-not (:local-name expr) (:name func)))
                          (list* (symbol (str (:class expr) \.)) args))
           :def (let [sym (-> expr :var :name)]
                  (if-let [func (and (-> expr :value :type (= :invoke-ctor))
                                     (fn-map (-> expr :value :class)))]
                    (render-fn 'defn func sym)
                    (list 'def sym (render-chain-do (:value expr)))))
           :invoke-member (list* (symbol (str \. (:member expr))) args)
           :recur (list* 'recur (map render-chain-do @(:args expr)))
           :get-field (symbol (str (:class expr) \/ (:field expr)))
           :let (render-binding 'let expr)
           :loop (render-binding 'loop expr)
           :local (if-let [assign (:assign expr)] (render-chain-do assign) (local-name expr))
           :var (:name expr)
           :if (let [c (render-chain-do (:cond expr))
                     t (render-chain-do (:then expr))
                     f (render-chain-do (:else expr))]
                 (if (nil? f)
                   (list 'if c t)
                   (list 'if c t f)))
           :case (list* 'case (render-chain-do (:cond expr))
                        (concat (mapcat #(map render-chain-do %) (:branches expr))
                                [(render-chain-do (:default expr))]))
           :arg (if-let [assign (:assign expr)]
                  (render-chain-do assign)
                  (symbol (or (:name expr) (fn-args (:index expr)))))
           :error (list 'comment "Couldn't decompile function"
                        (str "Exception:" (:cause expr))
                        (str "Instruction where the exception occured:" (:insn expr)))
           (if *debug* expr (throw (IllegalArgumentException. (str "Cannot render: " expr)))))))

     (render-binding [sym expr]
       (let [local-names (map local-name (:locals expr))]
         (list* sym (vec (interleave
                           local-names
                           (map #(render-chain-do
                                   (assoc (:initial %1) :local-name %2))
                                   (:locals expr) local-names)))
                (render-chain (:body expr)))))

     (fn-arg-syms [args]
       (mapv #(symbol (.getName %)) args))

     (render-arity [arity fn-name]
       (let [args (fn-arg-syms (:args arity))
             argspec (if-let [req (:required-arity arity)]
                       (let [[left right] (split-at req args)]
                         (vec (concat left ['&] right)))
                       args)]
         (cons argspec (render-expr (:body arity) fn-map (vec (cons fn-name args))))))

     (render-fn [sym func fn-name]
       (let [definition (map #(render-arity % fn-name) (:arities func))
             definition (if (= (count definition) 1) (first definition) definition)]
         (cons sym (if fn-name (cons fn-name definition) definition))))

     (render-chain [expr]
       (map render-single (statement-chain expr)))
     (render-chain-do [expr]
       (let [chain (statement-chain expr)]
         (if (> (count chain) 1)
           (list* 'do (map render-single chain))
           (render-single (peek chain)))))]
    (render-chain expr)))

(defn decompile-invoke [clazz invoke fields]
  (let [{:keys [return error]} (method->expr clazz invoke :fields fields)
        argc (count (.getArgumentTypes invoke))
        required-arity (if (= (.getName invoke) "doInvoke")
                         (-> (method->expr clazz (find-method clazz "getRequiredArity"))
                             :return :value))
        var-table (-> invoke .getLocalVariableTable .getLocalVariableTable)]
    (when *debug* (pprint return))
    {:type :fn-single
     :required-arity required-arity
     :args (filter #(<= 1 (.getIndex %) argc) var-table)
     :body (or error return)}))

(defn decompile-fn [clazz]
  (let [name-parts (string/split (.getClassName clazz) #"\$")
        fn-ns (demunge (name-parts 0))
        fn-name (demunge (string/replace (last name-parts) #"__\d+$" ""))
        clinit (find-method clazz "<clinit>")
        {:keys [fields error]}  (method->expr clazz clinit)
        invokes (find-methods clazz "invoke")
        do-invoke (find-method clazz "doInvoke")
        arities (vec (sort-by #(count (:args %))
                              (map #(decompile-invoke clazz % fields) invokes)))]
    {:type :fn
     :class-name (.getClassName clazz)
     :ns fn-ns
     :name (if-not (= fn-name 'fn) fn-name)
     :error error
     :arities (if do-invoke
                (conj arities (decompile-invoke clazz do-invoke fields))
                arities)}))

(defn decompile-init [clazz]
  (let [inits (filter #(.startsWith (.getName %) "__init") (.getMethods clazz))
        fields (reduce #(:fields (method->expr clazz %2 :fields %1)) (cons nil inits))
        statement-types #{:invoke :invoke-static :invoke-ctor :invoke-member
                          :def :if :let :loop}
        load-method (method->expr clazz (find-method clazz "load") :fields fields)
        ; FIXME this looks kinda arbitrary
        body (if (identical? (-> load-method :stack peek) (-> load-method :return))
               (:stack load-method)
               (cons (:return load-method) (:stack load-method)))]
    {:type :init
     :body (conj-if (filter #(statement-types (:type %)) body) (:error load-method))}))

(defn decompile-class [clazz]
  "Decompiles single class file"
  (let [class-name (.getClassName clazz)
        superclass (.getSuperclassName clazz)]
    (cond
      (= superclass "clojure.lang.AFunction")
      (decompile-fn clazz)
      (= superclass "clojure.lang.RestFn")
      (decompile-fn clazz)
      (find-method clazz "load")
      (decompile-init clazz)
      :default
      (log/warn "Unrecognized class " class-name ". Skipping"))))

(defn get-classes [files]
  "Returns file paths as BCEL's JavaClasses"
  (map #(.parse (ClassParser. %)) files))

(defn get-classes-from-paths [paths]
  (->> paths
       (mapcat #(file-seq (io/file %)))
       (map str)
       (filter #(.endsWith % ".class"))
       (get-classes)))

(defn decompile-classes [paths]
  "Decompiles all class files at given paths. Recurses into directories"
  (keep decompile-class (get-classes-from-paths paths)))

(defn render-classes [classes]
  (let [fn-map (into {} (keep #(if (= (:type %) :fn) [(:class-name %) %]) classes))
        init (first (filter #(= (:type %) :init) classes))]
    (if init
      (mapcat #(render-expr % fn-map []) (:body init))
      (log/error "No __init class found in the paths given, please adjust the "
                 "path to include all class files for the project.\n"
                 "Decompiling projects generated by different compilers than "
                 "Clojure compiler, such as javac, are not supported.\n"
                 "For decompling Java projects use a Java decompiler."))))

(defn do-decompile [paths]
  (render-classes (decompile-classes paths)))

(defn -main [& paths]
  "Entry point. Decompiles class files given as commandline arguments"
  (dorun (map pprint (render-classes (decompile-classes paths)))))
