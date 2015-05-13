(ns decompiler.core
  (:gen-class :main true)
  (:require
    [decompiler.data :as data]
    [clojure.string :as string]
    [clojure.java.io :as io]
    [clojure.pprint :as pprint]
    [clojure.tools.cli :as cli]
    [clojure.tools.logging :as log]
    [clj-logging-config.log4j :as log-config])
  (:import
    (clojure.lang Reflector)
    (org.apache.bcel.classfile ClassParser)
    (org.apache.bcel.generic
      ConstantPoolGen InstructionList Type Select LoadInstruction
      StoreInstruction ConstantPushInstruction GotoInstruction IfInstruction
      PopInstruction ArithmeticInstruction
      ACONST_NULL ARETURN RETURN DUP LDC LDC_W LDC2_W INVOKESTATIC PUTSTATIC
      GETSTATIC INVOKEVIRTUAL INVOKEINTERFACE INVOKESPECIAL NEW IFNULL IFEQ
      IF_ACMPEQ IF_ACMPNE IF_ICMPNE ANEWARRAY AASTORE GETFIELD PUTFIELD LCMP
      DCMPL DCMPG INSTANCEOF)))

(log-config/set-logger!)

(def ^:dynamic *debug* false)

(def smap (comp dorun map))

; advanced stack operations
(defn pop-n [stack n] (let [c (count stack)] (subvec stack 0 (- c n))))
(defn peek-n [stack n] (let [c (count stack)] (subvec stack (- c n) c)))
(defn peek-at [stack n] (let [c (count stack)] (nth stack (- c n 1))))

(defn assoc*
  "Assocs item into vector at given index. If the index is not present, pads
  the vector with nils up to the index and inserts the item there."
  [coll n item]
  (if (contains? coll n)
    (assoc coll n item)
    (recur (conj coll nil) n item)))

(defmacro conj-if
  "conjs the item to coll when the condition is true, otherwise leaves it
  unmodified"
  ([coll condition item] `(let [c# ~coll] (if ~condition (conj c# ~item) c#)))
  ([coll item] `(let [c# ~coll i# ~item] (if i# (conj c# i#) c#))))

(defn find-methods [clazz method]
  "Returns class' methods with given name"
  (filter #(= (.getName %) method) (.getMethods clazz)))

(defn find-method [clazz method]
  "Returns class method with given name"
  (first (find-methods clazz method)))

(defn get-insns [method]
  "Returns instruction array of the method"
  (-> method .getCode .getCode InstructionList. .getInstructions))

(defn demunge [what]
  "Inverse operation of clojure.core/munge"
  (symbol (Compiler/demunge (if (symbol? what) (name what) what))))

(defn insn-method [insn pool]
  "Gets qualified method name from invoke instruction in format
  \"className/methodName\""
  (str (.getClassName insn pool) \/ (.getMethodName insn pool)))

(defn insn-field [insn pool]
  "Gets qualified field name from get/put instruction in format
  \"className/fieldName\""
  (str (.getClassName insn pool) \/ (.getFieldName insn pool)))

(defmulti process-insn
  "Processes one or more instructions, producing altered decompilation context.
  Methods take instruction, instruction index and context map, returning
  altered context map."
  (fn [_ insn & _] (class insn)))

(defn process-insns [context]
  "Processes all instructions in decompilation context, returning new
  decompilation context that corresponds to the state of the virtual machine
  after the block of code was executed. Ends when the list of instructions is
  exhausted or when a jump/return instruction is encountered. Is suppose to be
  called recursively for branch instructions. Context need to be initialized.
  (see method->expr documentation for the context format)"
  (if (seq (:code context))
    (let [[[index insn] & code] (:code context) ; pull out one instruction
          ; single processing step
          result (try (process-insn index insn (assoc context :code code))
                   (catch Exception e e))]
      (if (instance? Exception result)
        ; don't fail whole decompilation if just one method cannot be
        ; decompiled
        (assoc context :error {:type :error
                               :cause result
                               :insn insn})
        (recur result)))
    ; no more instructions
    (let [top (or (:return context) ; if there was explicit return, use it
                  (-> context :stack peek)) ; otherwise, use top stack item
          top (if (:preceding-statement top)
                top
                ; if there is a statement left, attach it to the return
                (assoc top :preceding-statement (:statement context)))]
      ; return the final context
      (assoc context :return top))))

; default implementation that doesn't change the context
(defmethod process-insn :default [_ _ context] context)

(defn index<
  "Helper for index less-than comparison when iterating indexed instruction
  lists. Returns a predicate to be used in drop-while/take-while."
  [x]
  (fn [[i _]] (< i x)))

(defn process-if
  "Generic if processor. The condition is prepared by processors of individual
  instructions, this handles the branching part. Also takes index of else
  branch as it needs to be offset depending on the instruction."
  [condition target {:keys [code stack statement pool] :as context}]
  (let [; context after decompiling then branch
        then (process-insns (assoc context
                                   ; take code up else start index
                                   :code (take-while (index< target) code)
                                   :statement nil))
        ; then block always ends with goto, whose index denotes the end of the
        ; whole if expression
        end (:goto-target then)
        rest-code (drop-while (index< target) code)
        ; context after decompiling else branch
        else (process-insns (assoc context
                                   :code (if end
                                           (take-while (index< end) rest-code)
                                           rest-code)
                                   :statement nil))
        ; extract expressions from branches
        then (:return then)
        else (:return else)

        ; the final expression may not be a real if, but auxiliary
        ; compiler-generated construct
        expr (cond
               (and (true? (:value then))
                    (false? (:value else)))
               ; not a real if, just boolean boxing -- (if condition true fals)
               condition

               (= (:type then) :case) ;TODO there may be real if around case
               ; case is sometimes wrapped in an if with instanceof check that
               ; branches to it's default. Get rid of the if, and attach the
               ; else as the case's default. (it doesn't have the default
               ; attached because the default branch was cut from it's code by
               ; take-while
               (assoc then :default else)

               :default
               ; probably real if expression (still may be case branch
               ; auxiliary, will be pulled apart by the caller)
               {:type :if
                ; put the statement from condition to whole if.  it's
                ; semantically the same, but looks prettier
                :cond (dissoc condition :preceding-statement)
                :preceding-statement (:preceding-statement condition statement)
                ; neccessary, if it's case expression inner (synthetic) if
                :end-index end
                :else else
                :then then})]
    (assoc context
           ; cut the remaining code
           :code (if end (drop-while (index< end) code) ())
           :stack (conj stack expr)
           :statement nil)))


(defmethod process-insn IFEQ
  [index insn {:keys [stack] :as context}]
  "Decompiles if expression with primitive boolean condition. The condition is
  on the stack"
  (process-if (peek stack)
              (+ index (.getIndex insn))
              (assoc context :stack (pop stack))))

(defmethod process-insn IFNULL
  [index insn {:keys [code stack pool] :as context}]
  "Decompiles generic if expression that compares against both nil and false.
  It's necessary to process both branchings at once to not emit multiple ifs."
  (let [; pull the getstatic java.lang.Boolean/FALSE instruction
        [[_ get-false-insn] & code] code
        _ (assert (instance? GETSTATIC get-false-insn))
        _ (assert (= (insn-field get-false-insn pool) "java.lang.Boolean/FALSE"))
        ; pull the comparison agains false
        [[_ acmpeq-insn] & code] code
        _ (assert (instance? IF_ACMPEQ acmpeq-insn))]
    (process-if (peek stack)
                (+ index (.getIndex insn) 1) ; skip pop that is between the branches
                ; 1 (ifnull) - 1 (getstatic) + 2 (if_acmpeq) = 2
                (assoc context :stack (pop-n stack 2)))))

; group numeric predicate instructions together to have one method for all of
; them
(derive LCMP ::number-predicate)
(derive DCMPL ::number-predicate)
(derive DCMPG ::number-predicate)

(defmethod process-insn ::number-predicate
  [index insn {:keys [code stack] :as context}]
  "Decompiles if that uses intrinsic predicate (primitive predicate
  instructions)"
  (let [; pull out the following branch instructions
        [[comp-index comp-insn] & code] code
        insn-types [(class insn) (class comp-insn)]
        ; unary predicates are in fact binary and compare against zero
        unary-predicate (and (-> stack peek :value (= 0))
                             (data/predicate-insns-unary insn-types nil))
        ; if it's not unary, it must be binary
        predicate (or unary-predicate
                      (data/predicate-insns insn-types))
        condition {:type :invoke
                   ; different number of arguments for unary and binary
                   :args (if unary-predicate [(peek-at stack 1)] (peek-n stack 2))
                   :fn-expr {:type :var
                             :name predicate}}]
    (process-if condition
                (+ comp-index (.getIndex comp-insn))
                ; always pop 2, unary predicates are implemented with binary
                ; instructions that compare against 0
                (assoc context :stack (pop-n stack 2)))))

(derive IF_ICMPNE ::cmpne)
(derive IF_ACMPNE ::cmpne)

(defmethod process-insn ::cmpne
  [index insn {:keys [stack] :as context}]
  "Decompiles if expression where the condition is a comparison of two
  primitive booleans (compared as integers)"
  (process-if {:type :invoke
               :args (peek-n stack 2)
               :fn-expr {:type :var
                         :name '=}}
              (+ index (.getIndex insn))
              (assoc context :stack (pop-n stack 2))))

(defmethod process-insn INSTANCEOF
  [index insn {:keys [stack pool] :as context}]
  "Decompiles instance? predicate"
  (let [of-class {:type :var
                  :name (-> (.getType insn pool) str symbol)}
        expr {:type :invoke
              :fn-expr {:type :var
                        :name 'instance?}
              :args [of-class (peek stack)]}]
  (assoc context
         :stack (conj (pop stack) expr))))

(defmethod process-insn Select
  [index insn {:keys [stack code] :as context}]
  "Decompiles lookupswitch and tableswitch. Produces a case expression. If it's
  wrapped in if, the default branch cannot be decompiled now, and needs to be
  specially handled by the wrapping if."
  (let [; indices are offsets, we need absolute values to be able to compare.
        ; helper function converts them to absolute
        add-index (partial + index)
        ; indices of branches. There may be a lot of them pointing to the same
        ; index
        targets (map add-index (.getIndices insn))
        ; index of the default branch. It may be out of bounds now
        default-index (add-index (.getIndex insn))
        ; process individual branches and get their expressions
        thens (map #(-> (process-insns
                          (assoc context
                                 :code (drop-while (index< %) code)))
                        :return)
                   targets)
        ; there are always if's in the branches that verify the jump, we get
        ; the condition from them (the case matches are likely just hashes)
        matches (map (comp second :args #(:cond % %)) thens)
        ; the else branch points at default, their end index is therefore the
        ; end index of whole case expression
        end-index (first (keep :end-index thens))
        ; we're intrested only in then branches as the else branches always
        ; point to default
        thens (map #(:then % {:type :const ; process-if may have confused real
                                           ; if expr with boolean unboxing.
                                           ; FIXME this is just a workaround
                              :value true})
                   thens)
        ; try to get the default if we're not wrapped in if
        default (process-insns
                  (assoc context
                         :code (take-while (index< end-index)
                                           (drop-while (index< default-index) code))))
        ; the main condition of the case upo which we perform the jump
        condition (peek stack)
        ; get rid of shifting and masking
        condition (if (and (-> condition :fn-expr :name (= 'bit-and))
                           (-> condition :args first :fn-expr :name (= 'bit-shift-right)))
                    (-> condition :args first :args first)
                    condition)
        ; get rid of hash computations
        condition (if (and (-> condition :class (= "clojure.lang.Util"))
                           (-> condition :method (= "hash")))
                    (-> condition :args first)
                    condition)

        expr {:type :case
              ; filter out empty branches (point to default in packed
              ; tableswitch)
              :branches (filter identity (map #(if-not (nil? %1) [%1 %2]) matches thens))
              :cond condition
              :default (:return default)}]
    (assoc context
           :stack (conj (pop stack) expr)
           :code (drop-while (index< end-index) code))))

(defmethod process-insn ArithmeticInstruction
  [_ insn {:keys [stack] :as context}]
  "Processes arithmetic instructions and returns expresison with corresponding
  Clojure function call"
  (let [; get the operation symbol
        unary-op (data/primitive-artihmetic-unary (class insn) nil)
        op (or unary-op (data/primitive-artihmetic-binary (class insn)))

        ; expression will be a regular function call to one of the functions
        ; with symbolic names (such as +) that are special-cased by the Clojure
        ; compiler
        expr (cond
               unary-op
               ; handle unary operation
               {:type :invoke
                :args [(peek stack)]
                :fn-expr {:type :var
                          :name unary-op}}

               (and (-> stack peek :value (= 1))
                    (#{'+ '-} op))
               ; inc/dec are emitted as addition/subtraction of 1
               {:type :invoke
                :args [(peek-at stack 1)]
                :fn-expr {:type :var
                          ; produce inc/dec instead of (+ x 1)/(- x 1)
                          :name ({'+ 'inc '- 'dec} op)}}

               :default
               ; handle binary operation
               {:type :invoke
                :args (peek-n stack 2)
                :fn-expr {:type :var
                          :name op}})]
    (assoc context
           ; inc/dec still need to pop 2 stack items
           :stack (conj (pop-n stack (if unary-op 1 2)) expr))))

(defmethod process-insn LoadInstruction
  [_ insn {:keys [stack vars] :as context}]
  "Loads local variable (or function argument) and puts it onto stack"
  (assoc context
         ; get the variable from context by it's index
         :stack (conj stack (nth vars (.getIndex insn)))))

(defmethod process-insn GETSTATIC
  [_ insn {:keys [clazz stack pool fields] :as context}]
  "Produces interop call to retrieve static variable of a class, or a constant
  in special cases."
  (let [class-name (.getClassName clazz)
        ; map of getstatic invocations that represent Clojure's constants
        const-map {"java.lang.Boolean/TRUE" true
                   "java.lang.Boolean/FALSE" false
                   "clojure.lang.PersistentList/EMPTY" ()
                   "clojure.lang.PersistentVector/EMPTY" []
                   "clojure.lang.PersistentArrayMap/EMPTY" {}
                   "clojure.lang.PersistentHashSet/EMPTY" #{}}
        ; field qualified name
        field (insn-field insn pool)
        ; final expression
        expr (cond
               (= (.getClassName insn pool) class-name)
               ; constant stored on the current function object, get it from
               ; class fields in the context
               (fields (.getFieldName insn pool))

               (contains? const-map field)
               ; boolean constant or empty collection constant
               {:type :const :value (const-map field)}

               :default
               ; interop static field retrieval
               {:type :get-field
                :class (.getClassName insn pool)
                :field (.getFieldName insn pool)})]
    (assoc context :stack (conj stack expr))))

(defmethod process-insn PUTSTATIC
  [_ insn {:keys [clazz stack pool fields] :as context}]
  "Initializes static field of this class in the context or produces interop
  call to set! a static field."
  (if (= (.getClassName insn pool) (.getClassName clazz))
    (assoc context
           :stack (pop stack)
           :fields (assoc fields (.getFieldName insn pool) (peek stack)))))

(defn find-local-name
  [method index]
  "Find name of local variable that began to be used at given instruction index"
  (let [table (-> method .getLocalVariableTable .getLocalVariableTable)
        local (seq (filter #(= (.getStartPC %) index) table))]
    (if local (-> local first .getName))))

(defmethod process-insn StoreInstruction
  [insn-index insn {:keys [method stack vars statement] :as context}]
  "If the local variable didn't exist already, produces a let or loop
  expression depending on the body. Otherwise attaches the expression to be
  assigned to the local in the context alongside it's initial value"
  (let [index (.getIndex insn)
        ; get the local variable if it exists
        existing (nth vars index nil)
        ; make the local to be stored in the context
        local (if (#{:local :arg} (:type existing))
                ; it already exists, this is second assignment (in recur)
                (assoc existing :assign (peek stack))
                ; it's a new local variable
                {:type :local
                 :initial (peek stack)
                 :index index
                 :name (find-local-name method (+ insn-index (.getLength insn)))})
        ; altered vector of vars for the new context
        vars (assoc* vars index local)
        ; we need to capture the whole body, therefore we need to recurse. For
        ; that we need a new context for the body. It gets all the remaining
        ; code
        new-context (assoc context
                           :stack (pop stack)
                           :vars (assoc vars index local))]
    (if existing
      ; will recur or do nothing
      new-context
      ; will form let or loop
      (let [; processed body context
            inner-context (process-insns new-context)
            inner-expr (:return inner-context)
            ; absolute index of this instruction
            target-index (+ insn-index (.getLength insn))
            ; find recurs (goto instructions) in the body. That's the only
            ; indication that we can use to distinguish between let and loop
            recurs (seq ((fn find-recur [e]
                           (condp = (:type e)
                             ; expression tree traversal
                             :if (concat (find-recur (:then e))
                                         (find-recur (:else e)))
                             :let (find-recur (:body e))
                             :loop (find-recur (:body e))
                             :invoke (mapcat find-recur (:args e))
                             :recur (if (= (:target e) target-index) [e])
                             nil)) inner-expr))
            ; single let expression with multiple bindings translates to
            ; multiple stores. We peek to the body, if there's a let, it should
            ; probably be merged with this one
            inner-is-binding (#{:let :loop} (:type inner-expr))
            ; determine whether we should merge it with inner let.
            ; not if inner is let and this is loop
            squash (and (not recurs) inner-is-binding)
            ; finally determine whether we're decompiling let or loop
            binding-type (if squash (:type inner-expr) (if recurs :loop :let))
            ; produce list of locals in this binding
            locals (if squash
                     (cons local (:locals inner-expr))
                     (list local))
            ; perform the inner merge if needed
            body (if squash (:body inner-expr) inner-expr)
            recurs (if squash (:recurs inner-expr) recurs)
            ; produce final expression
            expr (if (and (= (:type inner-expr) :case)
                          (identical? (:cond inner-expr) local))
                   ; auxiliary generated around case. Get rid of it
                   (assoc inner-expr :cond (:initial local))

                   ; real let/loop
                   {:type binding-type
                    :preceding-statement statement
                    :locals locals
                    :body body
                    :recurs recurs})]

        ; propagate locals to recur. TODO do this without atoms
        (smap (fn [e]
                      (swap! (:args e) (constantly
                                         (filter
                                           #((set (map :index locals)) (:index %))
                                           (:vars e)))))
                    recurs)

        (assoc inner-context
               :code nil ; it's nil already, just making it obvious
               :return expr
               :statement nil)))))

(defmethod process-insn GotoInstruction
  [index insn {:keys [stack vars arg-count] :as context}]
  "Ends the processing of current code slice. If pointing forwards, it's an end
  of then branch of if expression and propagates the jump index. Otherwise it's
  recur"
  (if (neg? (.getIndex insn))
    ; it's recur (either in a loop, or whole function)
    (assoc context
           :code nil
           :return {:type :recur
                    ; propagate absolute jump index
                    :target (+ index (.getIndex insn))
                    :vars vars
                    ; :args will be overriden later if it's a loop
                    ; otherwise it's a tail-recur of function and the arguments
                    ; are the function's argument
                    :args (atom (subvec vars 1 arg-count))})
    ; it's end of then branch of an if expression
    (assoc context
           :code nil
           ; propagate the index to containing if
           :goto-target (+ index (.getIndex insn)))))

(defmethod process-insn DUP
  [_ _ {:keys [stack] :as context}]
  "Duplicates top stack item"
  (assoc context :stack (conj stack (peek stack))))

; group of constatn load instructions
(derive LDC ::ldc-insn)
(derive LDC_W ::ldc-insn)
(derive LDC2_W ::ldc-insn)

(defmethod process-insn ::ldc-insn
  [_ insn {:keys [stack pool] :as context}]
  "Pushes constant on the stack"
  (assoc context :stack (conj stack {:type :const :value (.getValue insn pool)})))

(defmethod process-insn ConstantPushInstruction
  [_ insn {:keys [stack] :as context}]
  "Pushes constant on the stack"
  (assoc context :stack (conj stack {:type :const :value (.getValue insn)})))

(defmethod process-insn ACONST_NULL
  [_ insn {:keys [stack] :as context}]
  "Pushes null on the stack"
  (assoc context :stack (conj stack {:type :const :value nil})))

(defmethod process-insn ANEWARRAY
  [_ insn {:keys [stack] :as context}]
  "Creates new array expression"
  (assoc context
         ; the expression needs to be mutable as following instruction will
         ; insert values to the array
         :stack (conj (pop stack) {:type :array :values (atom [])})))

(defmethod process-insn AASTORE
  [_ insn {:keys [stack] :as context}]
  "Stores value in an array"
  (let [array (peek-at stack 2)
        idx (:value (peek-at stack 1))
        item (peek stack)]
    ; mutate the expression in place
    (swap! (:values array) #(assoc* % idx item))
    (assoc context
           ; aastore doesn't push the array back
           :stack (pop-n stack 3))))

(defn eliminate-cast [expr target-type]
  "Remove cast that was injected by the compiler or returns the expression
  unchanged"
  (if (and (= (:type expr) :invoke)
           (-> expr :fn-expr :name data/casts)
           ; compare the return types to be sure we can remove the cast
           (= (:return-type expr) target-type))
    (-> expr :args first)
    expr))

(defn eliminate-arg-casts [args arg-types]
  "Removes compiler injected casts from arguments list"
  (assert (= (count args) (count arg-types)))
  (map eliminate-cast args arg-types))

(defn generic-invoke-expr
  [insn expr argc {:keys [stack pool statement code] :as context}]
  "Produce function invocation expression"
  (let [return-type (.getReturnType insn pool)
        is-void (= return-type Type/VOID)
        expr (assoc expr
                    :preceding-statement (:preceding-statement expr statement)
                    :return-type return-type)]
    (assoc context
           :stack (conj (pop-n stack argc) expr)
           :statement nil
           ; void calls don't push anything and are followed by aconst_null
           ; get rid of aconst_null, store this as expression instead
           :code (if is-void (rest code) code))))

(defmethod process-insn INVOKESTATIC
  [_ insn {:keys [stack pool statement] :as context}]
  "Produces static method invocation interop call or various inline function
  invocations"
  (let [arg-types (.getArgumentTypes insn pool)
        argc (count arg-types)
        ; true?, false?, nil? are implemented by calling identical
        identical?-variants {true 'true?
                             false 'false?
                             nil 'nil?}
        ; collection constant constructors
        coll-consts {"clojure.lang.RT/vector" vec
                     "clojure.lang.RT/set" set
                     "clojure.lang.RT/map" #(apply hash-map %)
                     "clojure.lang.RT/mapUniqueKeys" #(apply hash-map %)}
        ; primitive type boxing methods to be eliminated
        boxing #{"java.lang.Long/valueOf"
                 "java.lang.Double/valueOf"
                 "java.lang.Integer/valueOf"
                 "clojure.lang.Numbers/num"}
        ; get qualified name
        method-name (insn-method insn pool)
        ; get argument list with eliminated casts
        args (eliminate-arg-casts (peek-n stack argc) arg-types)
        ; base for newly generated expression
        expr {:type :invoke-static
              :class (.getClassName insn pool)
              :method (.getMethodName insn pool)
              :args args}
        expr (condp #(%1 %2) method-name
               #{"clojure.lang.RT/var"}
               ; interns a var, produce var expression instead of method call
               {:type :var
                :ns (demunge (:value (first args)))
                :name (demunge (:value (second args)))}

               coll-consts
               ; collection constant constructed from an array on the stack
               {:type :const-coll
                :ctor (coll-consts method-name)
                :value @(-> args first :values)}

               data/inline-fns
               ; inline function. Let's uninline it
               {:type :invoke
                :fn-expr {:type :var
                          :ns 'clojure.core
                          :name (data/inline-fns method-name)}
                :args args
                :return-type (.getReturnType insn pool)}

               #{"clojure.lang.Util/identical"}
               ; either identical? or one of true?, false?, nil?
               (let [variant (-> args second (:value :not-there) identical?-variants)]
                 {:type :invoke
                  :fn-expr {:type :var
                            :ns 'clojure.core
                            :name  (or variant 'identical?)}
                  :args (if variant [(first args)] args)})

               boxing
               ; automatic boxing, get rid of it
               ; we want to skip cast elimination. If there was a cast, it was
               ; explicit, otherwise the compiler wouldn't immediately box it
               ; again for no reason
               (peek stack)

               #{"java.lang.Character/valueOf"}
               ; character constant
               (if (-> args first :type (= :const))
                 {:type :const
                  :value (-> args first :value char)}
                 (peek stack))

               #{"clojure.lang.RT/keyword"}
               ; keyword constant
               {:type :const
                :value (keyword (-> args first :value) (-> args second :value))}

               #{"clojure.lang.Symbol/intern"}
               ; symbol constant, we need to wrap it into quote
               {:type :const
                :value (symbol (-> args first :value) (-> args second :value))}

               #{"clojure.lang.RT/readString"}
               ; BigDecimal or BigInt constant, Clojure will parse it for us
               {:type :const
                :value (clojure.lang.RT/readString (-> args first :value))}

               #{"java.util.regex.Pattern/compile"}
               ; regular expression constant
               (let [arg (first args)]
                 (if (= (:type arg) :const)
                   {:type :const
                    :value (java.util.regex.Pattern/compile (:value arg))}
                   expr))

               #{"clojure.lang.Reflector/invokeConstructor"}
               ; reflective call to constructor, will produce interop
               ; expression of ctor invocation if the pattern matches
               (let [for-name-expr (first args)]
                 (if (and (= (:class for-name-expr) "java.lang.Class")
                          (= (:method for-name-expr) "forName")
                          (= (-> for-name-expr :args first :type) :const))
                   ; it's generated
                   {:type :invoke-ctor
                    :args @(-> args second :values)
                    :class (-> for-name-expr :args first :value)}
                   ; the pattern didn't match, it was probably called manually
                   expr))

               #{"clojure.lang.Reflector/invokeStaticMethod"}
               ; reflective call to static method, will produce interop
               ; expression of static method invocation if the pattern matches
               (let [for-name-expr (first args)
                     method-name (second args)]
                 (if (and (= (:class for-name-expr) "java.lang.Class")
                          (= (:method for-name-expr) "forName")
                          (= (-> for-name-expr :args first :type) :const)
                          (= (:type method-name) :const))
                   ; it's generated
                   {:type :invoke-static
                    :method (:value method-name)
                    :args @(-> args (nth 2) :values)
                    :class (-> for-name-expr :args first :value)}
                   ; the pattern didn't match, it was probably called manually
                   expr))

               #{"clojure.lang.Reflector/invokeNoArgInstanceMember"}
               ; reflective call to instance method or field, will produce
               ; interop expression of instance method invocation if the
               ; pattern matches
               (let [method-or-field (second args)]
                 (if (= (:type method-or-field) :const)
                   ; it's generated
                   {:type :invoke-member
                    :args [(first args)]
                    :member (:value method-or-field)}
                   ; the pattern didn't match, it was probably called manually
                   expr))

               #{"clojure.lang.Reflector/invokeInstanceMethod"}
               ; reflective call to instance method, will produce interop
               ; expression of instance method invocation if the pattern
               ; matches
               (let [method-name-expr (second args)]
                 (if (= (:type method-name-expr) :const)
                   ; it's generated
                   {:type :invoke-member
                    :args (cons (first args) @(-> args (nth 2) :values))
                    :member (:value method-name-expr)}
                   ; the pattern didn't match, it was probably called manually
                   expr))
               ; default, keep it as static method invocation interop
               expr)
               is-invoke (.startsWith (name (:type expr)) "invoke")]
  (if is-invoke
    (generic-invoke-expr insn expr argc context)
    (assoc context
           :stack (conj (pop-n stack argc) expr)
           :statement nil))))

(defmethod process-insn GETFIELD
  [_ insn {:keys [stack pool] :as context}]
  "If the accessed class is this function, produces closure binding access.
  Otherwise, produces field acces interop expression."
  (let [top (peek stack)
        field-name (.getFieldName insn pool)
        expr (if (and (= (:type top) :arg)
                      ; 0th argument is reference to this function
                      (zero? (:index top)))
               ; closure captured binding
               {:type :arg
                :name field-name}
               ; interop field access
               {:type :invoke-member
                :args [top]
                :member field-name})]
    (assoc context
           :stack (conj (pop stack) expr))))

(defmethod process-insn PUTFIELD
  [_ insn {:keys [stack pool statement] :as context}]
  "Produces a set! call that sets instance field of an object"
  (let [value (eliminate-cast (peek stack) (.getFieldType insn pool))
        obj (peek-at stack 1)
        expr {:type :set-field
              :preceding-statement statement
              :field (.getFieldName insn pool)
              :target obj
              :value value}]
    (assoc context
           ; The object was dup'ed by dup_x1. We ignore dup_x1, so we don't
           ; need to pop it
           :stack (conj (pop stack) expr)
           :statement nil)))

(defmethod process-insn INVOKEINTERFACE
  [_ insn {:keys [stack pool statement code] :as context}]
  "Producess either keyword lookup or Clojure function call"
  (condp = (insn-method insn pool)
    "clojure.lang.IFn/invoke"
    ; Clojure function call
    (let [argc (count (.getArgumentTypes insn pool))
          args (peek-n stack argc)
          expr {:type :invoke
                :preceding-statement statement
                :args args
                ; which function was called is on stack, probably in a var
                :fn-expr (peek-at stack argc)}]
      (assoc context
             :stack (conj (pop-n stack (inc argc)) expr)
             :statement nil))

    "clojure.lang.ILookupThunk/get"
    ; keyword lookup, we need to get rid of tons of boilerplate
    (let [; the lookupsite object containing reference to the actual keyword
          keyword-site (peek-at stack 1)
          _ (assert (= (:class keyword-site) "clojure.lang.KeywordLookupSite"))
          ; the argument in which the lookup is perfromed
          lookup-target (peek stack)
          ; the boilerplate is delimited by another call to ILookupThunk/get
          ; let's just throw instructions away until we hit it
          end-fn (fn [[_ i]]
                   (not (and (instance? INVOKEINTERFACE i)
                             (= (insn-method i pool) "clojure.lang.ILookupThunk/get"))))
          expr {:type :invoke
                ; get the keyword
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
  "Creates new instance of an object as an expression"
  (assoc context
         :stack (conj stack {:type :new ; we don't actually use it later
                             :class (.getLoadClassType insn pool)})))

(defmethod process-insn INVOKESPECIAL
  [_ insn {:keys [stack pool statement] :as context}]
  "Produces constructor call interop expression"
  (let [arg-types (.getArgumentTypes insn pool)
        argc (count arg-types)
        expr {:type :invoke-ctor
              :preceding-statement statement
              :args (eliminate-arg-casts (peek-n stack argc) arg-types)
              :class (.getClassName insn pool)}]
    ;TODO check it's <init>
    (assoc context
           ; the stack item is the new instance expression and we assume it was
           ; duped so we can store the whole expression back
           :stack (conj (pop-n stack (+ argc 2)) expr)
           :statement nil)))

(defmethod process-insn INVOKEVIRTUAL
  [_ insn {:keys [stack pool statement] :as context}]
  "Produce interop instance method call, def statement or nothing"
  (condp = (insn-method insn pool)
    "clojure.lang.Var/getRawRoot"
    ; derefences var, no-op from our POV
    context

    "clojure.lang.Var/get"
    ; derefences var, no-op from our POV
    context

    "clojure.lang.Var/setMeta"
    ; we don't handle metadata now, just keep the stack in sync
    (assoc context :stack (pop-n stack 2)) ; TODO metadata

    "java.lang.Number/intValue"
    ; int cast generated in case condition, get rid of it
    context

    "clojure.lang.Var/bindRoot"
    ; def statement
    (let [expr {:type :def
                :var (peek-at stack 1)
                ; pull statement from the argument
                :value (-> stack peek (dissoc :preceding-statement))
                :preceding-statement (-> stack peek :preceding-statement)}]
      (assoc context
             :stack (pop-n stack 2)
             :statement expr))
    ; default, invoke instance method interop call
    (let [arg-types (.getArgumentTypes insn pool)
          argc (count arg-types)
          args (cons (peek-at stack argc) (peek-n stack argc))
          expr {:type :invoke-member
                :args (eliminate-arg-casts args (cons Type/OBJECT arg-types))
                :member (.getMethodName insn pool)}]
      (generic-invoke-expr insn expr (inc argc) context))))

(defmethod process-insn PopInstruction
  [_ insn {:keys [stack statement] :as context}]
  "Pops top stack item and adds it as a statement onto context"
  (assert (not statement)) ; all statements should have been picked up by invokes
  (assoc context
         :stack (pop stack)
         ; throw away constants (usually nils), they're not statements
         :statement (if (-> stack peek :type (= :const)) nil (peek stack))))

(defmethod process-insn ARETURN
  [_ insn {:keys [stack] :as context}]
  "Marks top stack item as return and ends processing"
  (assoc context
         :code nil
         :stack (pop stack)
         :return (peek stack)))

(defmethod process-insn RETURN
  [_ insn {:keys [stack statement] :as context}]
  "Marks last statement as return and ends processing"
  (assoc context
         :code nil
         :statement nil
         :return statement))

(defn process-namespace
  [exprs]
  "Transforms list of expression trees to a form with 'ns macro"
  (if-not (-> exprs first :fn-expr :name (= 'in-ns))
    exprs
    (let [ns-sym (-> exprs first :args first :value)
          ns-expr {:type :invoke
                   :fn-expr {:type :var
                             :ns 'clojure.core
                             :name 'ns}
                   :args [{:type :var
                           :name ns-sym}]}]
      ; in-ns + loading-fn + if
      (cons ns-expr (drop 3 exprs)))))

(defn get-indexed-insns [method]
  "Creates a sequence of instructions indexed by their absolute bytecode index"
  (let [insns (get-insns method)]
    (map vector (reductions + (cons 0 (map #(.getLength %) insns))) insns)))

(defn method->expr [clazz method & {:as context}]
  "Decompiles a single method and returns the whole decompilation context.
  Optionally accepts parts of context which will be used for initialization."
  (let [arg-count (inc (count (.getArgumentTypes method)))
        ; (almost) empty context
        context (merge {:code (get-indexed-insns method)
                        :stack []
                        :clazz clazz
                        :method method
                        :fields {}
                        :pool (ConstantPoolGen. (.getConstantPool clazz))
                        :arg-count arg-count
                        ; function arguments as local variables
                        :vars (mapv (fn [n] {:type :arg :index n}) (range arg-count))}
                       context)]
    (process-insns context)))

(defn statement-chain [expr]
  "Converts linked list connected with :preceding-statement into regular list"
  (loop [expr expr
         chain nil]
    (if-let [preceding (:preceding-statement expr)]
      (recur preceding (cons expr chain))
      (cons expr chain))))

(defn render-expr [expr fn-map fn-args]
  "Converts expression tree into Clojure code"
  (letfn
    [; helper to get name of local variable
     (local-name [expr]
       (demunge (or (:name expr)
                    (str "local" (- (:index expr) (count fn-args) -1)))))
     ; convert single expression
     (render-single [expr]
       (let [args (map render-chain-do (:args expr ()))]
         (condp = (:type expr)
           :const (let [v (:value expr)]
                    (if (symbol? v) (list 'quote v) v))
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
           :set-field (list 'set! (list (symbol (str \. (:field expr)))
                                        (render-chain-do (:target expr)))
                            (render-chain-do (:value expr)))
           :let (render-binding 'let expr)
           :loop (render-binding 'loop expr)
           :local (if-let [assign (:assign expr)] (render-chain-do assign) (local-name expr))
           :var (demunge (:name expr))
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
           ; we couldn't decompile, so output placeholder comment
           :error (list 'comment "Couldn't decompile function"
                        (str "Exception:" (:cause expr))
                        (str "Instruction where the exception occured:" (-> expr :insn class)))
           (if *debug* expr (throw (IllegalArgumentException. (str "Cannot render: " expr)))))))

     ; let/loop helper
     (render-binding [sym expr]
       (let [local-names (map local-name (:locals expr))]
         (list* sym (vec (interleave
                           local-names
                           (map #(render-chain-do
                                   (assoc (:initial %1) :local-name %2))
                                (:locals expr) local-names)))
                (render-chain (:body expr)))))

     ; helper to get argument name symbols
     (fn-arg-syms [args]
       (mapv #(symbol (.getName %)) args))

     ; helper to conver single arity of a function
     (render-arity [arity fn-name]
       (let [args (fn-arg-syms (:args arity))
             argspec (if-let [req (:required-arity arity)]
                       (let [[left right] (split-at req args)]
                         (vec (concat left ['&] right)))
                       args)]
         (cons argspec (render-expr (:body arity) fn-map (vec (cons fn-name args))))))

     ; convert function definition
     (render-fn [sym func fn-name]
       (let [definition (map #(render-arity % fn-name) (:arities func))
             definition (if (= (count definition) 1) (first definition) definition)]
         (cons sym (if fn-name (cons fn-name definition) definition))))

     ; render a chain of statements inline (without do)
     (render-chain [expr]
       (map render-single (statement-chain expr)))

     ; render a chain of statements wrapped in do if there are more than 1
     (render-chain-do [expr]
       (let [chain (statement-chain expr)]
         (if (> (count chain) 1)
           (list* 'do (map render-single chain))
           (render-single (peek chain)))))]
    (render-chain expr)))

(defn decompile-invoke [clazz invoke fields]
  "Decompiles single invoke method into function expression tree"
  (let [{:keys [return error]} (method->expr clazz invoke :fields fields)
        argc (count (.getArgumentTypes invoke))
        ; variadic functions have methdos returning their minimal arity
        ; we need to know it to place the '& argument separator
        required-arity (if (= (.getName invoke) "doInvoke")
                         (-> (method->expr clazz (find-method clazz "getRequiredArity"))
                             :return :value))
        ; local variable (and arguments) table (names and indices where they start
        var-table (-> invoke .getLocalVariableTable .getLocalVariableTable)]
    (when *debug* (pprint/pprint return))
    {:type :fn-single
     ; minimal arity for variadic, nil for others
     :required-arity required-arity
     ; locals with index less than argc are function arguments, 0th one is
     ; implicit this that we don't want emitted
     :args (filter #(<= 1 (.getIndex %) argc) var-table)
     :body (or error return)}))

(defn decompile-fn [clazz]
  "Decompiles whole function class into function expression tree"
  (let [; get function name from class name
        name-parts (string/split (.getClassName clazz) #"\$")
        fn-ns (demunge (name-parts 0))
        ; remove gensym digits from the name
        fn-name (demunge (string/replace (last name-parts) #"__\d+$" ""))
        ; class initializer, we need the fields
        clinit (find-method clazz "<clinit>")
        {:keys [fields error]}  (method->expr clazz clinit)
        ; regular arities
        invokes (find-methods clazz "invoke")
        ; optional variadic arity
        do-invoke (find-method clazz "doInvoke")
        ; decompile invokes
        arities (vec (sort-by #(count (:args %))
                              (map #(decompile-invoke clazz % fields) invokes)))]
    {:type :fn
     :class-name (.getClassName clazz)
     :ns fn-ns
     ; functions with name 'fn are anonymous, set the name to nil for them
     :name (if-not (= fn-name 'fn) fn-name)
     :error error
     ; add variadic among arities, if there is one
     :arities (if do-invoke
                (conj arities (decompile-invoke clazz do-invoke fields))
                arities)}))

(defn decompile-init [clazz]
  "Decompile initialization class into expression tree"
  (let [; constant initializer methods
        inits (filter #(.startsWith (.getName %) "__init") (.getMethods clazz))
        ; decompile to get all initialized fields
        fields (reduce #(:fields (method->expr clazz %2 :fields %1)) (cons nil inits))
        statement-types #{:invoke :invoke-static :invoke-ctor :invoke-member
                          :def :if :let :loop}
        ; decompile top-level statements
        load-method (method->expr clazz (find-method clazz "load") :fields fields)
        ; get statements from decompilation context
        ; the compiler emits expression in statement context, so they end up on
        ; the stack. We need to get them from there
        ; FIXME this looks kinda arbitrary
        body (if (identical? (-> load-method :stack peek) (-> load-method :return))
               (:stack load-method)
               (concat (:stack load-method) [(:return load-method)]))
        ; filter out irrelevant stack items
        body (conj-if (filter #(statement-types (:type %)) body) (:error load-method))
        body (process-namespace body)]
    {:type :init
     :source-file (string/replace (.getClassName clazz) "__init" ".clj")
     :body body}))

(defn decompile-class [clazz]
  "Decompiles single class file"
  (let [class-name (.getClassName clazz)
        superclass (.getSuperclassName clazz)]
    (cond
      (= superclass "clojure.lang.AFunction")
      ; regular Clojure function
      (decompile-fn clazz)

      (= superclass "clojure.lang.RestFn")
      ; variadic Clojure function
      (decompile-fn clazz)

      (find-method clazz "load")
      ; module initialization class
      (decompile-init clazz)

      :default
      ; unsupported class type
      (log/warn "Unrecognized class " class-name ". Skipping"))))

(defn get-classes [files]
  "Returns file paths as BCEL's JavaClasses"
  (map #(.parse (ClassParser. %)) files))

(defn get-classes-from-paths [paths]
  "Finds classes in supplied paths and parses them using BCEL"
  (->> paths
       (mapcat #(file-seq (io/file %)))
       (map str)
       (filter #(.endsWith % ".class"))
       (get-classes)))

(defn decompile-classes [paths]
  "Decompiles all class files at given paths. Recurses into directories"
  (keep decompile-class (get-classes-from-paths paths)))

(defn render-classes [classes]
  "Convert expression trees of classes into Clojure source code. Requires at
  least one initialization class to be present"
  (let [fn-map (into {} (keep #(if (= (:type %) :fn) [(:class-name %) %]) classes))
        inits (filter #(= (:type %) :init) classes)]
    (if (seq inits)
      (apply hash-map
             (mapcat
               (fn [init]
                 [(:source-file init)
                  (mapcat #(render-expr % fn-map []) (:body init))])
               inits))
      (log/error "No __init class found in the paths given, please adjust the "
                 "path to include all class files for the project. "
                 "Decompiling projects generated by different compilers than "
                 "Clojure compiler, such as javac, are not supported. "
                 "For decompling Java projects use a Java decompiler."))))

(defn do-decompile [paths]
  "Decompile class files found in paths into Clojure source code"
  (render-classes (decompile-classes paths)))

(defn pprint-code [code writer]
  "Pretty prints Clojure structures as code into stream"
  ; workaround for bug CLJ-1361
  (with-redefs [pprint/pprint-ns-reference empty]
    (pprint/write code :pretty true :stream writer :dispatch pprint/code-dispatch))
  (.write writer "\n\n"))

(defn output-source-file [code-wrapper out-dir]
  "Takes decompiled form of prepared code and writes it to appropriate file in
  out dir"
  (let [file (io/file out-dir (first code-wrapper))]
    (with-open [writer (io/writer file)]
      (smap #(pprint-code % writer) (second code-wrapper)))
    (log/info "Created file " (str file))))

(defn -main [& args]
  "Entry point. Decompiles class files given as commandline arguments"
  (let [cli-opts [["-o" "--output DIR" "Output directory"
                   :default "decompiled"]
                  ["-h" "--help" "Print usage"]]
        {paths :arguments
         {out-dir :output help :help} :options
         summary :summary
         errors :errors} (cli/parse-opts args cli-opts)]
    (when errors (smap #(log/error %) errors) (System/exit 1))
    (when (or help (empty? paths))
      (println (str "Usage: java -jar decompiler.jar [-o DIR] [PATHS]\n"
                    "Decompiles Clojure code from class files found in PATHS.\n"
                    "Recurses into directories.\n"
                    "Options:\n"
                    summary))
      (System/exit 0))
    (-> (io/file out-dir) .mkdirs)
    (smap #(output-source-file % out-dir)
                (do-decompile paths))))
