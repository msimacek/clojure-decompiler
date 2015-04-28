(ns decompiler.data
  "Module containing data tables used throughout the decompilation process"
  (:import
    (org.apache.bcel.generic
      LNEG DNEG DADD IADD LADD DADD ISUB DSUB DSUB LSUB IMUL DMUL LMUL DMUL
      IDIV DDIV LDIV IREM LREM LAND IAND LOR LXOR ISHL LSHL ISHR LSHR LUSHR
      IUSHR LCMP DCMPG DCMPL IFNE IFGE IFLE IFGT IFLT)))

(def predicate-insns
  "Binary predicate instructions that appear in if's that deal with primitive
  values.  They map to Clojure counterparts."
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
  "Unary redicate instructions that appear in if's that deal with primitive
  values.  They map to Clojure counterparts."
  {[DCMPL IFNE] 'zero?
   [LCMP IFNE] 'zero?
   [LCMP IFLE] 'pos?
   [DCMPL IFLE] 'pos?
   [LCMP IFGE] 'neg?
   [DCMPG IFGE] 'neg?})

(def primitive-artihmetic-unary
  "Unary primitive arithmetic instructions mapping to their Clojure
  counterparts."
  {LNEG '-
   DNEG '-})

(def primitive-artihmetic-binary
  "Binary primitive arithmetic instructions mapping to their Clojure
  counterparts."
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
   IAND 'bit-and ; emitted in case condition
   LOR 'bit-or
   LXOR 'bit-xor
   ISHL 'bit-shift-left
   LSHL 'bit-shift-left
   ISHR 'bit-shift-right
   LSHR 'bit-shift-right
   LUSHR 'unsigned-bit-shift-right
   IUSHR 'unsigned-bit-shift-right})

(def casts
  "Cast functions that return primitive values"
  '#{char short int long float double boolean})

(def inline-fns
  "Clojure compiler inlines several Clojure functions as static method calls.
  This maps the methods back to functions"
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
