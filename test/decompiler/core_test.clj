(ns decompiler.core-test
  (:import (java.nio.file Files)
           (java.nio.file.attribute FileAttribute)
           (java.io StringReader StringWriter))
  (:require [clojure.test :refer :all]
            [decompiler.core :refer :all]))

; (alter-var-root #'*debug* (constantly true))

(defn compile-and-decompile [test-name code]
  (let [dir (Files/createTempDirectory (str "decompiler-test-" test-name)
                                       (into-array FileAttribute []))]
    (-> dir .toFile .deleteOnExit)
    (binding [*out* (StringWriter.)
              *compile-files* true
              *compile-path* (str dir)]
      (with-open [rdr (StringReader. (apply str code))]
        (Compiler/compile rdr "test_code.clj" "TEST_SOURCE")))
    (if *debug* (println))
    (vec (do-decompile [(str dir)]))))

(defmacro deftest-decompile
  ([test-name code]
   `(deftest-decompile ~test-name ~code ~code))
  ([test-name code expected-code]
   (let [to-code #(if (vector? %) % [%])
         code (to-code code)
         expected-code (to-code expected-code)]
     `(deftest ~test-name
        (is (= '~expected-code
                          (compile-and-decompile ~(name test-name) '~code)))))))

(deftest-decompile return-0
  (defn test-fn [] 0))
(deftest-decompile return-string
  (defn test-fn [] "Hello"))
(deftest-decompile return-long
  (defn test-fn [] 123456789))
(deftest-decompile return-big-decimal
  (defn test-fn [] 12345678901234567890.1M))
(deftest-decompile return-big-int
  (defn test-fn [] 12345678901234567890N))
(deftest-decompile return-double
  (defn test-fn [] 1.1))
(deftest-decompile return-nil
  (defn test-fn [] nil))
(deftest-decompile return-true
  (defn test-fn [] true))
(deftest-decompile return-false
  (defn test-fn [] false))
(deftest-decompile return-char
  (defn test-fn [] \a))
(deftest-decompile return-keyword
  (defn test-fn [] :lol))
(deftest-decompile return-keyword-ns
  ; TODO this will print it as :decompiler.core-test/lol
  (defn test-fn [] ::lol))
(deftest-decompile return-symbol
  (defn test-fn [] 'lol))
(deftest-decompile return-empty-list
  (defn test-fn [] ()))
(deftest-decompile return-empty-vector
  (defn test-fn [] []))
(deftest-decompile return-empty-map
  (defn test-fn [] {}))
(deftest-decompile return-empty-set
  (defn test-fn [] #{}))
(deftest-decompile return-vector
  (defn test-fn [] [1 2 (str 3)]))
; list literals have metadata!
; (deftest-decompile return-list
;   (defn test-fn [] '(1 2 3)))
(deftest-decompile return-set
  (defn test-fn [] #{1 2 (str 3)}))
(deftest-decompile return-map
  (defn test-fn [] {:live 4 :ever (str \!)}))
(deftest-decompile return-global
  (defn test-fn [] cons))
(deftest-decompile return-global-dynamic
  (defn test-fn [] *command-line-args*))

(deftest-decompile simple-clj-call
  (defn test-fn [] (println "Hello")))
(deftest-decompile clj-call-param
  (defn test-fn [arg1] (str arg1)))
(deftest-decompile clj-call-param2
  (defn test-fn [arg1 arg2] (str arg1 arg2)))
(deftest-decompile clj-call-nested
  (defn test-fn [arg1 arg2] (str (str arg1 2) 1)))
(deftest-decompile call-static
  (defn test-fn [arg1 arg2] (java.lang.Double/compare 1.0 1.00001)))
(deftest-decompile call-static-void
  (defn test-fn [arg1 arg2] (java.lang.System/exit 1)))
(deftest-decompile call-static-reflection
  (defn test-fn [arg1 arg2] (java.lang.Math/abs arg1)))
(deftest-decompile get-static
  (defn test-fn [] java.lang.Double/NaN))
(deftest-decompile call-ctor
  ; TODO get rid of java.lang
  (defn test-fn [] (java.lang.StringBuilder. "I can haz instance?")))
(deftest-decompile call-ctor-overloaded
  (defn test-fn [arg1] (java.lang.Throwable. arg1)))
(deftest-decompile call-virtual-reflective-no-arg
  (defn test-fn [arg1] (.getSimpleRemoteStatelessSessionProxyFactoryBean arg1)))
(deftest-decompile call-virtual-reflective-args
  (defn test-fn [arg1 arg2] (.getSimpleRemoteStatelessSessionProxyFactoryBean arg1 arg2)))
(deftest-decompile get-member-field
  (defn test-fn [] (.x (java.awt.Point. 1 2))))
(deftest-decompile set-member-field
  (defn test-fn [] (set! (.x (java.awt.Point. 1 2)) 3)))
(deftest-decompile call-virtual
  (defn test-fn [] (.toString (java.awt.Point. 1 2))))
(deftest-decompile call-virtual-void
  (defn test-fn [] (.println java.lang.System/out "bbb")))
(deftest-decompile instanceof
  (defn test-fn [] (instance? java.io.InputStream *in*)))

; test that inlined functions are converted to their clojure form
(defmacro deftest-inline [sym arity]
  (let [argsyms (map #(symbol (str "arg" %)) (range 1 (inc arity)))]
    `(deftest-decompile ~(-> (str "inline-" sym \- arity) munge symbol)
       ~(list 'defn 'test-fn (vec argsyms) (cons sym argsyms)))))
(defmacro gen-inline-tests [arity syms]
  `(do
     ~@(loop [[sym & syms] syms
              code nil]
         (if sym
           (recur syms (conj code `(deftest-inline ~sym ~arity)))
           code))))

; todo: unchecked casts, uncehcked ops, arrays, array ops, prim casts, array casts
(gen-inline-tests 1 [- nil? zero? count inc inc' dec dec' pos? neg? bit-not
                     reduced?])
(gen-inline-tests 2 [+ +' - -' * *' / > < >= <= = == identical? compare nth max
                     min rem quot bit-and bit-or bit-xor bit-and-not bit-clear
                     bit-set bit-flip bit-test bit-shift-left bit-shift-right
                     unsigned-bit-shift-right get])
(gen-inline-tests 3 [get])

(deftest-decompile primitive-arith-double
  (defn test-fn [x y]
    (let [local1 (double x)
          local2 (double y)]
      (java.lang.Math/sqrt (+ (* local1 local2) (- local1))))))
(deftest-decompile primitive-arith-long
  (defn test-fn [x y]
    (let [local1 (long x)
          local2 (long y)]
      (java.lang.Math/abs (quot (rem local1 local2) (inc local1))))))

(deftest-decompile return-cast-char
  (defn test-fn [x] (char (+ 97 x))))
(deftest-decompile return-cast-int
  (defn test-fn [x] (int (/ 2 x))))
(deftest-decompile return-cast-keyword
  (defn test-fn [x] (keyword (str x))))
(deftest-decompile return-cast-symbol
  (defn test-fn [x] (symbol (str x))))

(deftest-decompile unconditional-recur-arg
  (defn test-fn [arg1] (recur arg1)))
(deftest-decompile unconditional-recur-expr
  (defn test-fn [arg1] (recur (str arg1))))
(deftest-decompile unconditional-recur-const
  (defn test-fn [arg1] (recur false)))
(deftest-decompile simple-if
  (defn test-fn [arg1] (if arg1 1 2)))
(deftest-decompile if-expr
  (defn test-fn [arg1 arg2] (if arg1 (str arg1) (str arg2))))
(deftest-decompile if-expr-child
  (defn test-fn [arg1 arg2] (str (if arg1 (str arg1) (str arg2)))))
(deftest-decompile if-expr-cond
  (defn test-fn [arg1 arg2] (if (str arg1) (str arg1) 0)))
(deftest-decompile if-no-else
  (defn test-fn [arg1 arg2] (if arg1 (str arg1))))
(deftest-decompile if-else-false
  (defn test-fn [arg1 arg2] (if arg1 (str arg1) false)))
(deftest-decompile if-nested
  (defn test-fn [arg1 arg2] (if arg1 (if (str arg2) (str arg2) "1") "2")))
(deftest-decompile conditional-recur
  (defn test-fn [arg1 arg2] (if (seq arg1) (recur (first arg1) (cons arg1 arg2)) arg2)))
(deftest-decompile if-primitive
  (defn test-fn [arg1 arg2] (if (java.lang.Double/isNaN 0.1) "NaN" arg1)))
(deftest-decompile if-primitive2
  (defn test-fn [arg1 arg2] (if (> arg1 arg2) (inc arg1) arg1)))
(deftest-decompile if-primitive-predicate1
  (defn test-fn [arg1 arg2] (if (> (int arg1) (int arg2)) (inc arg1) arg1)))
(deftest-decompile if-primitive-predicate2
  (defn test-fn [arg1 arg2] (if (== (long arg1) (long arg2)) (inc arg1) arg1)))
(deftest-decompile if-primitive-predicate3
  (defn test-fn [arg1 arg2] (if (= (boolean arg1) (boolean arg2)) (inc arg1) arg1)))
(deftest-decompile if-primitive-predicate-zero
  (defn test-fn [arg1 arg2] (if (zero? (long arg2)) (inc arg1) arg1)))
(deftest-decompile if-primitive-predicate-pos
  (defn test-fn [arg1 arg2] (if (pos? (int arg2)) (inc arg1) arg1)))
(deftest-decompile if-primitive-predicate-neq
  (defn test-fn [arg1 arg2] (if (neg? (long arg2)) (inc arg1) arg1)))

(deftest-decompile simple-let
  (defn test-fn [arg1 arg2] (let [local1 (str arg1 arg1)] local1)))
(deftest-decompile let-multiple
  (defn test-fn [arg1 arg2] (let [local1 (str arg1 arg1)
                                  local2 (str local1 "猫耳")]
                              (str local2 local1 local2))))
(deftest-decompile let-nested
  (defn test-fn [arg1 arg2]
    (let [local1 (first arg1)]
      (if (seq arg2)
        (let [local2 (str arg1 arg1)
              local3 (str local1 "猫耳")]
          (recur (conj local3 local1) (next local2)))
        ; it would be better if it generated at least unique local names, but
        ; this is technically correct
        (let [local2 (first local1)]
          (str local2 local1))))))
(deftest-decompile let-names
  (defn test-fn [x]
    (let [a (first x)]
      (inc a))))

(deftest-decompile simple-loop
  (defn test-fn [arg1 arg2]
    (loop [local1 (concat arg1 arg2)]
      (recur (first local1)))))
(deftest-decompile loop-more-locals
  (defn test-fn [arg1 arg2]
    (loop [local1 (concat arg1 arg2)
           local2 (str local1)]
      (recur (first local1) local2))))
(deftest-decompile loop-condition
  (defn test-fn [arg1 arg2]
    (loop [local1 (concat arg1 arg2)
           local2 []]
      (if local1
        (recur (first local1) (cons local1 local2))
        local2))))
; loops in expressions are rewrapped into anonymous functions
; (deftest-decompile nested-loop
;   (defn test-fn [arg1 arg2]
;     (loop [local1 (concat arg1 arg2)
;            local2 (str local1)]
;       (recur (loop [local3 (first arg2)
;                     local4 []]
;                (if local3
;                  (recur nil (next local3))
;                  local4)) local1))))

(deftest-decompile case-ints-packed
  (defn test-fn [arg1]
    (case arg1
      0 nil
      1 true
      false)))
(deftest-decompile case-ints-sparse
  (defn test-fn [arg1]
    (case arg1
      0 nil
      9999 true
      false)))
(deftest-decompile case-hash-identity
  (defn test-fn [arg1]
    (case arg1
      :bb true ; the order is arbitrary
      :aa nil
      false)))
(deftest-decompile case-hash-identity-shifted
  (defn test-fn [arg1]
    (case arg1
      :bbb nil
      :aaa true ; the order is arbitrary
      false)))
(deftest-decompile case-hash-equiv
  (defn test-fn [arg1]
    (case arg1
      "aa" nil
      "bb" true
      false)))

(deftest-decompile multiple-statements
  (defn test-fn [arg1]
    (println 0)
    (println arg1)))
(deftest-decompile even-more-statements
  (defn test-fn [arg1]
    (println 0)
    (.println java.lang.System/out "bbb")
    (println arg1)))
(deftest-decompile multiple-statements-const
  (defn test-fn [arg1]
    (println 0)
    0))
(deftest-decompile do-in-expression
  (defn test-fn [arg1]
    (str (inc arg1) (do (println arg1) (dec arg1)))))
(deftest-decompile multiple-statements-let
  (defn test-fn [arg1]
    (let [local1 (inc arg1)]
      (println 0)
      (println arg1))))
(deftest-decompile multiple-statements-if
  (defn test-fn [arg1]
    (if arg1
      (do (println arg1) (println ";"))
      (do (println 0) (println 1)))))
(deftest-decompile multiple-statements-loop
  (defn test-fn [arg1]
    (loop [local1 (inc arg1)]
      (println local1)
      (if local1 (recur (dec local1))))))
(deftest-decompile multiple-statements-before-if
  (defn test-fn [arg1]
    (inc (do (println "haha")
           (if (nil? arg1) 1 2)))))

(deftest-decompile argument-names
  (defn test-fn [x y]
    (+ x y)))

(deftest-decompile return-function
  (defn test-fn [arg1]
    (fn [] arg1)))
(deftest-decompile return-function2
  (defn test-fn [foo]
    (fn [x] (+ foo x))))
(deftest-decompile local-function
  (defn test-fn [foo]
    (let [local1 (fn [x] (+ foo x))]
      (local1 3))))
(deftest-decompile call-fn
  (defn test-fn [foo]
    ((fn [bar] (inc bar) foo))))
(deftest-decompile recursion
  (defn test-fn [x]
    (if (integer? x)
      (test-fn (/ x 2))
      x)))
(deftest-decompile named-local-fn
  (defn test-fn [foo]
    (filter (fn f [x] (if (integer? x) (f (/ x 2) x))) foo)))
(deftest-decompile map-lookup
  (defn test-fn [foo]
    ({:a "a" :b "bbb"} foo)))
(deftest-decompile set-lookup
  (defn test-fn [foo]
    (#{"a" (str 1)} foo)))
(deftest-decompile keyword-lookup1
  (defn test-fn []
    (:a {:a 1})))
(deftest-decompile keyword-lookup2
  (defn test-fn [foo]
    (:a foo)))
(deftest-decompile keyword-lookup3
  (defn test-fn [foo]
    (:b (:a foo))))
(deftest-decompile keyword-lookup-default
  (defn test-fn [foo]
    (:b foo false)))

(deftest-decompile multiple-arities
  (defn test-fn
    ([foo] (inc foo))
    ([foo bar] (+ foo bar))))
(deftest-decompile variadic
  (defn test-fn [a & args]
    (map (fn [x] (* a x)) args)))
(deftest-decompile variadic-multiple
  (defn test-fn
    ([a] (* a 2))
    ([a & args] (map (fn [x] (* a x)) args))))

(deftest-decompile toplevel
  (println "Hello"))
(deftest-decompile toplevel-multiple
  [(println "Hello")
   (println (str "World") (do (println \!) (str "")))
   (println "猫耳着け")])
(deftest-decompile toplevel-def
  (def some-string "私はかわいい猫です"))
(deftest-decompile toplevel-def-expr
  (def important-number (inc 41)))
(deftest-decompile toplevel-more
  [(def some-string "私はかわいい猫です")
   (def important-number (inc 41))])
(deftest-decompile toplevel-if
  [(println "haha")
   (if *command-line-args* (println 1) (println 2))])

(deftest-decompile ns-statement
  [(ns cool-namespace)
   (def one 1)])
