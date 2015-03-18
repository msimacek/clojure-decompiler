(ns decompiler.core-test
  (:import (java.nio.file Files)
           (java.nio.file.attribute FileAttribute)
           (java.io StringReader))
  (:require [clojure.test :refer :all]
            [decompiler.core :refer :all]))

(alter-var-root #'*debug* (constantly true))

(defn compile-and-decompile [test-name code]
  (let [dir (Files/createTempDirectory (str "decompiler-test-" test-name)
                                       (into-array FileAttribute []))]
    (-> dir .toFile .deleteOnExit)
    (binding [*compile-files* true
              *compile-path* (str dir)]
      (with-open [rdr (StringReader. (apply str code))]
        (Compiler/compile rdr "test_code.clj" "TEST_SOURCE")))
    (println)
    (decompile-classes [(str dir)])))

(defmacro deftest-decompile
  ([test-name code]
   (deftest-decompile &form &env test-name code code))
  ([test-name code expected-code]
   (let [to-code #(if (vector? %) % [%])
         code (to-code code)
         expected-code (to-code expected-code)]
     `(deftest ~test-name (is (= '~expected-code (compile-and-decompile ~(name test-name) '~code)))))))

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
(deftest-decompile simple-clj-call
  (defn test-fn [] (println "Hello")))
(deftest-decompile clj-call-param
  (defn test-fn [arg1] (str arg1)))
(deftest-decompile clj-call-param2
  (defn test-fn [arg1 arg2] (str arg1 arg2)))
(deftest-decompile clj-call-nested
  (defn test-fn [arg1 arg2] (str (str arg1 2) 1)))
(deftest-decompile clj-call-static
  (defn test-fn [arg1 arg2] (java.lang.Double/compare 1.0 1.00001)))
(deftest-decompile clj-call-static
  (defn test-fn [] java.lang.Double/NaN))
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
; (deftest-decompile if-primitive
;   (defn test-fn [arg1 arg2] (if (java.lang.Double/isNaN arg1) "NaN" arg1)))
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
(deftest-decompile simple-loop
  (defn test-fn [arg1 arg2]
    (loop [local1 (concat arg1 arg2)]
      (recur (first local1)))))
