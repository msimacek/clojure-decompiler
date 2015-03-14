(ns decompiler.core-test
  (:import (java.nio.file Files)
           (java.nio.file.attribute FileAttribute)
           (java.io StringReader))
  (:require [clojure.test :refer :all]
            [decompiler.core :refer :all]))

(defn compile-and-decompile [test-name code]
  (let [dir (Files/createTempDirectory (str "decompiler-test-" test-name)
                                       (into-array FileAttribute []))]
    (-> dir .toFile .deleteOnExit)
    (binding [*compile-files* true
              *compile-path* (str dir)]
      (with-open [rdr (StringReader. (apply str code))]
        (Compiler/compile rdr "test_code.clj" "TEST_SOURCE")))
    (decompile-classes [(str dir)])))

(defmacro deftest-decompile
  ([test-name code]
   (deftest-decompile &form &env test-name code code))
  ([test-name code expected-code]
   (let [to-code #(if (vector? %) % [%])
         code (to-code code)
         expected-code (to-code expected-code)]
   `(deftest ~test-name (is (= '~expected-code (compile-and-decompile ~(name test-name) '~code)))))))


(deftest-decompile empty-fn (defn test-fn [] ()))
(deftest-decompile return-0 (defn test-fn [] 0))
(deftest-decompile return-string (defn test-fn [] "Hello"))
(deftest-decompile return-long (defn test-fn [] 123456789))
(deftest-decompile return-big-decimal (defn test-fn [] 12345678901234567890.1M))
(deftest-decompile return-big-int (defn test-fn [] 12345678901234567890N))
(deftest-decompile return-double (defn test-fn [] 1.1))
(deftest-decompile return-nil (defn test-fn [] nil))
(deftest-decompile return-true (defn test-fn [] true))
(deftest-decompile return-false (defn test-fn [] false))
(deftest-decompile simple-clj-call (defn test-fn [] (println "Hello")))
(deftest-decompile clj-call-param (defn test-fn [arg1] (str arg1)))
(deftest-decompile clj-call-param2 (defn test-fn [arg1 arg2] (str arg1 arg2)))
(deftest-decompile clj-call-nested (defn test-fn [arg1 arg2] (str (str arg1 2) 1)))
(deftest-decompile clj-call-static (defn test-fn [arg1 arg2] (java.lang.Double/compare 1.0 1.00001)))
