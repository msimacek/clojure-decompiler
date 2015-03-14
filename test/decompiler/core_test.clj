(ns decompiler.core-test
  (:import (java.nio.file Files)
           (java.nio.file.attribute FileAttribute)
           (java.io StringReader))
  (:require [clojure.test :refer :all]
            [decompiler.core :refer :all]))

(defn compile-and-decompile [code]
  ; TODO get rid of that array
  (let [dir (Files/createTempDirectory "decompiler-test" (into-array FileAttribute []))]
    (-> dir .toFile .deleteOnExit)
    (binding [*compile-files* true
              *compile-path* (str dir)]
      (with-open [rdr (StringReader. (apply str code))]
        (Compiler/compile rdr "test_code.clj" "TEST_SOURCE")))
    (decompile-classes [(str dir)])))

(defmacro deftest-decompile
  ([name code]
   (deftest-decompile &form &env name code code))
  ([name code expected-code]
   (let [to-code #(if (vector? %) % [%])
         code (to-code code)
         expected-code (to-code expected-code)]
   `(deftest ~name (is (= '~expected-code (compile-and-decompile '~code)))))))


(deftest-decompile test-empty-fn (defn test-fn [] ()) (defn test-fn [] ()))
(deftest-decompile test-return-0 (defn test-fn [] 0))
(deftest-decompile test-simple-clj-call (defn test-fn [] (println "Hello")))
