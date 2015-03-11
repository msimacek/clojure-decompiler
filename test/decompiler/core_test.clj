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
      (with-open [rdr (StringReader. code)]
        (Compiler/compile rdr "test_code.clj" "TEST_SOURCE")))
    (decompile-classes [(str dir)])))


(deftest test-empty-fn
  (let [code "(defn test-fn [] ())"]
    (is (= code (compile-and-decompile code)))))
