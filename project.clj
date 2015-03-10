(defproject decompiler "0.1.0-SNAPSHOT"
  :description "Clojure decompiler"
  :url "http://example.com/FIXME"
  :license {:name "Eclipse Public License"
            :url "http://www.eclipse.org/legal/epl-v10.html"}
  :main decompiler.core
  :aot [decompiler.core]
  :dependencies [[org.clojure/clojure "1.6.0"]
                 [org.apache.bcel/bcel "5.2"]])
