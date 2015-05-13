(defproject decompiler "0.1.0-SNAPSHOT"
  :description "Clojure decompiler"
  :url "https://github.com/msimacek/clojure-decompiler"
  :license {:name "Eclipse Public License"
            :url "http://www.eclipse.org/legal/epl-v10.html"}
  :main decompiler.core
  :aot [decompiler.core decompiler.data]
  :dependencies [[org.clojure/clojure "1.6.0"]
                 [org.clojure/tools.cli "0.3.1"]
                 [org.clojure/tools.logging "0.3.1"]
                 [clj-logging-config "1.9.12"]
                 [org.apache.bcel/bcel "5.2"]])
