(ns decompiler.core
  (:gen-class)
  (:import (org.apache.bcel.classfile ClassParser)))

(defn decompile-class [clazz]
  "Decompiles single class file"
  clazz) ; placeholder

(defn get-classes [files]
  "Returns file paths as BCEL's JavaClasses"
  (map #(.parse (ClassParser. %)) files))

(defn -main [& paths]
  "Entry point. Decompiles class files given as commandline arguments"
  (let [classes (get-classes paths)]
    (dorun (map (comp prn decompile-class) classes))))
