(ns decompiler.core
  (:gen-class :main true)
  (:require [clojure.string :as string]
            [clojure.java.io :as io])
  (:import (org.apache.bcel.classfile ClassParser)
           (org.apache.bcel.generic
             ConstantPoolGen InstructionList
             LDC INVOKESTATIC PUTSTATIC GETSTATIC INVOKEVIRTUAL INVOKEINTERFACE)))

(defn pop-n [stack n] (let [c (count stack)] (subvec stack 0 (- c n))))
(defn peek-n [stack n] (let [c (count stack)] (subvec stack (- c n) c)))
(defn peek-at [stack n] (let [c (count stack)] (nth stack (- c n))))

(defn find-method [clazz method]
  (first (filter #(= (.getName %) method) (.getMethods clazz))))

(defn get-instructions [method]
  (-> method .getCode .getCode InstructionList. .getInstructions))

(defn demunge [what]
  (symbol (Compiler/demunge what)))

(defn populate-fields [clazz]
  (let [clinit (find-method clazz "<clinit>")
        pool (ConstantPoolGen. (.getConstantPool clazz))
        code (get-instructions clinit)]
    (loop [[insn & code] code
           stack []
           result {}]
      (if insn
        (condp instance? insn
          LDC (recur code (conj stack (.getValue insn pool)) result)
          INVOKESTATIC (recur code ; verify it's calling intern
                              (conj (pop (pop stack))
                                    {:type :var
                                     :ns (demunge (nth stack 0))
                                     :name (demunge (nth stack 1))})
                              result)
          PUTSTATIC (recur code
                           (pop stack)
                           (assoc result (.getFieldName insn pool) (peek stack)))
          (recur code stack result))
        result))))

(defn code->expr [clazz method fields]
  (let [code (get-instructions method)
        pool (ConstantPoolGen. (.getConstantPool clazz))]
    (loop [[insn & code] code
           stack []
           result ()]
      (if insn
        (condp instance? insn
          GETSTATIC (recur code (conj stack (fields (.getFieldName insn pool))) result)
          LDC (recur code (conj stack (.getValue insn pool)) result)
          INVOKEINTERFACE (if (= (.getMethodName insn pool) "invoke")
                          (let [argc (count (.getArgumentTypes insn pool))
                                argc1 (inc argc)
                                expr {:type :invoke
                                      :args (peek-n stack argc)
                                      :name (:name (peek-at stack argc1))}]
                            (recur code
                                   (conj (pop-n stack argc1) expr)
                                   (conj result expr)))
                          (recur code (pop stack) result)) ; TODO handle interop
          (recur code stack result))
        result))))

(defn expr->clojure [exprs]
  (let [expr (if (vector? exprs) (last exprs) exprs)] ; TODO more exprs form `do`
    (condp = (:type expr)
      :const (:value expr)
      :invoke (list* (:name expr) (map expr->clojure (:args expr))))))

(defn decompile-fn [clazz]
  (let [[fn-ns fn-name] (map demunge (string/split (.getClassName clazz) #"\$" 2))
        fields (populate-fields clazz)
        invoke (find-method clazz "invoke") ;TODO multiple arities
        exprs (code->expr clazz invoke fields)]
    (list 'defn (symbol fn-name) [] (expr->clojure exprs))))

(defn decompile-class [clazz]
  "Decompiles single class file"
  (cond
    (= (.getSuperclassName clazz) "clojure.lang.AFunction")
    (decompile-fn clazz)))

(defn get-classes [files]
  "Returns file paths as BCEL's JavaClasses"
  (map #(.parse (ClassParser. %)) files))

(defn decompile-classes [paths]
  "Decopmiles all class files at given paths. Recurses into directories"
  (->> paths
      (mapcat #(file-seq (io/file %)))
      (map str)
      (filter #(.endsWith % ".class"))
      (get-classes)
      (map decompile-class)
      (apply str)))

(defn -main [& paths]
  "Entry point. Decompiles class files given as commandline arguments"
  (println (decompile-classes paths)))
