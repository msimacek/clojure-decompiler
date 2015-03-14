(ns decompiler.core
  (:gen-class :main true)
  (:require [clojure.string :as string]
            [clojure.java.io :as io])
  (:import (org.apache.bcel.classfile ClassParser)
           (org.apache.bcel.generic
             ConstantPoolGen InstructionList
             LoadInstruction
             DUP LDC INVOKESTATIC PUTSTATIC GETSTATIC INVOKEVIRTUAL INVOKEINTERFACE)))

(defn pop-n [stack n] (let [c (count stack)] (subvec stack 0 (- c n))))
(defn peek-n [stack n] (let [c (count stack)] (subvec stack (- c n) c)))
(defn peek-at [stack n] (let [c (count stack)] (nth stack (- c n 1))))

(defn find-method [clazz method]
  (first (filter #(= (.getName %) method) (.getMethods clazz))))

(defn get-instructions [method]
  (-> method .getCode .getCode InstructionList. .getInstructions))

(defn demunge [what]
  (symbol (Compiler/demunge what)))

(defn insn-method [insn pool]
  (str (.getClassName insn pool) \/ (.getMethodName insn pool)))

(defn code->expr [clazz method fields]
  (let [code (get-instructions method)
        class-name (.getClassName clazz)
        pool (ConstantPoolGen. (.getConstantPool clazz))]
    (loop [[insn & code] code
           stack []
           vars []
           fields fields
           result []]
      (if insn
        (condp instance? insn
          GETSTATIC (if (= (.getClassName insn pool) class-name)
                      (recur code ; TODO getstatic on other objects
                             (conj stack (fields (.getFieldName insn pool)))
                             vars fields result))
          PUTSTATIC (if (= (.getClassName insn pool) class-name)
                      (recur code ; TODO putstatic on other objects
                             (pop stack)
                             vars
                             (assoc fields (.getFieldName insn pool) (peek stack))
                             result))
          LoadInstruction (recur code
                                 (conj stack (nth vars (.getIndex insn)))
                                 vars fields result)
          DUP (recur code (conj stack (peek stack)) vars fields result)
          LDC (recur code
                     (conj stack {:type :const :value (.getValue insn pool)})
                     vars fields result)
          INVOKESTATIC (cond
                         (= (.getMethodName insn pool) "var") ; TODO verify type
                         (recur code
                                (conj (pop-n stack 2)
                                      {:type :var
                                       :ns (demunge (:value (peek-at stack 1)))
                                       :name (demunge (:value (peek stack)))})
                                vars fields result)
                         :default (recur code stack vars fields result))
          INVOKEVIRTUAL (if (= (.getMethodName insn pool) "getRawRoot") ; TODO and is var
                          (recur code stack vars fields result) ; we have the var already
                          (recur code stack vars fields result)) ; TODO handle this
          INVOKEINTERFACE (if (= (.getMethodName insn pool) "invoke") ;TODO check type
                            (let [argc (count (.getArgumentTypes insn pool))
                                  argc1 (inc argc)
                                  expr {:type :invoke
                                        :args (peek-n stack argc)
                                        :name (:name (peek-at stack argc))}]
                              (recur code
                                     (conj (pop-n stack argc1) expr)
                                     vars fields
                                     (conj result expr)))
                            (recur code (pop stack) vars fields result)) ; TODO handle interop
          (recur code stack vars fields result))
        [result fields]))))

(defn expr->clojure [exprs]
  (let [expr (if (vector? exprs) (last exprs) exprs)] ; TODO more exprs form `do`
    (condp = (:type expr)
      :const (:value expr)
      :invoke (list* (:name expr) (map expr->clojure (:args expr)))
      ())))

(defn decompile-fn [clazz]
  (let [[fn-ns fn-name] (map demunge (string/split (.getClassName clazz) #"\$" 2))
        clinit (find-method clazz "<clinit>")
        [_ fields] (code->expr clazz clinit {})
        invoke (find-method clazz "invoke") ;TODO multiple arities
        [exprs _] (code->expr clazz invoke fields)]
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
       (keep decompile-class)))

(defn -main [& paths]
  "Entry point. Decompiles class files given as commandline arguments"
  (println (apply str (decompile-classes paths))))
