(ns decompiler.core
  (:gen-class :main true)
  (:require [clojure.string :as string])
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

(defn decompile-code [clazz method fields]
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
                                argc1 (inc argc)]
                            (recur code
                                   (pop-n stack argc1)
                                   (conj result
                                         (list* (:name (peek-at stack (inc argc)))
                                                (peek-n stack argc)))))
                          (recur code (pop stack) result))
          (recur code stack result))
        result))))

(defn decompile-fn [clazz]
  (let [[fn-ns fn-name] (map demunge (string/split (.getClassName clazz) #"\$" 2))
        fields (populate-fields clazz)
        invoke (find-method clazz "invoke") ;TODO multiple arities
        decompiled (decompile-code clazz invoke fields)]
    (list 'defn (symbol fn-name) [] (first decompiled))))

(defn decompile-class [clazz]
  "Decompiles single class file"
  (cond
    (= (.getSuperclassName clazz) "clojure.lang.AFunction")
    (decompile-fn clazz)))

(defn get-classes [files]
  "Returns file paths as BCEL's JavaClasses"
  (map #(.parse (ClassParser. %)) files))

(defn -main [& paths]
  "Entry point. Decompiles class files given as commandline arguments"
  (let [classes (get-classes paths)]
    (dorun (map (comp prn decompile-class) classes))))
