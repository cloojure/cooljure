;   Copyright (c) Alan Thompson. All rights reserved. 
;   The use and distribution terms for this software are covered by the Eclipse Public
;   License 1.0 (http://opensource.org/licenses/eclipse-1.0.php) which can be found in the
;   file epl-v10.html at the root of this distribution.  By using this software in any
;   fashion, you are agreeing to be bound by the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns tupelo.dev
  (:use tupelo.core)
  (:require
    [clojure.string :as str]
    [clojure.math.combinatorics :as combo]
    [schema.core :as s] ))

(defn ^:no-doc find-idxs-impl
  [idxs data pred-fn]
  (if (empty? data)
    []
    (apply glue
      (forv [[idx val] (indexed data)]
        (let [idxs-curr (append idxs idx)]
          (if (sequential? val) ; #todo does not work for vector pred-fn
            (find-idxs-impl idxs-curr val pred-fn)
            (if (pred-fn val)
              [{:idxs idxs-curr :val val}]
              []))))))) ; #todo convert to lazy-gen/yield

(s/defn find-idxs
  "Given an N-dim data structure (nested vectors/lists) & a target value, returns
  a list of maps detailing where index values where the target value is found.

    (is= (find-idxs  [[ 1  2 3]
                      [10 11  ]
                      [ 9  2 8]]  2)
      [{:idxs [0 1], :val 2}
       {:idxs [2 1], :val 2}]) "
  [data :- [s/Any]
   tgt :- s/Any]
  (let [pred-fn (if (fn? tgt)
                  tgt
                  (fn [arg] (= tgt arg)))]
    (find-idxs-impl [] data pred-fn)))

(defn combinations-duplicate [coll n]
  "Returns all combinations of elements from the input collection, presevering duplicates."
  (let [values     (vec coll)
        idxs       (range (count values))
        idx-combos (combo/combinations idxs n)
        combos     (forv [idx-combo idx-combos]
                     (mapv #(nth values %) idx-combo))]
    combos))

(defn parse-string [line]
  (mapv read-string (str/split line #" ")))

(comment

  ; #todo add this function???
  (ns tst.demo.core
    (:use demo.core tupelo.core tupelo.test)
    (:require [clojure.string :as str]))

  (defmacro fn+ [& args]
    (println :args args)
    (let [arg-1        (first args)
          ns-str-nice  (str/replace (ns-name *ns*) "." "-")
          fn-name-auto (symbol
                         (str "fn-plus--" ns-str-nice
                              "--line-" (:line (meta &form))))
          ctx          (if (symbol? arg-1)
                         {:fn-name (str fn-name-auto arg-1)
                          :forms   (rest args)}
                         {:fn-name fn-name-auto
                          :forms   args})]
      `(fn ~(grab :fn-name ctx)
         ~@(grab :forms ctx))))


  (dotest
    (let [f1 (fn+ [x y] (/ x y))
          f2 (fn something [x y] (/ x y))]
      (println :call (f1 6 3))
      (println :boom (f1 9 0))
      )
    )
  )
