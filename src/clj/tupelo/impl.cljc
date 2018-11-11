;   Copyright (c) Alan Thompson. All rights reserved.
;   The use and distribution terms for this software are covered by the Eclipse Public License 1.0
;   (http://opensource.org/licenses/eclipse-1.0.php) which can be found in the file epl-v10.html at
;   the root of this distribution.  By using this software in any fashion, you are agreeing to be
;   bound by the terms of this license.  You must not remove this notice, or any other, from this
;   software.
(ns ^:no-doc tupelo.impl
  "Tupelo - Making Clojure even sweeter"
  (:require
    [clojure.core :as cc]
    [clojure.core.async :as ca]
    [clojure.pprint :as pprint]
    [clojure.string :as str]
    [clojure.test]
    [clojure.set :as set]
    [clojure.walk :as walk]
    [tupelo.schema :as tsk]
    [schema.core :as s]

    #?@(:clj [[cheshire.core :as cheshire]
              [clojure.core.match :as ccm]
              [tupelo.types :as types]
             ]))
  #?(:clj (:import [java.io PrintStream ByteArrayOutputStream]))
)

; #todo make sure works with cljdoc

; #todo wrap = < <= et al to throw ArityException if only 1 arg
; #todo or if not number?
; #todo wrap contains? get etc to enforce "normal" input types: map/set vs vec/list
; #todo contains-key? for map/set, contains-val? for map/set/vec/list (disable contains? for strict) (use .contains for -val)
; #todo (fnil inc 0) => (with-default-args [0 "hello" :cc]
; #todo                   some-fn-of-3-or-more-args)
; #todo    like (some-fn* (glue {0 0   1 "hello"   2 :cc} {<user args here>} ))


(defn truthy?
  "Returns true if arg is logical true (neither nil nor false); otherwise returns false."
  [arg]
  (if arg true false))

(defn falsey?
  "Returns true if arg is logical false (either nil or false); otherwise returns false. Equivalent
   to (not (truthy? arg))."
  [arg]
  (if arg false true))

(defn nl
  "Abbreviated name for `newline` "
  [] (newline))

; #todo -> README
(s/defn has-some? :- s/Bool ; #todo rename to has-any?   Add warning re new clj/any?
  "For any predicate pred & collection coll, returns true if (pred x) is logical true for at least one x in
   coll; otherwise returns false.  Like clojure.core/some, but returns only true or false."
  [pred :-  s/Any
   coll :- [s/Any] ]
  (truthy? (some pred coll)))
; NOTE: was `any?` prior to new `clojure.core/any?` added in clojure 1.9.0-alpha10

; #todo -> README
(s/defn has-none? :- s/Bool
  "For any predicate pred & collection coll, returns false if (pred x) is logical true for at least one x in
   coll; otherwise returns true.  Equivalent to clojure.core/not-any?, but inverse of has-some?."
  [pred :-  s/Any
   coll :- [s/Any] ]
  (falsey? (some pred coll))) ; #todo -> (not (has-some? pred coll))

(s/defn contains-elem? :- s/Bool
  "For any collection coll & element tgt, returns true if coll contains at least one
  instance of tgt; otherwise returns false. Note that, for maps, each element is a
  vector (i.e MapEntry) of the form [key value]."
  [coll :- s/Any
   elem :- s/Any ]
  (has-some? truthy?
    (mapv #(= elem %) (seq coll))))

(s/defn contains-key? :- s/Bool
  "For any map or set, returns true if elem is a map key or set element, respectively"
  [map-or-set :- (s/pred #(or (map? %) (set? %)))
   elem :- s/Any ]
  (contains? map-or-set elem))

(s/defn contains-val? :- s/Bool
  "For any map, returns true if elem is present in the map for at least one key."
  [map :- tsk/Map
   elem :- s/Any ]
  (has-some? truthy?
    (mapv #(= elem %) (vals map))))

(s/defn dissoc-in :- s/Any
  "A sane version of dissoc-in that will not delete intermediate keys.
   When invoked as (dissoc-in the-map [:k1 :k2 :k3... :kZ]), acts like
   (clojure.core/update-in the-map [:k1 :k2 :k3...] dissoc :kZ). That is, only
   the map entry containing the last key :kZ is removed, and all map entries
   higher than kZ in the hierarchy are unaffected."
  [the-map :- tsk/KeyMap
   keys-vec :- [s/Keyword]]
  (let [num-keys     (count keys-vec)
        key-to-clear (last keys-vec)
        parent-keys  (butlast keys-vec)]
    (cond
      (zero? num-keys) the-map
      (= 1 num-keys) (dissoc the-map key-to-clear)
      :else (update-in the-map parent-keys dissoc key-to-clear))))


(defn unlazy ; #todo need tests & docs. Use for datomic Entity?
  "Converts a lazy collection to a concrete (eager) collection of the same type."
  [coll]
  (let [unlazy-item (fn [item]
                      (cond
                        (sequential? item) (vec item)
                        (map? item) (into {} item)
                        (set? item) (into #{} item)
             #?@(:clj [ (instance? java.io.InputStream item) (slurp item) ])  ; #todo need test
                        :else item))
        result    (walk/postwalk unlazy-item coll) ]
    result ))

; #todo impl-merge *****************************************************************************

(defn has-length?
  "Returns true if the collection has the indicated length. Does not hang for infinite sequences."
  [coll n]
  (when (nil? coll) (throw (ex-info "has-length?: coll must not be nil" coll)))
  (let [take-items (cc/take n coll)
        rest-items (cc/drop n coll)]
    (and (= n (count take-items))
      (empty? rest-items))))

(defn only
  "Ensures that a sequence is of length=1, and returns the only value present.
  Throws an exception if the length of the sequence is not one.
  Note that, for a length-1 sequence S, (first S), (last S) and (only S) are equivalent."
  [coll]
  (when-not (has-length? coll 1)
    (throw (ex-info "only: num-items must=1" coll)))
  (clojure.core/first coll))

(defn onlies
  "Given an outer collection of length-1 collections, returns a sequence of the unwrapped values.
    (onlies  [ [1] [2] [3] ])  =>  [1 2 3]
    (onlies #{ [1] [2] [3] })  => #{1 2 3} "
  [coll] (into (unlazy (empty coll)) (mapv only coll)))

(defn only2
  "Given a collection like `[[5]]`, returns `5`.  Equivalent to `(only (only coll))`."
  [coll] (only (only coll)))

(defn single?
  "Returns true if the collection contains a single item.`"
  [coll] (has-length? coll 1))

(defn pair?
  "Returns true if the collection contains exactly 2 items."
  [coll] (has-length? coll 2))

(defn triple?
  "Returns true if the collection contains exactly 3 items."
  [coll] (has-length? coll 3))

(defn quad?
  "Returns true if the collection contains exactly 4 items."
  [coll] (has-length? coll 4))

; #todo make xdrop ?
(defn xtake
  "Returns the first n values from a collection.  Returns map for map colls.
  Throws if empty."
  [n coll]
  (when (or (nil? coll) (empty? coll))
    (throw (ex-info "xtake: invalid coll: " coll)))
  (let [items (cc/take n coll)
        actual (count items)]
    (when (<  actual n)
      (throw (ex-info "xtake: insufficient items" {:n n :actual actual} )))
    (if (map? coll)
      (into {} items)
      (vec items))))

(defn xfirst        ; #todo -> tests
  "Returns the first value in a list or vector. Throws if empty."
  [coll]
  (when (or (nil? coll) (empty? coll))
    (throw (ex-info "xfirst: invalid coll: " coll)))
  (nth coll 0))

; #todo fix up for maps
; #todo (it-> coll (take 2 it), (validate (= 2 (count it))), (last it))
(defn xsecond  ; #todo -> tests
  "Returns the second value in a list or vector. Throws if (< len 2)."
  [coll]
  (when (or (nil? coll) (empty? coll))
    (throw (ex-info "xsecond: invalid coll: " coll)))
  (nth coll 1))

; #todo fix up for maps
(defn xthird  ; #todo -> tests
  "Returns the third value in a list or vector. Throws if (< len 3)."
  [coll ]
  (when (or (nil? coll) (empty? coll)) (throw (ex-info "xthird: invalid coll: " coll)))
  (nth coll 2))

; #todo fix up for maps
(defn xfourth  ; #todo -> tests
  "Returns the fourth value in a list or vector. Throws if (< len 4)."
  [coll]
  (when (or (nil? coll) (empty? coll)) (throw (ex-info "xfourth: invalid coll: " coll)))
  (nth coll 3))

; #todo fix up for maps
(s/defn xlast :- s/Any ; #todo -> tests
  "Returns the last value in a list or vector. Throws if empty."
  [coll :- [s/Any]]
  (when (or (nil? coll) (empty? coll)) (throw (ex-info "xlast: invalid coll: " coll)))
  (clojure.core/last coll))

; #todo fix up for maps
(s/defn xbutlast :- s/Any ; #todo -> tests
  "Returns a vector of all but the last value in a list or vector. Throws if empty."
  [coll :- [s/Any]]
  (when (or (nil? coll) (empty? coll)) (throw (ex-info "xbutlast: invalid coll: " coll)))
  (vec (clojure.core/butlast coll)))

; #todo fix up for maps
(defn xrest ; #todo -> tests
  "Returns the last value in a list or vector. Throws if empty."
  [coll]
  (when (or (nil? coll) (empty? coll)) (throw (ex-info "xrest: invalid coll: " coll)))
  (clojure.core/rest coll))

(defn xreverse ; #todo -> tests & doc
  "Returns a vector containing a sequence in reversed order. Throws if nil."
  [coll]
  (when (nil? coll) (throw (ex-info "xreverse: invalid coll: " coll)))
  (vec (clojure.core/reverse coll)))

(s/defn xvec :- [s/Any]
  "Converts a collection into a vector. Throws if given nil."
  [coll :- [s/Any]]
  (when (nil? coll) (throw (ex-info "xvec: invalid coll: " coll)))
  (clojure.core/vec coll))

(defn glue
  "Glues together like collections:

     (glue [1 2] [3 4] [5 6])                -> [1 2 3 4 5 6]
     (glue {:a 1} {:b 2} {:c 3})             -> {:a 1 :c 3 :b 2}
     (glue #{1 2} #{3 4} #{6 5})             -> #{1 2 6 5 3 4}
     (glue \"I\" \" like \" \\a \" nap!\" )  -> \"I like a nap!\"

  If you want to convert to a sorted set or map, just put an empty one first:

     (glue (sorted-map) {:a 1} {:b 2} {:c 3})      -> {:a 1 :b 2 :c 3}
     (glue (sorted-set) #{1 2} #{3 4} #{6 5})      -> #{1 2 3 4 5 6}

   If there are duplicate keys when using glue for maps or sets, then \"the last one wins\":

     (glue {:band :VanHalen :singer :Dave}  {:singer :Sammy}) "
  [& colls]
  (let [string-or-char? #(or (string? %) (char? %))]
    (cond
      (every? sequential? colls)        (reduce into [] colls) ; coerce to vector result
      (every? map? colls)               (reduce into    colls) ; first item determines type of result
      (every? set? colls)               (reduce into    colls) ; first item determines type of result
      (every? string-or-char? colls)    (apply str colls)
      :else (throw (ex-info "glue: colls must be all same type; found types=" (mapv type colls))))))

(defn glue-rows   ; #todo :- tsk/List ; #todo necessary?
  " Convert a vector of vectors (2-dimensional) into a single vector (1-dimensional).
  Equivalent to `(apply glue ...)`"
  [coll-2d          ; :- tsk/List
   ]
  (when-not (sequential? coll-2d)
    (throw (ex-info "Sequential collection required, found=" coll-2d)))
  (when-not (every? sequential? coll-2d)
    (throw (ex-info "Nested sequential collections required, found=" coll-2d)))
  (reduce into [] coll-2d))

; #todo rename to (map-of a b c ...)  ??? (re. potpuri)
(defmacro vals->map ; #todo -> README
  [& symbols]
  (let [maps-list (for [symbol symbols]
                    {(keyword symbol) symbol})]
    `(glue ~@maps-list)) )

(defmacro with-map-vals ; #todo -> README
  [ the-map items-vec & forms]
  `(do
     ; (assert (map? ~the-map))
     ; (assert (sequential? ~items-vec))
     (let  ; generate the binding vector dynamically
       ~(apply glue
          (for [item items-vec
                :let [sym (symbol (name item))
                      kw  (keyword item)]]
            [sym (list 'grab kw the-map)]))
       ~@forms)))


;-----------------------------------------------------------------------------
; Clojure version stuff

(s/defn increasing? :- s/Bool
  "Returns true iff the vectors are in (strictly) lexicographically increasing order
    [1 2]  [1]        -> false
    [1 2]  [1 1]      -> false
    [1 2]  [1 2]      -> false
    [1 2]  [1 2 nil]  -> true
    [1 2]  [1 2 3]    -> true
    [1 2]  [1 3]      -> true
    [1 2]  [2 1]      -> true
    [1 2]  [2]        -> true "
  [a :- tsk/List
   b :- tsk/List]
  (let [len-a        (count a)
        len-b        (count b)
        cmpr         (fn [x y] (cond
                                 (= x y) :eq
                                 (< x y) :incr
                                 (> x y) :decr
                                 :else (throw (ex-info "should never get here" nil))))
        cmpr-res     (mapv cmpr a b)
        first-change (first (drop-while #{:eq} cmpr-res)) ; nil if all :eq
        ]
    (cond
      (= a b)                       false
      (= first-change :decr)        false
      (= first-change :incr)        true
      (nil? first-change)           (< len-a len-b))))

(s/defn increasing-or-equal? :- s/Bool
  "Returns true iff the vectors are in (strictly) lexicographically increasing-or-equal order
    [1 2]  [1]        -> false
    [1 2]  [1 1]      -> false
    [1 2]  [1 2]      -> true
    [1 2]  [1 2 nil]  -> true
    [1 2]  [1 2 3]    -> true
    [1 2]  [1 3]      -> true
    [1 2]  [2 1]      -> true
    [1 2]  [2]        -> true "
  [a :- tsk/List
   b :- tsk/List]
  (or (= a b)
    (increasing? a b)))

;-----------------------------------------------------------------------------
(declare clip-str
  )

;-----------------------------------------------------------------------------
(s/defn not-nil? :- s/Bool
  "Returns true if arg is not nil; false otherwise. Equivalent to (not (nil? arg)),
   or the poorly-named clojure.core/some? "
  [arg :- s/Any]
  (not (nil? arg)))

(s/defn not-empty? :- s/Bool
  "For any collection coll, returns true if coll contains any items; otherwise returns false.
   Equivalent to (not (empty? coll))."
  ; [coll :- [s/Any]]  ; #todo extend Prismatic Schema to accept this for strings
  [coll]
  (not (empty? coll)))

; #todo add not-neg? not-pos? not-zero?

; #todo make coercing versions of these ->sym ->str ->kw ->int  for args of (kw, str, sym, int)

(s/defn kw->sym :- s/Symbol
  "Converts a keyword to a symbol"
  [arg :- s/Keyword]
  (symbol (name arg)))

(s/defn kw->str :- s/Str
  "Converts a keyword to a string"
  [arg :- s/Keyword]
  (name arg))

(s/defn sym->str :- s/Str
  "Converts a symbol to a string"
  [arg :- s/Symbol]
  (name arg))

(s/defn sym->kw :- s/Keyword
  "Converts a symbol to a keyword"
  [arg :- s/Symbol]
  (keyword arg))

(s/defn str->sym :- s/Symbol
  "Converts a string to a symbol"
  [arg :- s/Str]
  (symbol arg))

; #todo throw if bad string
(s/defn str->kw :- s/Keyword
  "Converts a string to a keyword"
  [arg :- s/Str]
  (keyword arg))

(s/defn str->chars :- s/Keyword
  "Converts a string to a vector of chars"
  [arg :- s/Str]
  (vec arg))

(defn int->kw [arg]
  (keyword (str arg)))
#?(:clj
   (defn kw->int [arg]
     (Integer/parseInt (kw->str arg))))
#?(:cljs
   (defn kw->int [arg]
     (js/parseInt (kw->str arg) 10)))

#?(:clj
   (do
     ; #todo add test & README
     (defn json->edn
       "Shortcut to cheshire.core/parse-string"
       [arg]
       (cheshire/parse-string arg true)) ; true => keywordize-keys

     ; #todo add test & README
     (defn edn->json
       "Shortcut to cheshire.core/generate-string"
       [arg]
       (cheshire/generate-string arg))
     ))
#?(:cljs
   (do
     ; #todo add test & README
     (defn json->edn
       "Convert from json -> edn"
       [arg]
       (js->clj (.parse js/JSON arg) :keywordize-keys true)) ; true => keywordize-keys

     ; #todo add test & README
     (defn edn->json
       "Convert from edn -> json "
       [arg]
       (.stringify js/JSON (clj->js arg)))
     ))

; #todo:  make (map-ctx {:trunc false :eager true} <fn> <coll1> <coll2> ...) <- default ctx
; #todo:  mapz, forz, filterz, ...?
(defn keep-if
  "Returns a vector of items in coll for which (pred item) is true (alias for clojure.core/filter)"
  [pred coll]
  (cond
    (sequential? coll) (vec (clojure.core/filter pred coll))
    (map? coll) (reduce-kv (fn [cum-map k v]
                             (if (pred k v)
                               (assoc cum-map k v)
                               cum-map))
                  {}
                  coll)
    (set? coll) (reduce (fn [cum-set elem]
                          (if (pred elem)
                            (conj cum-set elem)
                            cum-set))
                  #{}
                  (seq coll))
    :else (throw (ex-info "keep-if: coll must be sequential, map, or set." coll))))

(defn drop-if
  "Returns a vector of items in coll for which (pred item) is false (alias for clojure.core/remove)"
  [pred coll]
  (keep-if (complement pred) coll))

;-----------------------------------------------------------------------------
(defn prettify
  "Recursively walks a data structure and returns a prettified version.
  Converts all lists to vectors. Converts all maps & sets to sorted collections."
  [coll]
  (let [prettify-item (fn prettify-item [item]
                        (cond
                          (sequential? item) (vec item)
                          (map? item) (into (sorted-map) item)
                          (set? item) (into (sorted-set) item)

                          #?@(:clj [ (instance? java.io.InputStream item) (prettify-item (slurp item)) ]) ; #todo need test

                          :else item))
        result        (walk/postwalk prettify-item coll)]
    result))

(defn strcat
  "Recursively concatenate all arguments into a single string result."
  [& args]
  (let [
        ; We need to use flatten twice since the inner one doesn't change a string into a
        ; sequence of chars, nor does it affect byte-array, et al.  We eventually get
        ; seq-of-scalars which can look like [ \a \b 77 78 \66 \z ]
        seq-of-scalars (flatten
                         (for [it (keep-if not-nil? (flatten [args])) ]
                           ; Note that "sequential?" returns false for sets, strings, and the various
                           ; array types.
                           (cond
                             (or
                               (sequential? it)
                               (set? it)
                               (string? it)
                    #?@(:clj [
                               (types/byte-array? it)
                               (types/char-array? it)
                               (types/int-array? it)
                               (types/long-array? it)
                               (types/object-array? it)
                               (types/short-array? it)
                             ])
                             ) (seq it)

                    #?@(:clj [ (instance? java.io.InputStream it) (seq (slurp it)) ])

                             :else it )))
        ; Coerce any integer values into character equivalents (e.g. 65 -> \A), then combine
        ; into a single string.
        result         (apply str
                         (clojure.core/map char
                           (keep-if not-nil? seq-of-scalars)))
        ]
    result))

(defn print-versions [] ; #todo need CLJS version
  #?(:clj
     (let [version-str (format "Clojure %s    Java %s"
                         (clojure-version) (System/getProperty "java.version"))
           num-hyphen  (+ 6 (count version-str))
           hyphens     (strcat (repeat num-hyphen \-))
           version-str (strcat "   " version-str)]
       (newline)
       (println hyphens)
       (println version-str)
       (println hyphens)))
  #?(:cljs
     (let [version-str (str "ClojureScript " *clojurescript-version* )
           num-hyphen  (+ 6 (count version-str))
           hyphens     (strcat (repeat num-hyphen \-))
           version-str (strcat "   " version-str)]
       (newline)
       (println hyphens)
       (println version-str)
       (println hyphens))) )

(defn seq->str
  "Convert a seq into a string (using pr) with a space preceding each value"
  [seq-in]
  (with-out-str
    (doseq [it (seq seq-in)]
      (print \space)
      (pr it))))

;-----------------------------------------------------------------------------
; spy stuff

; #todo defn-spy  saves fn name to locals for spy printout
; #todo spyxl  adds line # to spy printout

; (def ^:dynamic *spy-enabled* false)
(def ^:dynamic *spy-enabled* true) ; #TODO fix before commit!!!

(def ^:dynamic *spy-enabled-map* {})


(defmacro with-spy-enabled ; #todo README & test
  [tag ; :- s/Keyword #todo schema for macros?
   & forms ]
  `(binding [*spy-enabled-map* (assoc *spy-enabled-map* ~tag true)]
     ~@forms))

(defmacro check-spy-enabled ; #todo README & test
  [tag ; :- s/Keyword #todo schema for macros?
   & forms]
  `(binding [*spy-enabled* (get *spy-enabled-map* ~tag false)]
     ~@forms))

(def ^:no-doc spy-indent-level (atom 0))

(defn ^:no-doc spy-indent-spaces []
  (str/join (repeat (* 2 @spy-indent-level) \space)))

(defn ^:no-doc spy-indent-reset
  "Reset the spy indent level to zero."
  []
  (reset! spy-indent-level 0))

(defn ^:no-doc spy-indent-inc
  "Increase the spy indent level by one."
  []
  (swap! spy-indent-level inc))

(defn ^:no-doc spy-indent-dec
  "Decrease the spy indent level by one."
  []
  (swap! spy-indent-level dec))

;-----------------------------------------------------------------------------
; #todo  Need it?-> like some-> that short-circuits on nil
(defmacro it->
  [expr & forms]
  `(let [~'it ~expr
         ~@(interleave (repeat 'it) forms)
         ]
     ~'it))

(defn clip-str      ; #todo -> tupelo.string?
  "Converts all args to single string and clips any characters beyond nchars."
  [nchars & args]
  (it-> (apply str args)
    (take nchars it)
    (apply str it)))

(defmacro forv ; #todo wrap body in implicit do
  "Like clojure.core/for but returns results in a vector.   Not lazy."
  [& forms]
  `(vec (for ~@forms)))

;-----------------------------------------------------------------------------
(defn spy
  "A form of (println ...) to ease debugging display of either intermediate values in threading
   forms or function return values. There are three variants.  Usage:

    (spy :msg <msg-string>)
        This variant is intended for use in either thread-first (->) or thread-last (->>)
        forms.  The keyword :msg is used to identify the message string and works equally
        well for both the -> and ->> operators. Spy prints both <msg-string>  and the
        threading value to stdout, then returns the value for further propogation in the
        threading form. For example, both of the following:
            (->   2
                  (+ 3)
                  (spy :msg \"sum\" )
                  (* 4))
            (->>  2
                  (+ 3)
                  (spy :msg \"sum\" )
                  (* 4))
        will print 'sum => 5' to stdout.

    (spy <msg-string> <value>)
        This variant is intended for simpler use cases such as function return values.
        Function return value expressions often invoke other functions and cannot be
        easily displayed since (println ...) swallows the return value and returns nil
        itself.  Spy will output both <msg-string> and the value, then return the value
        for use by further processing.  For example, the following:
            (println (* 2
                       (spy \"sum\" (+ 3 4))))
      will print:
            sum => 7
            14
      to stdout.

    (spy <value>)
        This variant is intended for use in very simple situations and is the same as the
        2-argument arity where <msg-string> defaults to 'spy'.  For example (spy (+ 2 3))
        prints 'spy => 5' to stdout.  "
  ([arg1 arg2]
   (let [[tag value] (cond
                       (keyword? arg1) [arg1 arg2]
                       (keyword? arg2) [arg2 arg1]
                       :else (throw (ex-info "spy: either first or 2nd arg must be a keyword tag \n   args:" [arg1 arg2])))]
     (when *spy-enabled*
       (println (str (spy-indent-spaces) tag " => " (pr-str value))))
     value ))
  ([value] ; 1-arg arity uses a generic "spy" message
   (spy :spy value)))

(defn spyx-proc
  [exprs]
  (let [r1         (for [expr (butlast exprs)]
                     (when *spy-enabled*
                       (if (keyword? expr)
                         `(when *spy-enabled* (print (str (spy-indent-spaces) ~expr \space)))
                         `(when *spy-enabled* (println (str (spy-indent-spaces) '~expr " => " ~expr))))))
        r2         (let [expr (xlast exprs)]
                     `(let [spy-val# ~expr]
                        (when *spy-enabled*
                          (println (str (spy-indent-spaces) '~expr " => " (pr-str spy-val#))))
                        spy-val#))
        final-code `(do ~@r1 ~r2) ]
    final-code))

; #todo allow spyx to have labels like (spyx :dbg-120 (+ 1 2)):  ":dbg-120 (+ 1 2) => 3"
(defmacro spyx
  "An expression (println ...) for use in threading forms (& elsewhere). Evaluates the supplied
   expressions, printing both the expression and its value to stdout. Returns the value of the
   last expression."
  [& exprs]
  (spyx-proc exprs))

(defn ^:no-doc spy-pretty-proc ; #todo => core
  [exprs]
  (let [r1         (for [expr (butlast exprs)]
                     `(when *spy-enabled* (println (spy-indent-spaces) (str ~expr))))
        r2         (let [expr (xlast exprs)]
                     `(let [spy-val# ~expr]
                        (when *spy-enabled*
                          (println (indent-lines-with (spy-indent-spaces)
                                     (pretty-str spy-val#))))
                        spy-val#))
        final-code `(do
                      ~@r1
                      ~r2)]
    final-code))

; #todo only allow 1 arg + optional kw-label
(defmacro spy-pretty ; #todo => core
  "Like `spyx-pretty` but without printing the original form"
  [& exprs]
  (spy-pretty-proc exprs)) ; #todo add in use of `prettify` for each value

(defn ^:no-doc spyx-pretty-proc
  [exprs]
  (let [r1         (for [expr (butlast exprs)]
                     (if (keyword? expr)
                       `(when *spy-enabled* (println (spy-indent-spaces) (str ~expr)))
                       `(when *spy-enabled* (println (spy-indent-spaces) (str '~expr " => " ~expr)))))
        r2         (let [expr (xlast exprs)]
                     `(let [spy-val# ~expr]
                        (when *spy-enabled*
                          (println (str (spy-indent-spaces) '~expr " => "))
                          (println (indent-lines-with (spy-indent-spaces)
                                     (pretty-str spy-val#))))
                        spy-val#))
        final-code `(do
                      ~@r1
                      ~r2)]
    final-code))
; #todo only allow 1 arg + optional kw-label
; #todo On all spy* make print file & line number
; #todo allow spyx-pretty to have labels like (spyx-pretty :dbg-120 (+ 1 2)):  ":dbg-120 (+ 1 2) => 3"
(defmacro spyx-pretty
  "Like `spyx` but with pretty printing (clojure.pprint/pprint)"
  [& exprs]
  (spyx-pretty-proc exprs)) ; #todo add in use of `prettify` for each value

(defmacro with-spy-indent
  "Increments indentation level of all spy, spyx, or spyxx expressions within the body."
  [& forms]
  `(do
     (spy-indent-inc)
     (let [result# (do ~@forms)]
       (spy-indent-dec)
       result#)))

(defmacro let-spy
  "An expression (println ...) for use in threading forms (& elsewhere). Evaluates the supplied
   expressions, printing both the expression and its value to stdout. Returns the value of the
   last expression."
  [& exprs]
  (let [decls      (xfirst exprs)
        _          (when (not (even? (count decls)))
                     (throw (ex-info "spy-let-proc: uneven number of decls:" decls)))
        forms      (xrest exprs)
        fmt-pair   (fn [[dest src]]
                     [dest src
                      '_ (list `spyx dest)]) ; #todo gensym instead of underscore?
        pairs      (vec (partition 2 decls))
        r1         (vec (mapcat fmt-pair pairs))
        final-code `(let ~r1 ~@forms)]
    final-code))

;-----------------------------------------------------------------------------

(defmacro let-spy-pretty   ; #todo -> deprecated
  "An expression (println ...) for use in threading forms (& elsewhere). Evaluates the supplied
   expressions, printing both the expression and its value to stdout. Returns the value of the
   last expression."
  [& exprs]
  (let [decls (xfirst exprs)
        _     (when (not (even? (count decls)))
                (throw (ex-info "spy-let-pretty-impl: uneven number of decls:" decls)))
        forms (xrest exprs)
        fmt-pair (fn [[dest src]]
                   [dest src
                    '_ (list `spyx-pretty dest)] ) ; #todo gensym instead of underscore?
        pairs (vec (partition 2 decls))
        r1    (vec (mapcat  fmt-pair pairs ))
        final-code  `(let ~r1 ~@forms ) ]
    final-code ))

(defmacro let-some
  "Threads forms as with `when-some`, but allow more than 1 pair of binding forms."
  [bindings & forms]
  (let [num-bindings (count bindings)]
    (when-not (even? num-bindings)
      (throw (ex-info (str "num-bindings must be even; value=" num-bindings) bindings)))
    (if (pos? num-bindings)
      `(let [result# ~(cc/second bindings)]
         (when (not-nil? result#)
           (let [~(cc/first bindings) result#]
             (let-some ~(cc/drop 2 bindings) ~@forms))))
      `(do ~@forms))))


; #todo fix so doesn't hang if give infinite lazy seq
; #todo rename :strict -> :trunc
(defmacro map-let*
  [context bindings & forms]
  (when (empty? bindings)
    (throw (ex-info "map-let*: bindings cannot be empty=" bindings)))
  (when-not (even? (count bindings))
    (throw (ex-info "map-let*: (count bindings) must be even=" bindings)))
  (when-not (pos? (count forms))
    (throw (ex-info  "map-let*: forms cannot be empty=" forms)))
  (let [binding-pairs (partition 2 bindings)
        syms          (mapv xfirst binding-pairs)
        colls         (mapv xsecond binding-pairs) ]
    `(do
       (when-not (map? ~context)
         (throw (ex-info  "map-let*: context must be a map=" ~context)))
       (let [lazy#          (get ~context :lazy false)
             strict#        (get ~context :strict true)
             lengths#       (mapv count ~colls)
             lengths-equal# (apply = lengths#)
             map-fn#        (fn ~syms ~@forms)
             output-fn#     (if lazy# identity vec)]
         (when (and strict#
                 (not lengths-equal#))
           (throw (ex-info  "map-let*: colls must all be same length; lengths=" lengths#)))
         (output-fn# (map map-fn# ~@colls))))))

(defmacro map-let
  [bindings & forms]
  `(map-let* {:strict true
              :lazy   false}
     ~bindings ~@forms))

(s/defn append :- tsk/List
  [listy       :- tsk/List
   & elems     :- [s/Any] ]
  (when-not (sequential? listy)
    (throw (ex-info  "Sequential collection required, found=" listy)))
  (when (empty? elems)
    (throw (ex-info "Nothing to append! elems=" elems)))
  (vec (concat listy elems)))

(s/defn prepend :- tsk/List
  [& args]
  (let [elems (butlast args)
        listy (xlast args)]
    (when-not (sequential? listy)
      (throw (ex-info  "Sequential collection required, found=" listy)))
    (when (empty? elems)
      (throw (ex-info "Nothing to prepend! elems=" elems)))
    (vec (concat elems listy))))

; #todo rename :strict -> :trunc
(defn zip-1*
  "Usage:  (zip* context & colls)
  where context is a map with default values:  {:strict true}
  Not lazy. "
  [context & colls] ; #todo how use Schema with "rest" args?
  (assert (map? context))
  (assert #(every? sequential? colls))
  (let [strict        (get context :strict true)
        lengths       (mapv count colls)
        lengths-equal (apply = lengths) ]
    (when (and strict
            (not lengths-equal))
      (throw (ex-info  "zip*: colls must all be same length; lengths=" lengths)))
    (vec (apply map vector colls))))
; #todo fix so doesn't hang if give infinite lazy seq. Technique:
;  (def x [1 2 3])
;  (seq (drop 2 x))          =>  (3)
;  (seq (drop 3 x))          =>  nil
;  (nil? (seq (drop 3 x)))   =>  true
;  (nil? (drop 3 (range)))   =>  false

; #todo rename :strict -> :trunc
(defn zip*
  [context & colls] ; #todo how use Schema with "rest" args?
  (assert (map? context))
  (assert #(every? sequential? colls))
  (let [num-colls  (count colls)
        strict-flg (get context :strict true)]
    (loop [result []
           colls  colls]
      (let [empty-flgs  (mapv empty? colls)
            num-empties (count (keep-if truthy? empty-flgs)) ]
        (if (zero? num-empties)
          (do
            (let [new-row (mapv xfirst colls)
                  new-results (append result new-row) ]
              (recur
                new-results
                (mapv xrest colls))))
          (do
            (when (and strict-flg
                    (not= num-empties num-colls))
              (throw (ex-info "zip*: collections are not all same length; empty-flgs=" empty-flgs)))
            result))))))

; #todo add schema; result = tsk/List[ tsk/Pair ]
; #todo add :trunc & assert;
(defn zip
  ; #todo ***** WARNING - will hang for infinite length inputs *****
  ; #todo fix so doesn't hang if give infinite lazy seq. Technique:
  ; #todo Use (zip ... {:trunc true}) if you want to truncate all inputs to the length of the shortest.
  [& args]
  (assert #(every? sequential? args))
  (apply zip* {:strict true} args))

(defn zip-lazy
  [& colls]  ; #todo how use Schema with "rest" args?
  (assert #(every? sequential? colls))
  (apply map vector colls))

(defn indexed
  [& colls]
  (apply zip-lazy (range) colls))

(defmacro lazy-cons
  [curr-val recursive-call-form]
  `(lazy-seq (cons ~curr-val ~recursive-call-form)))


(defn rel=
  "Returns true if 2 double-precision numbers are relatively equal, else false.  Relative equality
   is specified as either (1) the N most significant digits are equal, or (2) the absolute
   difference is less than a tolerance value.  Input values are coerced to double before comparison.
   Example:

     (rel= 123450000 123456789   :digits 4   )  ; true
     (rel= 1         1.001       :tol    0.01)  ; true
   "
  [val1 val2 & {:as opts}]
  {:pre  [(number? val1) (number? val2)]
   :post [(contains? #{true false} %)]}
  (let [{:keys [digits tol]} opts]
    (when-not (or digits tol)
      (throw (IllegalArgumentException.
               (str "Must specify either :digits or :tol" \newline
                 "opts: " opts))))
    (when tol
      (when-not (number? tol)
        (throw (IllegalArgumentException.
                 (str ":tol must be a number" \newline
                   "opts: " opts))))
      (when-not (pos? tol)
        (throw (IllegalArgumentException.
                 (str ":tol must be positive" \newline
                   "opts: " opts)))))
    (when digits
      (when-not (integer? digits)
        (throw (IllegalArgumentException.
                 (str ":digits must be an integer" \newline
                   "opts: " opts))))
      (when-not (pos? digits)
        (throw (IllegalArgumentException.
                 (str ":digits must positive" \newline
                   "opts: " opts)))))
    ; At this point, there were no invalid args and at least one of
    ; either :tol and/or :digits was specified.  So, return the answer.
    (let [val1      (double val1)
          val2      (double val2)
          delta-abs (Math/abs (- val1 val2))
          or-result (truthy?
                      (or (zero? delta-abs)
                        (and tol
                          (let [tol-result (< delta-abs tol)]
                            tol-result))
                        (and digits
                          (let [abs1          (Math/abs val1)
                                abs2          (Math/abs val2)
                                max-abs       (Math/max abs1 abs2)
                                delta-rel-abs (/ delta-abs max-abs)
                                rel-tol       (Math/pow 10 (- digits))
                                dig-result    (< delta-rel-abs rel-tol)]
                            dig-result))))
          ]
      or-result)))

(defn all-rel=
  "Applies"
  [x-vals y-vals & opts]
  (let [num-x (count x-vals)
        num-y (count y-vals)]
    (when-not (= num-x num-y)
      (throw (IllegalArgumentException.
               (str ": x-vals & y-vals must be same length" \newline
                 "  #x: " num-x "  #y: " num-y)))))
  (every? truthy?
    (clojure.core/map #(apply rel= %1 %2 opts)
      x-vals y-vals)))


(defn range-vec [& args]
  (vec (apply range args)))

; #todo need docs & tests
; #todo:  add (thru a b)     -> [a..b] (inclusive)
;             (thru 1 3)     -> [ 1  2  3]
;             (thru \a \c)   -> [\a \b \c]
;             (thru :a :c)   -> [:a :b :c]
;             (thru 'a 'c)   -> ['a 'b 'c]
;             (thru 1   2   0.1)     -> [1.0  1.1  1.2 ... 2.0]
;             (thru 0.1 0.3 0.1)     -> [0.1  0.2  0.3]
;                  (thru start stop step) uses integer steps and
;                  (rel= curr stop :tol step) as ending criteria
;  #todo range version => (butlast (thru ...))
(defn thru          ; #todo make lazy: (thruz ...) -> (thru* {:lazy true} ...)
  ([end]       (thru 0 end))
  ([start end] (thru start end 1))
  ([start end step]
   (let [delta          (- (double end)   (double start))
         nsteps-dbl     (/ (double delta) (double step))
         nsteps-int     (Math/round nsteps-dbl)
         rounding-error (Math/abs (- nsteps-dbl nsteps-int)) ]
     (when (< 0.00001 rounding-error)
       (throw (ex-info "thru: non-integer number of steps \n   args:" (vals->map start end step))))
     (vec (clojure.core/map #(-> %
                               (* step)
                               (+ start))
            (range (inc nsteps-int)))))))

; #todo need test, readme
; #todo merge into `thru` using a protocol for int, double, char, string, keyword, symbol, other?
(defn chars-thru
  [start-char stop-char]
  {:pre [ (char start-char) (char stop-char) ] }
  ; These "dummy" casts are to ensure that any input integer values are within the valid
  ; range for Unicode characters
  (let [start-val   (int start-char)
        stop-val    (int stop-char)]
    (when-not (<= start-val stop-val)
      (throw (ex-info "char-seq: start-char must come before stop-char." (vals->map start-val stop-val))))
    (mapv char (thru start-val stop-val))))

; #todo rename to "get-in-safe" ???
; #todo make throw if not Associative arg (i.e. (get-in '(1 2 3) [0]) -> throw)
; #todo make throw if any index invalid
; #todo need safe (assoc-in m [ks] v) (assoc-in m [ks] v :missing-ok)
; #todo need safe (update-in m [ks] f & args)
(s/defn fetch-in :- s/Any
  [the-map   :- tsk/Map
   keys-vec  :- tsk/Vec ]
  (let [result (get-in the-map keys-vec ::not-found)]
    (if (= result ::not-found)
      (throw (ex-info "Key seq not present in map:" (vals->map the-map keys-vec)))
      result)))

(s/defn fetch :- s/Any
  [the-map :- tsk/Map
   the-key :- s/Any]
  (fetch-in the-map [the-key]))

; #todo:  (grab [:person :address :zip] the-map)  => fetch-in
; #todo:  (grab-all :name :phone [:address :zip] the-map)
; #todo:      => (mapv #(grab % the-map) keys)
(s/defn grab :- s/Any
  [the-key :- s/Any
   the-map :- tsk/Map]
  (fetch-in the-map [the-key]))

(defrecord Unwrapped [data])
(s/defn unwrap :- Unwrapped
  [data :- [s/Any]]
  (assert (sequential? data))
  (->Unwrapped data))

(s/defn ->vector :- [s/Any]
  [& args :- [s/Any]]
  (let [result (reduce (fn [accum item]
                         (let [it-use (cond
                                        (sequential? item) [ (apply ->vector item) ]
                                        (instance? Unwrapped item) (apply ->vector (fetch item :data))
                                        :else [item])
                               accum-out (glue accum it-use ) ]
                           accum-out ))
                 [] args)]
    result))

(s/defn unnest :- [s/Any] ; #todo readme
  [& values]
  (let [unnest-coll (fn fn-unnest-coll [coll]
                      (apply glue
                        (for [item coll]
                          (if (coll? item)
                            (fn-unnest-coll item)
                            [item]))))
        result      (apply glue
                      (for [item values]
                        (if (coll? item)
                          (unnest-coll item)
                          [item])))]
    result))

(defn cond-it-impl
  [expr & forms]
  (let [num-forms (count forms)]
    (when-not (even? num-forms)
      (throw (ex-info "num-forms must be even; value=" (vals->map num-forms forms)))))
  (let [cond-action-pairs (partition 2 forms)
        cond-action-forms (for [[cond-form action-form] cond-action-pairs]
                            `(if ~cond-form
                               ~action-form
                               ~'it)) ]
    `(it-> ~expr ~@cond-action-forms)))

(defmacro cond-it->
  [& forms]
  (apply cond-it-impl forms))

; #todo #wip
(defmacro some-it->
  [expr & forms]
  (let [binding-pairs (interleave (repeat 'it) forms) ]
    `(let-some [~'it ~expr
                            ~@binding-pairs]
       ~'it)))


(defmacro with-exception-default
  [default-val & forms]
  `(try
     ~@forms
     (catch
       #?(:clj Exception)
       #?(:cljs js/Object) ; js/Error  :default
       e# ~default-val)))

(defn validate
  [is-valid? sample-val]
  (let [tst-result (is-valid? sample-val)]
    (when-not (truthy? tst-result)
      (throw (ex-info  "validate: " (vals->map sample-val tst-result))))
    sample-val))

(defn validate-or-default
  [is-valid? sample-val default-val]
  (if (is-valid? sample-val)
    sample-val
    default-val))

(defn with-nil-default
  [default-val sample-val]
  (validate-or-default not-nil? sample-val default-val))

(defmacro verify
  [form]
  `(let [value# ~form]
     (if (truthy? value#)
       value#
       (throw (ex-info "verification failed  " '~form)))))

;-----------------------------------------------------------------------------
; #todo need option for (take 3 coll :exact) & drop; xtake xdrop

; #todo fix up for maps
(defn rand-elem
  [coll]
  (verify (not-nil? coll))
  (rand-nth (vec coll)))

; #todo add (->sorted-map <map>)        => (into (sorted-map) <map>)
; #todo add (->sorted-set <set>)        => (into (sorted-set) <set>)
; #todo add (->sorted-vec <sequential>) => (vec (sort <vec>))

(s/defn lexical-compare :- s/Int
  [a :- tsk/List
   b :- tsk/List]
  (cond
    (= a b) 0
    (empty? a) -1
    (empty? b) 1
    :else (let [a0 (xfirst a)
                b0 (xfirst b)]
            (if (= a0 b0)
              (lexical-compare (xrest a) (xrest b))
              (compare a0 b0)))))

; #todo maybe submap-without-keys, submap-without-vals ?
; #todo filter by pred in addition to set/list?
; #todo -> README
(s/defn submap-by-keys :- tsk/Map
  [map-arg :- tsk/Map
   keep-keys :- (s/either tsk/Set tsk/List)
   & opts]
 ;(println :awt00 map-arg)
  (let [keep-keys (set keep-keys)]
   ;(println :awt01 keep-keys)
   ;(println :awt02 opts)
    (if (= opts [:missing-ok])
      (do
       ;(println :awt10 )
        (apply glue {}
          (for [key keep-keys]
            (with-exception-default {}
              {key (grab key map-arg)}))))
      (do
       ;(println :awt20 )
        (apply glue {}
          (for [key keep-keys]
            {key (grab key map-arg)}))))))

; #todo -> README
(s/defn submap-by-vals :- tsk/Map
  [map-arg :- tsk/Map
   keep-vals :- (s/either tsk/Set tsk/List)
   & opts]
  (let [keep-vals    (set keep-vals)
        found-map    (into {}
                       (for [entry map-arg
                             :let [entry-val (val entry)]
                             :when (contains? keep-vals entry-val)]
                         entry))
        found-vals   (into #{} (vals found-map))
        missing-vals (set/difference keep-vals found-vals)]
    (if (or (empty? missing-vals) (= opts [:missing-ok]))
      found-map
      (throw (ex-info "submap-by-vals: " (vals->map missing-vals map-arg))))))

; #todo need README
(s/defn submap? :- s/Bool
  [inner-map :- {s/Any s/Any}                           ; #todo
   outer-map :- {s/Any s/Any}]                          ; #todo
  (let [inner-set (set inner-map)
        outer-set (set outer-map)]
    (set/subset? inner-set outer-set)))

(s/defn keyvals :- [s/Any]
  [m :- tsk/Map ]
  (reduce into [] (seq m)))

(s/defn keyvals-seq :- [s/Any]
  [ctx :- tsk/KeyMap]
  (with-map-vals ctx [missing-ok the-map the-keys]
    (apply glue
      (for [key the-keys]
        (let [val (get the-map key ::missing)]
          (if-not (= val ::missing)
            [key val]
            (if missing-ok
              []
              (throw (ex-info "Key not present in map:" (vals->map the-map key))))))))))




; #todo ***** toptop **********************************************************************************
#?(:clj (do

(ns-unmap *ns* 'first) ; #todo -> (set-tupelo-strict! true/false)
(ns-unmap *ns* 'second)
(ns-unmap *ns* 'rest)
(ns-unmap *ns* 'next)
(ns-unmap *ns* 'last)

(defn is-clojure-1-7-plus? []
  (let [{:keys [major minor]} *clojure-version*]
    (increasing-or-equal? [1 7] [major minor])))

(defn is-clojure-1-8-plus? []
  (let [{:keys [major minor]} *clojure-version*]
    (increasing-or-equal? [1 8] [major minor])))

(defn is-clojure-1-9-plus? []
  (let [{:keys [major minor]} *clojure-version*]
    (increasing-or-equal? [1 9] [major minor])))

(defn is-pre-clojure-1-8? [] (not (is-clojure-1-8-plus?)))
(defn is-pre-clojure-1-9? [] (not (is-clojure-1-9-plus?)))

; #todo add is-clojure-1-8-max?
; #todo need clojure-1-8-plus-or-throw  ??

(defmacro when-clojure-1-8-plus
  "Wraps code that should only be included for Clojure 1.8 or higher.  Otherwise, code is supressed."
  [& forms]
  (if (is-clojure-1-8-plus?)
    `(do ~@forms)))

(defmacro when-clojure-1-9-plus
  "Wraps code that should only be included for Clojure 1.9 or higher.  Otherwise, code is supressed."
  [& forms]
  (if (is-clojure-1-9-plus?)
    `(do ~@forms)))

(defmacro when-not-clojure-1-9-plus
  "Wraps code that should only be included for Clojure versions prior to 1.9.  Otherwise, code is supressed."
  [& forms]
  (if (is-pre-clojure-1-9?)
    `(do ~@forms)))

;----------------------------------------------------------------------------
(when-clojure-1-9-plus
  (require
    '[clojure.spec.alpha :as sp]
    '[clojure.spec.gen.alpha :as gen]
    '[clojure.spec.test.alpha :as stest] ))

(defmacro spyxx
  "An expression (println ...) for use in threading forms (& elsewhere). Evaluates the supplied
   expression, printing both the expression, its type, and its value to stdout, then returns the value."
  [expr]
  `(let [spy-val#    ~expr
         class-name# (-> spy-val# class .getName)]
     (when *spy-enabled*
       (println (str (spy-indent-spaces) '~expr " => <#" class-name# " " (pr-str spy-val#) ">")))
     spy-val#))

; #todo gogo ---------------------------------------------------------------------------------------------------


; #todo Need safe versions of:
; #todo    + - * /  (others?)  (& :strict :safe reassignments)
; #todo    and, or    (& :strict :safe reassignments)
; #todo    = not=   (others?)  (& :strict :safe reassignments)
; #todo    (drop-last N coll)  (take-last N coll)
; #todo    subvec
; #todo    others???

; #todo add postwalk and change to all sorted-map, sorted-set
; #todo rename to pp or pprint ?
; #todo add test & README
(defn pretty                                                ; #todo experimental
  ([arg]
   (pprint/pprint arg)
   arg)
  ([arg writer]
   (pprint/pprint arg writer)
   arg))

; #todo add test & README
; #todo defer to tupelo.impl/pretty
(defn pretty-str
  [arg]
  (with-out-str (pprint/pprint arg)))

(s/defn indent-lines-with :- s/Str  ; #todo add readme ;  need test
  "Splits out each line of txt using clojure.string/split-lines, then
  indents each line by prepending it with the supplied string. Joins lines together into
  a single string result, with each line terminated by a single \newline."
  [indent-str :- s/Str
   txt  :- s/Str]
  (str/join
    (interpose \newline
      (for [line (str/split-lines txt)]
        (str indent-str line)))))

(comment
  (is= (merge-deep  ; #todo need a merge-deep where
         {:a {:b 2}}
         {:a {:c 3}})
    {:a {:b 2
         :c 3}}))

;-----------------------------------------------------------------------------
; clojure.spec stuff
(when-clojure-1-9-plus
  (sp/def ::anything (sp/spec (constantly true) :gen gen/any-printable))
  (sp/def ::nothing  (sp/spec (constantly false)))

  ; #todo how to test the :ret part?
  (sp/fdef truthy?
    :args (sp/cat :arg ::anything)
    :ret boolean?)

  (sp/fdef falsey?
    :args (sp/cat :arg ::anything)
    :ret boolean?
    :fn #(= (:ret %) (not (truthy? (-> % :args :arg))))))

(s/defn sequential->idx-map :- {s/Any s/Any} ; #todo move
  [data :- [s/Any]]
  (into (sorted-map)
    (map-indexed (fn [idx val] [idx val])
      data)))

(defn char->sym [ch] (symbol (str ch))) ; #todo move

(defn get-in-strict [data path] ; #todo move
  (let [result (get-in data path ::not-found)]
    (when (= result ::not-found)
      (throw (ex-info "destruct(get-in-strict): value not found" {:data data :path path})))
    result))

(defn ^:no-doc destruct-tmpl-analyze
  [ctx]
  (with-map-vals ctx [parsed path tmpl]
    ;(spyx path)
    (cond
      (map? tmpl)
      (doseq [entry tmpl]
        ;(spyx entry)
        (let [[curr-key curr-val] entry]
          ;(spyx [curr-key curr-val])
          (let [path-new (append path curr-key)]
            ;(spyx path-new)
            (if (symbol? curr-val)
              (let [var-sym (if (= curr-val (char->sym \?))
                              (kw->sym curr-key)
                              curr-val)]
                (swap! parsed append {:path path-new :name var-sym}))
              (destruct-tmpl-analyze {:parsed parsed :path path-new :tmpl curr-val})))))

      (sequential? tmpl)
      (do
        ;(spy :tmpl-51 tmpl)
        (destruct-tmpl-analyze {:parsed parsed :path path :tmpl (sequential->idx-map tmpl)}))

      :else (println :oops-44))))

(defn ^:no-doc is-restruct-one?
  "Return true if receive a form like either `(restruct)` or `(restruct info)` (i.e. either zero or one symbol args)."
  [form]
  (and (list? form)
    (= 2 (count form))
    (= 'restruct (cc/first form))))

(defn ^:no-doc destruct-impl
  [bindings forms]
  (when (not (even? (count bindings)))
    (throw (ex-info "destruct: uneven number of bindings:" bindings)))
  (when (empty? bindings)
    (throw (ex-info "destruct: bindings empty:" bindings)))
  (let [binding-pairs (partition 2 bindings)
        datas         (mapv cc/first binding-pairs)
        tmpls         (mapv cc/second binding-pairs)
        tmpls-parsed  (vec (for [tmpl tmpls]
                             (let [parsed (atom [])]
                               (destruct-tmpl-analyze {:parsed parsed :path [] :tmpl tmpl})
                               @parsed)))]
    ; (spyx tmpls-parsed)
    ; look for duplicate variable names
    (let [var-names (vec (for [tmpl-parsed   tmpls-parsed
                               path-name-map tmpl-parsed]
                           (grab :name path-name-map)))]
      ; (spyx var-names)
      (when (not= var-names (distinct var-names))
        (println "destruct: var-names not unique" var-names)
        (throw (ex-info "destruct: var-names not unique" var-names))))

    (let [data-parsed-pairs (zip datas tmpls-parsed)]
      ; (spyx data-parsed-pairs)
      (let [extraction-pairs    (apply glue
                                  (for [[data parsed] data-parsed-pairs
                                        {:keys [name path]} parsed]
                                    [name `(get-in-strict ~data ~path)]))
            ; >>   (do (nl) (spyx extraction-pairs))

            construct-one-pairs (apply glue
                                  (for [[data parsed] data-parsed-pairs]
                                    {data (apply glue
                                            (for [{:keys [name path]} parsed]
                                              `[~data (assoc-in ~data ~path ~name)]))}))
            ; >>   (do (nl) (spyx-pretty construct-one-pairs))

            construct-all-pairs (apply glue (vals construct-one-pairs))
            ; >>   (spyx-pretty construct-all-pairs)

            restruct-one-defs   (apply glue
                                  (for [[data construction-pairs] construct-one-pairs]
                                    {data (apply list `[fn []
                                                        (let [~@construction-pairs]
                                                          ~data)])}))
            ; >>   (do (nl) (spyx-pretty restruct-one-defs))

            restruct-only-def   (when (= 1 (count datas))
                                  (let [[data construction-pairs] (only construct-one-pairs)] ; #todo test single data case
                                    (apply list `[fn []
                                                  (let [~@construction-pairs]
                                                    ~data)])))
            ; >>   (do (nl) (spyx-pretty restruct-only-def))

            restruct-all-def    (apply list `[fn []
                                              (let [~@construct-all-pairs]
                                                (vals->map ~@datas))])
            ; >>   (do (nl) (spyx-pretty restruct-all-def))

            res-raw             `(let [~@extraction-pairs]
                                   ~@forms)
            ; >>   (do (nl) (spyx-pretty res-raw))

            res-all             (walk/postwalk
                                  (fn [form]
                                    (if (not= form '(restruct-all))
                                      form
                                      (list 'let ['restruct-fn restruct-all-def
                                                  'result (list 'restruct-fn)]
                                        'result)))
                                  res-raw)
            ; >>   (do (nl) (spyx-pretty res-all))

            res-one             (walk/postwalk
                                  (fn [form]
                                    (if-not (is-restruct-one? form)
                                      form
                                      (let [restr-one-data (cc/second form)
                                            restr-one-def  (get restruct-one-defs restr-one-data ::not-found) ]
                                        (list 'let ['restruct-fn restr-one-def
                                                    'result (list 'restruct-fn)]
                                          'result))))
                                  res-all)
            ; >>   (do (nl) (spyx-pretty res-one))

            res-only            (walk/postwalk
                                  (fn [form]
                                    (if (not= form '(restruct))
                                      form
                                      (if (not= 1 (count datas)) ; #todo test exception works
                                        (do
                                          (println "(restruct) error: more than 1 data src present" datas)
                                          (throw (IllegalArgumentException. "restruct:  aborting...")))
                                        (list 'let ['restruct-fn restruct-only-def
                                                    'result (list 'restruct-fn)]
                                          'result))))
                                    res-one) ]
        ; (do (nl) (spyx-pretty res-only))
        res-only ))))

(defmacro destruct
  [bindings & forms]
  (destruct-impl bindings forms))

; #todo max-key -> t/max-by

(defn chan->lazy-seq ; #todo add schema, add tests, readme
  [chan]
  (let [curr-item (ca/<!! chan)] ; #todo ta/take-now!
    (when (not-nil? curr-item)
      (lazy-cons curr-item (chan->lazy-seq chan)))))

; #todo document use via binding
(def ^:dynamic *lazy-gen-buffer-size*
  "Default output buffer size for `lazy-gen`."
  32)

; #todo add to README
; #todo fix SO posting:  defgen -> lazy-gen
; #todo make null case return [] instead of nil
; #todo make eager version?  gen-vec, gen-seq, ...
(defmacro lazy-gen
  [& forms]
  `(let [~'lazy-gen-output-buffer (ca/chan *lazy-gen-buffer-size*) ]
        (ca/go
          ~@forms
          (ca/close! ~'lazy-gen-output-buffer))
        (chan->lazy-seq ~'lazy-gen-output-buffer)))

(defmacro yield ; #todo put-now/put-later & dynamic
  [value]
  `(do
     (ca/>! ~'lazy-gen-output-buffer ~value)
     ~value))

(defmacro yield-all
  [values]
  `(do
     (doseq [value# ~values]
       (yield value#))
     (vec ~values)))

; #todo rename -> drop-idx
; #todo force to vector result
; #todo allow range to drop
(s/defn drop-at :- tsk/List
  [coll :- tsk/List
   index :- s/Int]
  (when (neg? index)
    (throw (IllegalArgumentException. (str "Index cannot be negative: " index))))
  (when (<= (count coll) index)
    (throw (IllegalArgumentException. (str "Index cannot exceed collection length: "
                                        " (count coll)=" (count coll) " index=" index))))
  (glue (take index coll)
    (drop (inc index) coll)))

; #todo rename -> insert-idx
; #todo force to vector result
; #todo allow vector to insert
(s/defn insert-at :- tsk/List
  [coll :- tsk/List
   index :- s/Int
   elem :- s/Any]
  (when (neg? index)
    (throw (IllegalArgumentException. (str "Index cannot be negative: " index))))
  (when (< (count coll) index)
    (throw (IllegalArgumentException. (str "Index cannot exceed collection length: "
                                        " (count coll)=" (count coll) " index=" index))))
  (glue (take index coll) [elem]
    (drop index coll)))

; #todo rename -> elem-set
; #todo force to vector result
; #todo allow idx range to replace with vector (maybe not equal # of elems)
(s/defn replace-at :- tsk/List
  [coll :- tsk/List
   index :- s/Int
   elem :- s/Any]
  (when (neg? index)
    (throw (IllegalArgumentException. (str "Index cannot be negative: " index))))
  (when (<= (count coll) index)
    (throw (IllegalArgumentException. (str "Index cannot exceed collection length: "
                                        " (count coll)=" (count coll) " index=" index))))
  (glue
    (take index coll)
    [elem]
    (drop (inc index) coll)))

; #todo make replace-in that is like assoc-in but verifies path first !!! (merge with replace-at)

; #todo use (idx    coll int-or-kw) as `get` replacement?
; #todo use (idx-in coll [kw's]) as `fetch-in` replacement?
; #todo allow (idx coll [low high]) like python xx( low:high )
; #todo multiple dimensions
(s/defn idx
  [coll       :- tsk/List
   index-val  :- s/Int]
  (when (nil? coll)
    (throw (IllegalArgumentException. (str "idx: coll cannot be nil: " coll))))
  (let [data-vec (vec coll)
        N        (count data-vec)
        >>       (assert (pos? N))
        ii       (mod index-val N)
        >>       (when (<= (count coll) ii)
                   (throw (IllegalArgumentException. (str "Index cannot exceed collection length: "
                                                       " (count coll)=" (count coll) " index=" ii))))
        result   (clojure.core/get data-vec ii)]
    result))

(defmacro matches?
  [pattern & values]
  `(and ~@(forv [value values]
            `(ccm/match ~value
               ~pattern true
               :else false))))

(def MapKeySpec (s/either [s/Any] #{s/Any}))
(s/defn validate-map-keys :- s/Any
  [tst-map :- tsk/Map
   valid-keys :- MapKeySpec]
  (let [valid-keys (set valid-keys)
        map-keys   (keys tst-map)]
    (when-not (every? truthy?
                (forv [curr-key map-keys]
                  (contains-key? valid-keys curr-key)))
      (throw (IllegalArgumentException. (format "validate-map-keys: invalid key found tst-map=%s, valid-keys=%s" tst-map valid-keys))))
    tst-map))

(s/defn map-keys :- tsk/Map ; #todo README
  [map-in :- tsk/Map
   tx-fn  :- tsk/Fn
   & tx-args ]
  (let [tuple-seq-orig (vec map-in)
        tuple-seq-out  (for [[tuple-key tuple-val] tuple-seq-orig]
                         [ (apply tx-fn tuple-key tx-args) tuple-val])
        map-out        (into {} tuple-seq-out) ]
    map-out))

(s/defn map-vals :- tsk/Map ; #todo README
  [map-in :- tsk/Map
   tx-fn  :- tsk/Fn
   & tx-args ]
  (let [tuple-seq-orig (vec map-in)
        tuple-seq-out  (for [[tuple-key tuple-val] tuple-seq-orig]
                         [tuple-key (apply tx-fn tuple-val tx-args) ])
        map-out        (into {} tuple-seq-out) ]
    map-out))

(defn macro?
  [s]
  (-> s resolve meta :macro boolean))
    ; from Alex Miller StackOverflow answer 2017-5-6

(s/defn val= :- s/Bool
  [& vals]
  (let [mapify   (fn [arg]
                   (if (map? arg)
                     (into {} arg)
                     arg))
        mapified (mapv #(walk/postwalk mapify %) vals)
        result   (apply = mapified)]
    result))

; #todo allow pred fn to replace entire node in search path:
; #todo    (fn [node] (and (contains? #{:horse :dog} (grab :animal/species node))
; #todo                 (<= 1 (grab :age node) 3 )))   ; an "adolescent" animal
(s/defn ^:private ^:no-doc wild-match-impl
  [ctx :- tsk/KeyMap ; #todo more precise schema needed { :submap-ok s/Bool ... }
   pattern :- s/Any
   value :- s/Any ]
  (with-map-vals ctx [submap-ok subset-ok subvec-ok wildcard-ok]
    (let [result (truthy?
                   (cond
                     (= pattern value)   true

                     (and wildcard-ok
                       (= pattern :*))   true

                     (and (map? pattern) (map? value))
                         (let [keyset-pat (set (keys pattern))
                               keyset-val (set (keys value))]
                           (and
                             (or (= keyset-pat keyset-val)
                               (and submap-ok ; #todo need test
                                 (set/subset? keyset-pat keyset-val)))
                             (every? truthy?
                               (forv [key keyset-pat]
                                 (wild-match-impl ctx
                                   (grab key pattern)
                                   (grab key value))))))

                     (and (set? pattern) (set? value)) ; #todo need test
                         (or (= pattern value)
                           (and subset-ok
                             (set/subset? pattern value)))

                     (and (coll? pattern) (coll? value))
                         (let [num-pat     (count pattern)
                               num-val     (count value)
                               lengths-ok? (or (= num-pat num-val) ; #todo need test
                                             (and subvec-ok
                                               (<= num-pat num-val)))]
                           (and lengths-ok?
                             (every? truthy?
                               (mapv #(wild-match-impl ctx %1 %2) pattern value)))) ; truncates shortest

                     :default false)) ]
      result)))

(defn wild-match? ; #todo readme
  [ctx-in]
  (let [ctx (glue {:submap-ok   false
                   :subset-ok   false
                   :subvec-ok   false
                   :wildcard-ok true }
              ctx-in)]
    (with-map-vals ctx [pattern values]
      (every? truthy?
        (for [value values]
          (wild-match-impl ctx pattern value))))))

(s/defn wild-item? :- s/Bool
  [item :- s/Any]
  (has-some? #(= :* %) (unnest [item])))

(defn set-match-impl
  [ctx pattern data]
  (or
    (= pattern :*)
    (= pattern data)
    (if (empty? pattern)
      (empty? data) ; #todo or :subset-ok
      (let [sub-pat     (xfirst (seq pattern))
            pattern-new (set/difference pattern #{sub-pat})]
        (if (wild-item? sub-pat)
          ; wildcard pattern
          (loop [items (seq data)]
            (if (empty? items)
              false
              (let [item     (xfirst items)
                    data-new (set/difference data #{item})]
                (if (and
                      (set-match-impl ctx sub-pat item)
                      (set-match-impl ctx pattern-new data-new)
                      )
                  true
                  (recur (xrest items))))))
          ; non-wildcard pattern
          (and (contains? data sub-pat)
            (let [data-new (set/difference data #{sub-pat})]
              (set-match-impl ctx pattern-new data-new))))))))

(defn set-match-ctx? [ctx-in pattern & values]
  (let [ctx (glue {:subset-ok false} ctx-in)]
  (every? truthy?
    (for [value values]
      (set-match-impl ctx pattern value)))))

(defn set-match? [pattern & values]
  (every? truthy?
      (for [value values]
        (set-match-impl {} pattern value))))

; #todo maybe ns-assoc, ns-dissoc, ns-get for intern/ns-unmap

; #todo maybe add explicit arg checking
; #todo   map->entries, entries->map
; #todo   str->chars, chars->str
; #todo   set->vec, vec->set
; #todo   line-seq et al not lazy (+ tupelo.lazy orig)

))

