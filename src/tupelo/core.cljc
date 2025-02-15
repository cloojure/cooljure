;   Copyrigh (c) Alan Thompson. All rights reserved.
;   The use and distribution terms for this software are covered by the Eclipse Public License 1.0
;   (http://opensource.org/licenses/eclipse-1.0.php) which can be found in the file epl-v10.html at
;   the root of this distribution.  By using this software in any fashion, you are agreeing to be
;   bound by the terms of this license.  You must not remove this notice, or any other, from this
;   software.
(ns tupelo.core
  "Tupelo - Making Clojure even sweeter"
  ; We use the self-require trick to force separate compilation stages for macros
  ; See "ClojureScript Macro Tower & Loop" by Mike Fikes (2015-12-18)
  ;   https://code.thheller.com/blog/shadow-cljs/2019/10/12/clojurescript-macros.html
  ;   http://blog.fikesfarm.com/posts/2015-12-18-clojurescript-macro-tower-and-loop.html
  #?(:cljs (:require-macros
             [tupelo.core.impl]
             [tupelo.core :refer [it-> cond-it-> some-it->
                                  vals->map with-map-vals forv
                                  with-spy-indent spyx spyxx spy-pretty spyx-pretty
                                  let-spy let-spy-pretty let-some map-let* map-let lazy-cons
                                  assert-info try-catchall with-exception-default verify-form
                                  if-java-1-8-plus
                                  when-clojure-1-8-plus when-clojure-1-9-plus when-not-clojure-1-9-plus
                                  destruct lazy-gen yield yield-all matches?]]))

  (:require
    [clojure.core :as cc]
    [clojure.core.async :as async]
    [clojure.data.avl :as avl]
    [clojure.pprint :as pprint]
    [clojure.set :as set]
    [clojure.string :as str]
    [clojure.walk :as walk]
    [schema.core :as s]
    [tupelo.core.impl :as impl]
    [tupelo.lexical :as lex]
    [tupelo.schema :as tsk])
  #?(:clj (:require [clojure.data.json :as json]
                    [clojure.core.match :as ccm]
                    [flatland.ordered.map :as omap]
                    [flatland.ordered.set :as oset]
                    [tupelo.types :as types]))
  #?(:clj (:import [java.io BufferedReader ByteArrayOutputStream PrintStream StringReader OutputStream]
                   [java.nio ByteBuffer])))

;---------------------------------------------------------------------------------------------------
; #todo include this stuff:
;   git@github.com:r0man/noencore.git - noencore/src/no/en/core.cljc

; #todo need (defkw :fred) and (kw :fred) to catch errors like
; (when (= person :frid)  ; (kw :frid) -> throws
;    (println "Hi Barney!"))

; WARNING:  cannot use Plumatic schema for functions that may receive an infinite lazy sequence
; as input.  See:  https://groups.google.com/forum/#!topic/clojure/oM1PH4sXzoA

; #todo replace clojure.core/map => tupelo.lazy/map if (t/refer-tupelo :strict)
; #todo replace clojure.core/map : not lazy; can add one of :trunc or :lazy modifiers
;   Use (map* {:trunc false :lazy false} ...)
;   Use (zip* {:trunc true  :lazy true } ...)

; #todo [tupelo.lazy :as z]
;   #todo (z/map ...)
;   #todo (z/filter ...)
;   #todo (z/map-indexed ...)
;   #todo (z/mapcat ...)
;   #todo (z/for ...)
;   #todo (z/concat ...)
;   #todo (z/zip ...)

;-----------------------------------------------------------------------------
; #todo maybe unify update & set for all state types:
;   atom-set       /  atom-update
;    ref-set       /   ref-update
;    var-set       /   var-update
;  agent-set       / agent-update
;   atom-set-both  /  atom-update-both  ; to return [old new] vector
;   xxxx-reset     /  xxxx-alter        ; other names
;   atom-set-old   /  atom-update-old   ; to return old value, not new

; #todo unify terminolgy (atom/ref/agent)
;   -> reset!/ref-set => set
;   -> swap!/alter => update

;-----------------------------------------------------------------------------
;                                               "1234.4567.89ab.cdef"  also valid for read
; #todo need conversion from Long -> hex string="1234-4567-89ab-cdef" (& inverse)
; #todo need rand-id/randid/rid/rid-str (rand id) -> 64 bit hex string="1234-4567-89ab-cdef"
; i[12] = Random.nextInt(); bytes += i[12].toHexString()

; #todo fix usage docs

;---------------------------------------------------------------------------------------------------
; #todo make sure works with cljdoc

; #todo wrap = < <= et al to throw ArityException if only 1 arg
; #todo or if not number?
; #todo wrap contains? get etc to enforce "normal" input types: map/set vs vec/list
; #todo contains-key? for map/set, contains-val? for map/set/vec/list (disable contains? for strict) (use .contains for -val)
; #todo (fnil inc 0) => (with-default-args [0 "hello" :cc]
; #todo                   some-fn-of-3-or-more-args)
; #todo    like (some-fn* (glue {0 0   1 "hello"   2 :cc} {<user args here>} ))

(defn cljs-env?     ; from plumatic schema/macros.clj
  "Given the &env from a macro, and tell whether we are expanding into cljs."
  [env] (boolean (:ns env)))

(defmacro if-cljs   ; from plumatic schema/macros.clj
  "For use within macros. Return `then-form` if we are generating ClojureScript code,
   and `else-form` for Clojure code.
     (from https://groups.google.com/d/msg/clojurescript/iBY5HaQda4A/w1lAQi9_AwsJ)"
  [then-form else-form]
  (if (cljs-env? &env) then-form else-form))

(defn try-catchall-impl ; from plumatic schema/macros.clj
  "A cross-platform variant of try-catch that catches all exceptions.
   Does not (yet) support finally, and does not need or want an exception class."
  [forms]
  (let [try-body (butlast forms)
        [catch-op ex-symbol & catch-body] (last forms)]
    (assert (= catch-op 'catch))
    (assert (symbol? ex-symbol))
    `(tupelo.core/if-cljs
       (try ~@try-body (catch js/Object ~ex-symbol ~@catch-body))
       (try ~@try-body (catch Throwable ~ex-symbol ~@catch-body)))))

(defmacro try-catchall ; from plumatic schema/macros.clj
  "A cross-platform variant of try-catch that catches all exceptions.
   Does not (yet) support finally, and does not need or want an exception class."
  [& forms] (try-catchall-impl forms))

(defmacro with-exception-default
  "Evaluates body & returns its result.  In the event of an exception, default-val is returned
   instead of the exception."
  [default-val & forms] ; :default
  `(try-catchall
     ~@forms
     (catch e# ~default-val)))

(defmacro with-result
  "Evaluates `result` and returns it; also evaluates `forms` for their side-effects."
  [result & forms]
  `(let [result# ~result]
     (do ~@forms)
     result#))

(defn type-name-str
  "Returns the type/class name of a value as a string.  Works for both CLJ and CLJS."
  [arg] (tupelo.core.impl/type-name-str arg))

;-----------------------------------------------------------------------------
#?(:clj
   (do

     (defmacro with-system-err-str
       "Evaluates exprs in a context in which JVM System/err is bound to a fresh
       PrintStream.  Returns the string created by any nested printing calls."
       [& body]
       `(let [err-orig# System/err
              baos#     (ByteArrayOutputStream.)
              ps#       (PrintStream. baos#)]
          (try
            (System/setErr ps#)
            (do ~@body)
            (.close ps#)
            (.toString baos#) ; <= return value - finally is side-effect only!
            (finally
              (System/setErr err-orig#)))))

     (defmacro with-system-out-str
       "Evaluates exprs in a context in which JVM System/out is bound to a fresh
       PrintStream.  Returns the string created by any nested printing calls."
       [& body]
       `(let [out-orig# System/out
              baos#     (ByteArrayOutputStream.)
              ps#       (PrintStream. baos#)]
          (try
            (System/setOut ps#)
            (do ~@body)
            (.close ps#)
            (.toString baos#) ; <= return value - finally is side-effect only!
            (finally
              (System/setOut out-orig#)))))

     (defmacro discarding-out-str
       "Evaluates exprs in a context in which Clojure `*out*` is bound to a fresh PrintStream that is discarded."
       [& body]
       `(let [s# (new java.io.StringWriter)]
          (binding [*out* s#]
            ~@body)))

     (defmacro discarding-system-err
       "Evaluates exprs in a context in which JVM System/err is bound to a fresh PrintStream that is discarded."
       [& body]
       `(let [err-orig# System/err
              ps#       (PrintStream. (OutputStream/nullOutputStream))]
          (try
            (System/setErr ps#)
            (let [result# (do ~@body)]
              (.close ps#)
              result#) ; <= return value - finally is side-effect only!
            (finally
              (System/setErr err-orig#)))))

     (defmacro discarding-system-out
       "Evaluates exprs in a context in which JVM System/out is bound to a fresh PrintStream that is discarded."
       [& body]
       `(let [out-orig# System/out
              ps#       (PrintStream. (OutputStream/nullOutputStream))]
          (try
            (System/setOut ps#)
            (let [result# (do ~@body)]
              (.close ps#)
              result#) ; <= return value - finally is side-effect only!
            (finally
              (System/setOut out-orig#)))))

     (defn exception-message
       "Returns the message from an exception => (.getMessage exception)"
       [exception]
       (.getMessage exception))

     (defn exception-stacktrace
       "Returns the stacktrace from an exception "
       [exception]
       (with-system-err-str
         (.printStackTrace exception)))
     ))
;-----------------------------------------------------------------------------
(defn assert-info-impl
  [[pred-expr err-str info-expr]]
  `(when-not ~pred-expr
     (throw (ex-info ~err-str ~info-expr))))

(defmacro assert-info ; #todo keep or discard???  Needs CLJS macro support
  "Like `assert` but accepts a map like `ex-info`:

        (assert-info (sequential? listy)
          \"prepend: Sequential collection required, found=\"
          {:listy listy} )

   Implemented using `(throw (ex-info ...))` "
  [pred-expr err-str info-expr] (assert-info-impl [pred-expr err-str info-expr]))

;-----------------------------------------------------------------------------
(declare
  glue xfirst xrest append prepend grab fetch-in indexed validate
  walk-with-parents with-nil-default vals->map snip snip* map-let map-let*
  spy spyx spy-pretty spyx-pretty let-spy let-spy-pretty unlazy
  atom?
  )

;-----------------------------------------------------------------------------
(defn const->fn
  "Creates a function that always returns a constant. The returned fn will accept
  (& ignore) any number of args. Synonym for `clojure.core/constantly`."
  [val]
  (constantly val))

(def noop
  "A function that accepts any number of args, does nothing, and returns `nil`."
  (constantly nil))

(defn truthy?
  "Returns true if arg is logical true (neither nil nor false); otherwise returns false."
  [arg] (if arg true false))

(defn falsey?
  "Returns true if arg is logical false (either nil or false); otherwise returns false. Equivalent
   to (not (truthy? arg))."
  [arg] (if arg false true))

(defn listy?
  "Returns true if arg is a list or a seq, else false."
  [arg] (or (list? arg) (seq? arg)))

(def ->true
  "A function that accepts any number of args, does nothing, and returns `true`."
  (constantly true))
(def ->false
  "A function that accepts any number of args, does nothing, and returns `false`."
  (constantly false))
(def ->nil
  "A function that accepts any number of args, does nothing, and returns `nil`."
  (constantly nil))
(def ->zero
  "A function that accepts any number of args, does nothing, and returns the number zero."
  (constantly 0))
(def ->one
  "A function that accepts any number of args, does nothing, and returns the number one."
  (constantly 1))

(defn nl
  "Abbreviated name for `newline`.  Accepts varargs to be printed 1 per line after initial newline. "
  [& args]
  (newline)
  (doseq [arg args]
    (println arg)))

;-----------------------------------------------------------------------------
(s/defn int-pos? :- s/Bool
  "Returns true iff x is an integer and is positive"
  [arg] (and (int? arg) (pos? arg)))

(s/defn int-neg? :- s/Bool
  "Returns true iff x is an integer and is negative"
  [arg] (and (int? arg) (neg? arg)))

(s/defn int-nonneg? :- s/Bool
  "Returns true iff x is an integer and is not negative"
  [arg] (and (int? arg) (not (neg? arg))))

(s/defn int-nonpos? :- s/Bool
  "Returns true iff x is an integer and is not positive"
  [arg] (and (int? arg) (not (pos? arg))))

(s/defn nonneg? :- s/Bool
  "Returns true iff x is not negative"
  [arg] (not (neg? arg)))

(s/defn nonpos? :- s/Bool
  "Returns true iff x is not positive"
  [arg] (not (pos? arg)))

; #todo add not-zero?

;-----------------------------------------------------------------------------
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

(s/defn str->chars :- [s/Any] ;  #todo  make tighter
  "Converts a string to a vector of chars"
  [arg :- s/Str]
  (vec arg))

(defn int->kw [arg]
  (keyword (str arg)))

; #todo make coercing versions of these ->long
(s/defn ->kw :- s/Keyword
  "Coerce arg to a keyword"
  [arg :- (s/cond-pre s/Keyword s/Str s/Symbol s/Num #?(:clj Character))]
  (cond
    (keyword? arg) arg
    (symbol? arg) (sym->kw arg)
    (string? arg) (str->kw arg)
    (number? arg) (str->kw (str arg))
    #?@(:clj [(char? arg) (str->kw (str arg))])

    :else (throw (ex-info "bad arg" {:arg arg}))))

(s/defn ->str :- s/Str
  "Coerce arg to a string"
  [arg :- (s/cond-pre s/Keyword s/Str s/Symbol s/Num #?(:clj Character))]
  (cond
    (string? arg) arg
    (symbol? arg) (sym->str arg)
    (keyword? arg) (kw->str arg)
    (number? arg) (str arg)
    #?@(:clj [(char? arg) (str arg)])
    :else (throw (ex-info "bad arg" {:arg arg}))))

(s/defn ->sym :- s/Symbol
  "Coerce arg to a symbol"
  [arg :- (s/cond-pre s/Keyword s/Str s/Symbol #?(:clj Character))]
  (cond
    (symbol? arg) arg
    (keyword? arg) (kw->sym arg)
    (string? arg) (str->sym arg)
    #?@(:clj [(char? arg) (str->sym (str arg))])
    :else (throw (ex-info "bad arg" {:arg arg}))))

(s/defn codepoint->char :- s/Any ; #todo need clj/cljs char? test
  "Convert a unicode int to a char"
  [arg :- s/Int]
  (assert (int? arg))
  #?(:clj  (char arg)
     :cljs (.fromCharCode js/String arg))) ; #todo just use cljs.core/char  ???

(s/defn char->codepoint :- s/Int
  "Convert a char to an unicode int"
  [arg :- s/Any]    ; #todo need clj/cljs char? test
  (assert (char? arg))
  #?(:clj  (int arg)
     :cljs (.charCodeAt arg 0)))

(defn kw->int [arg]
  #?(:clj  (Integer/parseInt (kw->str arg))
     :cljs (js/parseInt (kw->str arg) 10)))

; #todo add edn->js
; #todo add js->edn (:keywordize-keys true)
#?(:clj  (do
           ; #todo add test & README
           (s/defn json->edn
             "Shortcut to clojure.data.json/read-str (keywordizing keys)"
             [json-str :- s/Str]
             (unlazy (json/read-str json-str :key-fn keyword)))

           ; #todo add test & README
           (s/defn edn->json :- s/Str
             "Shortcut to clojure.data.json/write-string"
             [arg]
             (json/write-str arg)))
   :cljs (do
           ; #todo add test & README
           (s/defn json->edn
             "Convert from json -> edn"
             [json-str :- s/Str]
             (unlazy (js->clj (.parse js/JSON json-str) :keywordize-keys true))) ; true => keywordize-keys

           ; #todo add test & README
           (s/defn edn->json :- s/Str
             "Convert from edn -> json "
             [arg]
             (.stringify js/JSON (clj->js arg)))))

#?(:clj
   (do
     (s/defn sym->var :- clojure.lang.Var
       "Given a fully-qualified Clojure symbol, returns the corresponding clojure.lang.Var object."
       [var-sym :- s/Symbol]
       (eval `(var ~var-sym)))

     (s/defn str->var :- clojure.lang.Var
       "Given a Java string representing a fully-qualified Clojure symbol,
       returns the corresponding clojure.lang.Var object."
       [var-str :- s/Str]
       (-> var-str (str->sym) (sym->var)))
     ))

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
  (not (cc/empty? coll)))

; #todo -> README
(s/defn has-some? :- s/Bool ; #todo rename to has-any?   Add warning re new clj/any?
  "For any predicate pred & collection coll, returns true if (pred x) is logical true for at least one x in
   coll; otherwise returns false.  Like clojure.core/some, but returns only true or false."
  [pred :- s/Any
   coll :- [s/Any]]
  (truthy? (some pred coll)))
; NOTE: was `any?` prior to new `clojure.core/any?` added in clojure 1.9.0-alpha10

; #todo -> README
(s/defn has-none? :- s/Bool
  "For any predicate pred & collection coll, returns false if (pred x) is logical true for at least one x in
   coll; otherwise returns true.  Equivalent to clojure.core/not-any?, but inverse of has-some?."
  [pred :- s/Any
   coll :- [s/Any]]
  (falsey? (some pred coll))) ; #todo -> (not (has-some? pred coll))

(s/defn contains-elem? :- s/Bool
  "For any collection coll & element tgt, returns true if coll contains at least one
  instance of tgt; otherwise returns false. Note that, for maps, each element is a
  vector (i.e MapEntry) of the form [key value]."
  [coll :- s/Any
   elem :- s/Any]
  (has-some? truthy?
             (mapv #(= elem %) (seq coll))))

(s/defn contains-key? :- s/Bool
  "For any map or set, returns true if elem is a map key or set element, respectively"
  [map-or-set :- (s/pred #(or (map? %) (set? %)))
   elem :- s/Any]
  (contains? map-or-set elem))

(s/defn contains-val? :- s/Bool
  "For any map, returns true if elem is present in the map for at least one key."
  [map :- tsk/Map
   elem :- s/Any]
  (has-some? truthy?
             (mapv #(= elem %) (vals map))))

(s/defn dissoc-in :- s/Any ; #todo upgrade tupelo.core
  "A sane version of dissoc-in that will not delete intermediate keys.
   When invoked as

        (dissoc-in the-map [:k1 :k2 :k3... :kZ])

   acts like

        (clojure.core/update-in the-map [:k1 :k2 :k3...] dissoc :kZ)

   That is, only the map entry containing the last key `:kZ` is removed, and all map entries
   higher than `:kZ` in the hierarchy are unaffected."
  [the-map :- tsk/Map
   keys-vec :- [s/Any]] ; #todo  Primitive?
  (let [num-keys     (count keys-vec)
        key-to-clear (last keys-vec)
        parent-keys  (butlast keys-vec)]
    (cond
      (zero? num-keys) the-map
      (= 1 num-keys) (dissoc the-map key-to-clear)
      :else (update-in the-map parent-keys dissoc key-to-clear))))

;(defn case
;  [& args]
;  (throw (ex-info "`case` is evil, use `cond` instead" {:args args} )))

; #todo maybe add coerce->set, coerce->vec, coerce->list, coerce->map to accept nil (& others?)
(s/defn ->set :- tsk/Set
  "Converts arg to a set."
  [arg]
  (when-not (or (nil? arg) (set? arg) (sequential? arg))
    (throw (ex-info "invalid arg" {:arg arg})))
  (cc/set arg))

(s/defn ->sorted-set :- tsk/Set
  "Coerces a set into a sorted-set"
  [set-in :- tsk/Set] (glue (sorted-set) set-in))

(s/defn ->sorted-map :- tsk/Map
  "Coerces a map into a sorted-map"
  [map-in :- tsk/Map] (glue (sorted-map) map-in))

(defn sorted-map-generic
  "Returns a generic sorted map, able to accept keys of different classes"
  [] (sorted-map-by lex/compare-generic))

(s/defn ->sorted-map-generic :- tsk/Map
  "Coerces a map into a sorted-map"
  [map-in :- tsk/Map] (glue (sorted-map-generic) map-in))

(defn sorted-set-generic
  "Returns a generic sorted set, able to accept keys of different classes"
  [] (sorted-set-by lex/compare-generic))

(s/defn ->sorted-set-generic :- tsk/Set
  "Coerces a set into a sorted-set-generic"
  [set-in :- tsk/Set] (glue (sorted-set-generic) set-in))

(defn walk-data->pretty
  "Recursively walks a data structure, converting all maps & sets to (generic) sorted versions,
   and all sequences to vectors. "
  [data]
  (let [pretty-item (fn pretty-item-fn
                      [item]
                      ;(spyx :awt--607 (type item))
                      ;(spyx :awt--607 (class item))
                      (cond
                        (sequential? item) (vec item)

                        #?@(:clj  [(map? item) (into (sorted-map-generic) item)
                                   (set? item) (into (sorted-set-generic) item)

                                   ;(comment ; #todo #awt 22-7-05 fix this!
                                   ;  (atom? item) item
                                   ;  (= datomic.db.Datum (type item)) item
                                   ;  )
                                   ]
                            :cljs [(map? item) (into (sorted-map) item) ; #todo => (sorted-map-generic)
                                   (set? item) (into (sorted-set) item) ; #todo => (sorted-map-generic)
                                   ])

                        :else item))
        result      (walk/postwalk pretty-item data)]
    result))

(defn unlazy        ; #todo need tests & docs. Use for datomic Entity?
  "Converts a lazy collection to a concrete (eager) collection of the same type."
  [coll]
  (let [unlazy-item (fn unlazy-item-fn
                      [item]
                      ;(newline)
                      ;(prn :awt--unlazy-item-fn---------------------------------------------------------------------------)
                      ;(prn "(type item) => " (type item))
                      ;(prn "item => " item)
                      (with-exception-default item
                        (cond
                          (sequential? item) (vec item)
                          (map? item) (into {} item)
                          (set? item) (into #{} item)

                          #?@(:clj [
                                    (instance? java.io.InputStream item) (slurp item) ; #todo need test
                                    (instance? java.util.List item) (vec item) ; #todo need test
                                    (instance? java.util.Map item) (into {} item) ; #todo need test
                                    (instance? java.util.Set item) (into #{} item) ; #todo need test
                                    (instance? java.lang.Iterable item) (into [] item) ; #todo need test
                                    (= "datomic.query.EntityMap" (type-name-str item)) (into {} item) ; type-free test (doesn't need datomic)
                                    ])
                          :else item)))
        result      (walk/prewalk unlazy-item coll)]
    result))

(defn unlazy-pretty
  "Shorthand for (walk-data->pretty (unlazy data))."
  [data]
  #?(:clj  (try
             (walk-data->pretty (unlazy data))
             (catch Throwable t
               (prn :*****************************************************************************)
               (prn :**********--error--**********--tupelo.core/unlazy-pretty--Throwable--********)
               (prn :*****************************************************************************)
               (.printStackTrace t)
               data))
     :cljs (walk-data->pretty (unlazy data))
     ))

; #todo impl-merge *****************************************************************************

(defn has-length?   ; #todo rework => (count= N coll)  ???
  "Returns true if the collection has the indicated length. Does not hang for infinite sequences."
  [coll n]
  (assert-info (not-nil? coll) "has-length?: coll must not be nil" {:coll coll})
  (let [take-items (cc/take n coll)
        rest-items (cc/drop n coll)]
    (and (= n (count take-items))
         (empty? rest-items))))

(defn only
  "Ensures that a sequence is of length=1, and returns the only value present.
  Throws an exception if the length of the sequence is not one.
  Note that, for a length-1 sequence S, (first S), (last S) and (only S) are equivalent."
  [coll]
  (assert-info (has-length? coll 1) "only: num-items must=1" {:coll coll})
  (clojure.core/first coll))

(defn onlies
  "Given an outer collection of length-1 collections, returns a sequence of the unwrapped values.

        (onlies  [ [1] [2] [3] ])  =>  [1 2 3]
        (onlies #{ [1] [2] [3] })  => #{1 2 3}
        "
  [coll] (into (unlazy (empty coll)) (mapv only coll)))

(defn only2
  "Given a collection like `[[5]]`, returns `5`.  Equivalent to `(only (only coll))`."
  [coll] (only (only coll)))

(s/defn only? :- s/Bool
  "Returns true iff collection has length=1"
  [coll :- s/Any] (and (has-length? coll 1)))
(s/defn only2? :- s/Bool
  "Returns true iff arg is two nested collections of length=1 (eg `[[5]]`)"
  [coll :- s/Any] (and (has-length? coll 1)
                       (has-length? (first coll) 1)))

(defn single?
  "Returns true if the collection contains a single item.`"
  [coll] (and (sequential? coll) (has-length? coll 1)))

(defn pair?
  "Returns true if the collection contains exactly 2 items."
  [coll] (and (sequential? coll) (has-length? coll 2)))

(defn triple?
  "Returns true if the collection contains exactly 3 items."
  [coll] (and (sequential? coll) (has-length? coll 3)))

(defn quad?
  "Returns true if the collection contains exactly 4 items."
  [coll] (and (sequential? coll) (has-length? coll 4)))

(defn first-or-nil
  "Returns the first item in a sequence, or nil"
  [seq-arg]
  (clojure.core/first seq-arg))

(defn second-or-nil
  "Returns the second item in a sequence, or nil"
  [seq-arg]
  (clojure.core/first (drop 1 seq-arg)))

(defn third-or-nil
  "Returns the third item in a sequence, or nil"
  [seq-arg]
  (clojure.core/first (drop 2 seq-arg)))

(defn fourth-or-nil
  "Returns the fourth item in a sequence, or nil"
  [seq-arg]
  (clojure.core/first (drop 3 seq-arg)))

(defn last-or-nil
  "Returns the last item in a sequence, or nil"
  [seq-arg]
  (first-or-nil (reverse seq-arg)))

(defn rest-or-empty
  "Returns a sequence with the first item removed, or a zero-length seq if there are no more items"
  [seq-arg]
  (rest seq-arg))

(defn rest-or-nil
  "Returns a sequence with the first item removed, or nil if there are no more items"
  [seq-arg]
  (next seq-arg))

(defn get-or-nil
  [mappy key] (clojure.core/get mappy key))

(defn get-or-default
  [mappy key default] (clojure.core/get mappy key default))

; NOTE:  Plumatic Schema doesn't handle infininite sequences
(defn xtake         ;  :- tsk/Collection
  "Returns the first n values from a collection.  Returns map for map colls.
  Throws if empty."
  [n                ; :- s/Num
   coll             ; :- tsk/Collection
   ]
  (assert (number? n))
  (assert (or (sequential? coll) (map? coll) (set? coll)))
  (assert-info (and (not-nil? coll) (not-empty? coll))
               "xtake: invalid coll: " {:coll coll})
  (let [items  (cc/take n coll)
        actual (count items)]
    (when (< actual n)
      (throw (ex-info "xtake: insufficient items" {:n n :actual actual})))
    (cond
      (sequential? coll) (vec items)
      (map? coll) (into {} items)
      (set? coll) (into #{} items)
      :else (throw (ex-info "Invalid collection type" {:coll coll})))))

(s/defn xdrop :- tsk/Collection
  "Returns a collection as a vector with the first n values removed.    Returns map for map colls.
  Throws if empty."
  [n :- s/Num
   coll :- tsk/Collection]
  (assert (number? n))
  (assert (or (sequential? coll) (map? coll) (set? coll)))
  (assert-info (and (not-nil? coll) (not-empty? coll))
               "xdrop: invalid coll: " {:coll coll})
  (let [taken     (cc/take n coll)
        taken-cnt (count taken)
        remaining (cc/drop n coll)]
    (assert-info (= taken-cnt n) "xdrop: insufficient taken" {:n n :actual taken-cnt})
    (cond
      (sequential? coll) (vec remaining)
      (map? coll) (into {} remaining)
      (set? coll) (into #{} remaining)
      :else (throw (ex-info "Invalid collection type" {:coll coll})))))

(defn xfirst        ; #todo -> tests
  "Returns the first value in a list or vector. Throws if empty."
  [coll]
  (assert-info (and (not-nil? coll) (not-empty? coll))
               "xfirst: invalid coll: " {:coll coll})
  (nth coll 0))

; #todo fix up for maps
; #todo (it-> coll (take 2 it), (validate (= 2 (count it))), (last it))
(defn xsecond       ; #todo -> tests
  "Returns the second value in a list or vector. Throws if (< len 2)."
  [coll]
  (assert-info (and (not-nil? coll) (not-empty? coll))
               "xsecond: invalid coll: " {:coll coll})
  (nth coll 1))

; #todo fix up for maps
(defn xthird        ; #todo -> tests
  "Returns the third value in a list or vector. Throws if (< len 3)."
  [coll]
  (assert-info (and (not-nil? coll) (not-empty? coll)) "xthird: invalid coll: " {:coll coll})
  (nth coll 2))

; #todo fix up for maps
(defn xfourth       ; #todo -> tests
  "Returns the fourth value in a list or vector. Throws if (< len 4)."
  [coll]
  (assert-info (and (not-nil? coll) (not-empty? coll)) "xfourth: invalid coll: " {:coll coll})
  (nth coll 3))

; #todo fix up for maps
(s/defn xlast :- s/Any ; #todo -> tests
  "Returns the last value in a list or vector. Throws if empty."
  [coll :- [s/Any]]
  (assert-info (and (not-nil? coll) (not-empty? coll)) "xlast: invalid coll: " {:coll coll})
  (clojure.core/last coll))

; #todo fix up for maps
(s/defn xbutlast :- s/Any ; #todo -> tests
  "Returns a vector of all but the last value in a list or vector. Throws if empty."
  [coll :- [s/Any]]
  (assert-info (and (not-nil? coll) (not-empty? coll)) "xbutlast: invalid coll: " {:coll coll})
  (vec (clojure.core/butlast coll)))

; #todo need xnext

; #todo fix up for maps
(defn xrest         ; #todo -> tests
  "Returns the last value in a list or vector. Throws if empty."
  [coll]
  (assert-info (and (not-nil? coll) (not-empty? coll)) "xrest: invalid coll: " {:coll coll})
  (clojure.core/rest coll))

(defn xreverse      ; #todo -> tests & doc
  "Returns a vector containing a sequence in reversed order. Throws if nil."
  [coll]
  (assert-info (not-nil? coll) "xreverse: invalid coll: " {:coll coll})
  (vec (clojure.core/reverse coll)))

(s/defn xvec :- [s/Any]
  "Converts a collection into a vector. Throws if given nil."
  [coll :- [s/Any]]
  (assert-info (not-nil? coll) "xvec: invalid coll: " {:coll coll})
  (clojure.core/vec coll))

(s/defn ->list :- [s/Any]
  "Coerce any sequential argument into a List."
  [arg :- [s/Any]]
  (apply list arg))

(s/defn xsequential? :- s/Bool
  "Like clojure.core/sequential? EXCEPT returns false for clojure.lang.MapEntry"
  [coll]
  (and (sequential? coll)
       (not (map-entry? coll))))

(s/defn xmap? :- s/Bool
  "Like clojure.core/map?, but returns false for records."
  [arg :- s/Any]
  (and (map? arg) (not (record? arg))))

(defmacro forv      ; #todo rename for-vec ???
  "Like clojure.core/for but returns results in a vector.
  Wraps the loop body in a `do` as with `doseq`. Not lazy."
  [& forms]
  (let [bindings-vec (xfirst forms)
        body-forms   (xrest forms)]
    `(vec (for ~bindings-vec
            (do ~@body-forms)))))

(defmacro for-list  ; #todo test
  "Like clojure.core/for but returns results in an eager list.
  Wraps the loop body in a `do` as with `doseq`. Not lazy."
  [& forms]
  (let [bindings-vec (xfirst forms)
        body-forms   (xrest forms)]
    `(->list (for ~bindings-vec
               (do ~@body-forms)))))

(defmacro map-list  ; #todo test
  "Like clojure.core/map but returns results in an eager list. Not lazy."
  [& forms]
  `(->list (map ~@forms)))

(defn ^:no-doc for-indexed-impl
  [forms]
  (let
    [bindings-vec (xfirst forms)
     body-forms   (xrest forms)
     >>           (assert-info (= 2 (count bindings-vec))
                               "for-indexed: binding form must be len=2 " (vals->map bindings-vec))
     bndg-dest    (xfirst bindings-vec)
     bndg-src     (xsecond bindings-vec)]
    `(vec
       (for [~bndg-dest (indexed ~bndg-src)]
         (do ~@body-forms)))))

(defmacro for-indexed
  "Like clojure.core/map-indexed, converts each element x in a sequence into a Pair [i x],
  where `i` is the zero-based index number. Supports only a single sequence in the binding form.
  Wraps all forms with an implicit `(do ...)` as with clojure.core/doseq.  Use `tupelo.core/indexed`
  for more complicated looping constructs. Usage:

        (for-indexed [[i x] vals]
          (println (format \"i=%d x=%s\" i x))
          {:i i :x x} )

  is equivalent to:

      (vec
        (for [[i x] (indexed vals)]
          (do
            (println (format \"i=%d x=%s\" i x))
            {:i i :x x} )))  "
  [& forms]
  (for-indexed-impl forms))

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
    :else (throw (ex-info "keep-if: coll must be sequential, map, or set." {:coll coll}))))

(defn drop-if
  "Returns a vector of items in coll for which (pred item) is false (alias for clojure.core/remove)"
  [pred coll]
  (keep-if (complement pred) coll))

(s/defn append :- tsk/List
  "Given a sequential object (vector or list), add one or more elements to the end."
  [listy :- tsk/List
   & elems :- [s/Any]]
  (assert-info (sequential? listy) "append: Sequential collection required, found=" {:listy listy})
  (assert-info (not-empty? elems) "Nothing to append! elems=" {:elems elems})
  ; (vec (concat listy elems))  ; #TODO ***WARNING*** never use `concat`!!! 1000x slower!
  (into (vec listy) elems)) ; #todo measure & write blog re TPX/TigerGraph data

(s/defn prepend :- tsk/List
  "Given a sequential object (vector or list), add one or more elements to the beginning"
  [& args]
  (let [elems (butlast args)
        listy (xlast args)]
    (assert-info (sequential? listy) "prepend: Sequential collection required, found=" {:listy listy})
    (assert-info (not-empty? elems) "Nothing to prepend! elems=" {:elems elems})
    (into (vec elems) listy)))

;-----------------------------------------------------------------------------
; spy stuff

; #todo defn-spy  saves fn name to locals for spy printout
; #todo spyxl  adds file/line to spy printout

; (def ^:dynamic *spy-enabled* false)
(def ^:dynamic *spy-enabled* true) ; #TODO fix before commit!!!

(def ^:dynamic *spy-enabled-map* {})

(defmacro with-spy-enabled ; #todo README & test
  [tag              ; :- s/Keyword #todo schema for macros?
   & forms]
  `(binding [*spy-enabled-map* (assoc *spy-enabled-map* ~tag true)]
     ~@forms))

(defmacro check-spy-enabled ; #todo README & test
  [tag              ; :- s/Keyword #todo schema for macros?
   & forms]
  `(binding [*spy-enabled* (get *spy-enabled-map* ~tag false)]
     ~@forms))

(def ^:no-doc spy-indent-level (atom 0))

(defn ^:no-doc spy-indent-spaces []
  (str/join (repeat (* 2 @spy-indent-level) \space)))

(defn ^:no-doc spy-indent-inc
  "Increase the spy indent level by one."
  []
  (swap! spy-indent-level inc))

(defn ^:no-doc spy-indent-dec
  "Decrease the spy indent level by one."
  []
  (swap! spy-indent-level dec))

(defn spy-indent-reset
  "Reset the spy indent level to zero."
  []
  (reset! spy-indent-level 0))

;-----------------------------------------------------------------------------
(defn ^:no-doc spy2-impl ; 2-arg arity requires user-supplied keyword
  [arg1 arg2]
  (let [[tag value] (cond
                      (keyword? arg1) [arg1 arg2]
                      (keyword? arg2) [arg2 arg1]
                      :else (throw (ex-info "spy: either first or 2nd arg must be a keyword tag \n   args:"
                                            {:arg1 arg1
                                             :arg2 arg2})))]
    (when *spy-enabled*
      (println (str (spy-indent-spaces) tag " => " (pr-str value))))
    value))

(defmacro spy       ; #todo clean up all spy stuff
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
  ; 1-arg arity uses a generic "spy" message
  ([value]
   (let [src-line   (:line (meta &form))
         src-ns-str (str (ns-name *ns*))
         out-tag    (keyword (format "spy--%s--line-%03d" src-ns-str src-line))]
     `(let [result# ~value]
        (println ~out-tag "=>" (pr-str result#))
        result#)))
  ([arg1 arg2]
   `(spy2-impl ~arg1 ~arg2)))

(comment
  (defn spy
    ; 1-arg arity uses a generic "spy" message
    ([value]
     (let [src-line   (:line (meta &form))
           src-ns-str (str (ns-name *ns*))
           out-tag    (keyword (format "spy--%s--line-%03d" src-ns-str src-line))]
       (spy ~out-tag ~value)))
    ; 2-arg arity requires user-supplied keyword
    ([arg1 arg2]
     (let [[tag value] (cond
                         (keyword? arg1) [arg1 arg2]
                         (keyword? arg2) [arg2 arg1]
                         :else (throw (ex-info "spy: either first or 2nd arg must be a keyword tag \n   args:"
                                               {:arg1 arg1
                                                :arg2 arg2})))]
       (when *spy-enabled*
         (println (str (spy-indent-spaces) tag " => " (pr-str value))))
       value))
    ))



(defn ^:no-doc spyx-impl
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
        final-code `(do ~@r1 ~r2)]
    final-code))

; #todo allow spyx to have labels like (spyx :dbg-120 (+ 1 2)):  ":dbg-120 (+ 1 2) => 3"
(defmacro spyx
  "An expression (println ...) for use in threading forms (& elsewhere). Evaluates the supplied
   expressions, printing both the expression and its value to stdout. Returns the value of the
   last expression."
  [& exprs]
  (spyx-impl exprs))

; #todo fix so works right with TagVal like `spyx` => <:idx 2> (not map format)
(defn ^:no-doc spy-pretty-impl
  [exprs]
  (let [r1         (for [expr (butlast exprs)]
                     `(when *spy-enabled* (println (spy-indent-spaces) (str ~expr " => "))))
        r2         (let [expr (xlast exprs)]
                     `(let [spy-val# ~expr]
                        (when *spy-enabled*
                          (println (impl/indent-lines-with (spy-indent-spaces)
                                                           (pretty-str spy-val#))))
                        spy-val#))
        final-code `(do
                      ~@r1
                      ~r2)]
    final-code))

; #todo (spyl value) prints:   spy-line-xxxx => value
(defn spyq          ; #todo => tupelo.core/spy
  "(spyq <value>) - Spy Quiet
        This variant is intended for use in very simple situations and is the same as the
        2-argument arity where <msg-string> defaults to 'spy'.  For example (spy (+ 2 3))
        prints 'spy => 5' to stdout.  "
  [value]
  (when *spy-enabled*
    (println (str (spy-indent-spaces) (pr-str value))))
  value)

(defn spydiv [] (spyq :-----------------------------------------------------------------------------))

; #todo only allow 1 arg + optional kw-label
(defmacro spy-pretty ; #todo => core
  "Like `spyx-pretty` but without printing the original form"
  [& exprs]
  (spy-pretty-impl exprs)) ; #todo add in use of `prettify` for each value

(defn ^:no-doc spyx-pretty-impl
  [exprs]
  (let [r1         (for [expr (butlast exprs)]
                     (if (keyword? expr)
                       `(when *spy-enabled* (println (spy-indent-spaces) (str ~expr)))
                       `(when *spy-enabled* (println (spy-indent-spaces) (str '~expr " => " ~expr)))))
        r2         (let [expr (xlast exprs)]
                     `(let [spy-val# ~expr]
                        (when *spy-enabled*
                          (println (str (spy-indent-spaces) '~expr " => "))
                          (println (impl/indent-lines-with (spy-indent-spaces)
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
  (spyx-pretty-impl exprs)) ; #todo add in use of `prettify` for each value

(defmacro with-spy-indent
  "Increments indentation level of all spy, spyx, or spyxx expressions within the body."
  [& forms]
  `(try
     (spy-indent-inc)
     (do ~@forms)
     (finally       ; ensure we un-do indentation in event of exception
       (spy-indent-dec))))

(defmacro with-debug-tag
  [debug-tag & forms]
  `(with-spy-indent
     (let [tag-enter# ~(str debug-tag "-enter")
           tag-leave# ~(str debug-tag "-leave")]
       (try
         (println (impl/indent-lines-with (spy-indent-spaces) tag-enter#))
         ~@forms
         (finally
           (println (impl/indent-lines-with (spy-indent-spaces) tag-leave#)))))))

; #todo: for all let-spy*:  if symbol is '>>' or '<>", skip display
(defmacro let-spy
  "An expression (println ...) for use in threading forms (& elsewhere). Evaluates the supplied
   expressions, printing both the expression and its value to stdout. Returns the value of the
   last expression."
  [& exprs]
  (let [decls      (xfirst exprs)
        _          (assert-info (even? (count decls)) "spy-let-proc: uneven number of decls:" {:decls decls})
        forms      (xrest exprs)
        fmt-pair   (fn [[dest src]]
                     [dest src
                      '_ (list `spyx dest)]) ; #todo gensym instead of underscore?
        pairs      (vec (partition 2 decls))
        r1         (vec (mapcat fmt-pair pairs))
        final-code `(let ~r1 ~@forms)]
    final-code))

(defmacro let-spy-pretty ; #todo -> deprecated
  "An expression (println ...) for use in threading forms (& elsewhere). Evaluates the supplied
   expressions, printing both the expression and its value to stdout. Returns the value of the
   last expression."
  [& exprs]
  (let [decls      (xfirst exprs)
        _          (assert-info (even? (count decls)) "spy-let-pretty-impl: uneven number of decls:" {:decls decls})
        forms      (xrest exprs)
        fmt-pair   (fn [[dest src]]
                     [dest src
                      '_ (list `spyx-pretty dest)]) ; #todo gensym instead of underscore?
        pairs      (vec (partition 2 decls))
        r1         (vec (mapcat fmt-pair pairs))
        final-code `(let ~r1 ~@forms)]
    final-code))

(defmacro spyxx
  "An expression (println ...) for use in threading forms (& elsewhere). Evaluates the supplied
   expression, printing both the expression, its type, and its value to stdout, then returns the value."
  [expr]
  `(let [spy-val#   ~expr
         type-name# (type-name-str spy-val#)]
     (when *spy-enabled*
       (println (str (spy-indent-spaces) '~expr " => <#" type-name# " " (pr-str spy-val#) ">")))
     spy-val#))

(defmacro let-spyxx
  "An expression (println ...) for use in threading forms (& elsewhere). Evaluates the supplied
   expressions, printing both the expression and its value to stdout. Returns the value of the
   last expression."
  [& exprs]
  (let [decls      (xfirst exprs)
        _          (assert-info (even? (count decls)) "spy-let-proc: uneven number of decls:" {:decls decls})
        forms      (xrest exprs)
        fmt-pair   (fn [[dest src]]
                     [dest src
                      '_ (list `spyxx dest)]) ; #todo gensym instead of underscore?
        pairs      (vec (partition 2 decls))
        r1         (vec (mapcat fmt-pair pairs))
        final-code `(let ~r1 ~@forms)]
    final-code))

;-----------------------------------------------------------------------------
(defn native-array?
  "Returns true iff arg is a native Java or JavaScript array."
  [arg] (impl/native-array? arg))

(defn ^:no-doc glue-byte-arrays
  "Glues together N byte arrays."
  [& byte-arrays]
  #?(:clj  (let [total-len   (apply + 0 (mapv count byte-arrays))
                 byte-buffer (ByteBuffer/allocate total-len)]
             (doseq [byte-array-curr byte-arrays]
               (.put byte-buffer byte-array-curr))
             (.array byte-buffer))
     :cljs (throw (ex-info "glue-byte-arrays: unimplemented on CLJS" {}))))

(comment            ; #todo add this?
  ; latest comment under above gist provides another
  ; simpler and more consistent version of deep-merge
  ; Source: https://gist.github.com/danielpcox/c70a8aa2c36766200a95#gistcomment-2759497
  (defn deep-merge [a & maps]
    (if (map? a)
      (apply merge-with deep-merge a maps)
      (apply merge-with deep-merge maps)))

  (deep-merge {:a {:b true}} {:a {:b false}} {:a {:b nil}})
  ; => {:a {:b nil}}

  (deep-merge {:a 1} nil)
  ; => {:a 1}
  )

(s/defn map-entry :- tsk/MapEntry
  "Returns a clojure.lang.MapEntry constructed from the given key and val"
  [key val]
  #?(:clj  (clojure.lang.MapEntry/create key val)
     :cljs (first {key val}))) ; #todo is this really used?  Maybe use 2-vector?

(defn list-entry
  "Constructs a list-entry map given an index and value"
  [idx val]
  (assert (int-nonneg? idx))
  {:type :list-entry :idx idx :val val})

(defn list-entry?
  "Returns true iff the arg is a list-entry"
  [arg] (and (map? arg)
             (= :list-entry (:type arg))))

(s/defn list->entries :- [tsk/Map]
  "Returns a vector of list-entry maps given a vector/list"
  [data :- tsk/Vec]
  (forv [[ii dd] (indexed data)]
    (list-entry ii dd)))

(s/defn list-entries->vec :- tsk/Vec ; #todo modify with :lax option & consolidate with lisit-entries-rerack
  [list-entries :- tsk/Vec]
  (doseq [item list-entries]
    (validate list-entry? item))
  (let [N    (count list-entries)
        idxs (mapv :idx list-entries)
        vals (mapv :val list-entries)]
    (assert (= idxs (range N)))
    vals))

(comment
  ; #todo => tupelo.core
  (s/defn mapentry->kv :- tsk/Pair ; #todo need test
    [mapentry :- tsk/MapEntry]
    [(key mapentry) (val mapentry)])

  ; #todo => tupelo.core
  (s/defn solomap->kv :- tsk/Pair ; #todo need test
    [solo-map :- tsk/Map]
    (let [map-seq (seq solo-map)
          >>      (assert-info (= 1 (count map-seq)) "solo-map must be of length=1 " (vals->map solo-map))]
      (mapentry->kv (only map-seq))))
  )

(s/defn ->map-entry :- tsk/MapEntry ; #todo need test
  "Coerce arg into a clojure.lang.MapEntry"
  [arg]
  (cond
    (map-entry? arg) arg
    (or (list? arg)
        (vector? arg)) (do
                         (assert-info (= 2 (count arg)) "map-entry must be of len=2" {:arg arg})
                         (map-entry (xfirst arg) (xsecond arg)))
    (map? arg) (let [arg-seq (seq arg)]
                 (assert-info #(= 1 (count arg-seq)) "map must be of len=1" {:arg arg})
                 (xfirst arg-seq))))

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
  [& colls]         ; #todo maybe return nil if no colls?  would allow some-> for users
  (let [string-or-char? #(or (string? %) (char? %))]
    (cond
      (every? #(or (map? %) ; NOTE: this must come first as MapEntry's pass `sequential?`
                   (map-entry? %)) colls) (let [mapentries (drop-if map? colls)
                                                maps       (keep-if map? colls)
                                                me-result  (reduce conj {} mapentries)
                                                result     (reduce into (append maps me-result))]
                                            result)
      (every? sequential? colls) (reduce into [] colls) ; coerce to vector result
      (every? set? colls) (reduce into colls) ; first item determines type of result
      (every? string-or-char? colls) (apply str colls)
      #?(:clj (every? types/byte-array? colls)) #?(:clj (apply glue-byte-arrays colls))

      :else (throw (ex-info "glue: colls must be all same type; found types=" (mapv type colls))))))

(defn glue-rows     ; #todo :- tsk/List ; #todo necessary?
  " Convert a vector of vectors (2-dimensional) into a single vector (1-dimensional).
  Equivalent to `(apply glue ...)`"
  [coll-2d          ; :- tsk/List
   ]
  (assert-info (sequential? coll-2d) "Sequential collection required, found=" coll-2d)
  (assert-info (every? sequential? coll-2d) "Nested sequential collections required, found=" coll-2d)
  (reduce into [] coll-2d))

; #todo rename to (map-of a b c ...)  ??? (re. potpuri)
(defmacro vals->map ; #todo -> README
  "Called with a list of symbols like `(vals->map a b c)` returns a map
   like {:a a :b b :c c}.

       (let [a 1
             b 2
             c 3]
         (vals->map a b c))  ;=>  {:a 1 :b 2 :c 3} }

   See `with-map-vals` for simple destructuring of such maps."
  [& symbols]
  (let [maps-list (for [symbol symbols]
                    {(keyword symbol) symbol})]
    `(glue ~@maps-list)))

(defn ^:no-doc vals->strmap-impl
  [symbols]
  (let [maps-list (for [symbol symbols]
                    {(->str symbol) (->sym symbol)})]
    `(glue ~@maps-list)))

(defmacro vals->strmap ; #todo -> README
  "Called with a list of symbols like `(vals->map a b c)` returns a map with string keys
   like {\"a\" a \"b\" b \"c\" c}.

       (let [a 1
             b 2
             c 3]
         (vals->map a b c))  ;=>  {\"a\" 1 \"b\" 2 \"c\" 3} }

   See `with-strmap-vals` for simple destructuring of such maps."
  [& args] (vals->strmap-impl args))

; #todo:  create with-map-vals-default
(comment
  (with-map-vals-default user-map {:name    "Unknown" ; <= all default vals & defines keys
                                   :address "n/a"}
                         (spyx address)
                         (isnt= "unknown" name)))

(defmacro with-map-vals ; #todo -> README
  "Given a map like {:a 1 :b 2 :c 3} (such as generated by `(vals->map a b c)`),
  performs safe `let` destructuring using `grab` like:

       (let [some-map  {:a 1 :b 2 :c 3} } ]
         (with-map-vals some-map [a b c]
            (+ a b c)))  ;=>  6

  `with-map-vals` is safe for typos since `grab` will throw if the requested key is not present in the map.
  See `vals->map` for simple creation of labeled data maps."
  [the-map items-vec & forms]
  `(do
     (let           ; generate the binding vector dynamically
       ~(apply glue
               (for [item items-vec
                     :let [sym (symbol (name item))
                           kw  (keyword item)]]
                 [sym (list `grab kw the-map)]))
       ~@forms)))

(defmacro with-strmap-vals ; #todo -> README
  "Given a map like {\"a\" 1 \"b\" 2 \"c\" 3} (such as generated by `(vals->strmap a b c)`),
  performs safe `let` destructuring using `grab` like:

       (let [some-map  {\"a\" 1 \"b\" 2 \"c\" 3} } ]
         (with-strmap-vals some-map [a b c]
            (+ a b c)))  ;=>  6

  `with-strmap-vals` is safe for typos since `grab` will throw if the requested key is not present in the map.
  See `vals->strmap` for simple creation of such maps."
  [the-map items-vec & forms]
  `(do
     (let           ; generate the binding vector dynamically
       ~(apply glue
               (for [item items-vec
                     :let [sym    (->sym item)
                           strkey (->str item)]]
                 [sym (list `tupelo.core/grab strkey the-map)]))
       ~@forms)))

(s/defn select-paths :- {tsk/Vec s/Any}
  "Like clojure.core/select-keys, but takes a sequence of datastructure paths as input:
      (let [m {:a 1
               :b {:c 2}
               :d [0 1 {:e 5}]}]
        (is= (t/select-paths m [[:a]
                                [:b :c]
                                [:d 2 :e]])
          {[:a]      1
           [:b :c]   2
           [:d 2 :e] 5}))
   See also `dissoc-paths` to remove unwanted sub-trees."
  [m :- tsk/Map
   paths :- [tsk/Vec]]
  (apply glue
         (forv [path paths]
           {path (fetch-in m path)})))

(s/defn dissoc-paths :- tsk/Map
  "Inverse of `select-paths`. removes subtrees of a data structure as specified by paths
  via successive calls to `tupelo.core/dissoc-in` "
  [m :- tsk/Map
   paths :- [tsk/Vec]]
  (reduce
    (fn [result path] (dissoc-in result path))
    m
    paths))

(defn ^:no-doc construct-impl ; #todo what is this???
  [template]
  ;(spyx template)
  ;(spy :impl-out)
  (walk-with-parents template
                     {:leave (fn [parents item]
                               (with-nil-default item
                                                 (when (= (->sym :?) item)
                                                   (let [ancestors  (vec (reverse parents))
                                                         -mv-ent-   (xfirst ancestors)
                                                         me         (xsecond ancestors)
                                                         me-key     (xfirst me)
                                                         me-key-sym (kw->sym me-key)]
                                                     me-key-sym))))}))
(defmacro construct
  [template] (construct-impl template))

;-----------------------------------------------------------------------------
#?(:clj
   (do

     (def ^:dynamic *dynamic-atom*
       "A dynamic Var pointing to an `atom`. Used by `with-cynamic-val` to accumulate state,
       such as in a vector or map.  Typically manipulated via helper functions such as
       `cum-val-set-it` or `cum-vector-append`. Can also be manipulated directly via `swap!` et al."
       nil)

     (defmacro with-mutable-var
       "Works with `(dynval-set-it ...)` to simulate a mutable variable.

             (is= 15 (with-mutable-var 9           ; <= initial value
                       (dynval-set-it! (+ it 1)    ; `it` refers to old value
                       (dynval-set-it! (+ it 2))   ; `it` refers to old value
                       (dynval-set-it! (+ it 3)))) ; `it` refers to old value

             (is= true (with-mutable-var false     ; <= initial value
                         (dynval-set-it! true)))   ; can ignore old value if desired
       "
       [init-val & forms]
       `(binding [tupelo.core/*dynamic-atom* (atom ~init-val)]
          (do ~@forms)
          (deref tupelo.core/*dynamic-atom*)))

     (defn ^:no-doc mutable-var-set-it-impl
       [forms]
       `(swap! *dynamic-atom*
               (fn [~'it] ~@forms)))

     (defmacro mutable-var-set-it!
       "Within `(with-dynamic-val ...)`, replaces value."
       [& forms]
       (mutable-var-set-it-impl forms))

     (defmacro with-cum-vector
       "Works with `(cum-vector-append ...)` to accumulate values into a vector.

             (is= [1 2 3]
               (with-cum-vector
                 (cum-vector-append! 1)
                 (cum-vector-append! 2)
                 (cum-vector-append! 3)))
       "
       [& forms]
       `(with-mutable-var []
                          ~@forms))

     (defn cum-vector-append! ; #todo file bug report for CLJS
       "Within `(with-cum-vector ...)`, appends a new value."
       [value]
       (mutable-var-set-it! (append it value)))

     ))
;-----------------------------------------------------------------------------
(defmacro source-code-env
  "A macro that returns information about the calling source code location like:
       {:src-line    61
        :src-col      9
        :src-ns-name 'tst.tupelo.core' } "
  []
  (let [src-line    (:line (meta &form))
        src-col     (:column (meta &form))
        src-ns-name (str (ns-name *ns*))]
    (vals->map src-line src-col src-ns-name)))

; #todo  Need it?-> like some-> that short-circuits on nil
(defmacro it->
  "A threading macro like as-> that always uses the symbol 'it' as the placeholder for the next threaded value:

        (it-> 1
              (inc it)
              (+ it 3)
              (/ 10 it))
        ;=> 2 "
  [expr & forms]
  `(let [~'it ~expr
         ~@(interleave (repeat 'it) forms)
         ]
     ~'it))

; #todo  Need it?-> like some-> that short-circuits on nil
(defn ^:no-doc spy-it->-impl
  [[expr & forms]]
  ; (spyx expr)   ; dbg
  ; (spyx forms)  ; dbg
  `(do
     (print "spy-it-> ") (prn ~expr)
     (let [~'it ~expr
           ~@(apply concat
                    (forv [form forms]
                      ; (spyx form)  ; dbg
                      ['it form
                       '>> `(println "  " (quote ~form) " => " (pr-str ~'it))]))
           ]
       ~'it)))
(defmacro spy-it->
  "Like it-> but prints the value at each stage of the pipeline"
  [& args] (spy-it->-impl args))

(defn ^:no-doc cond-it-impl
  [expr & forms]
  (let [num-forms (count forms)]
    (assert-info (even? num-forms) "num-forms must be even; value=" (vals->map num-forms forms)))
  (let [cond-action-pairs (partition 2 forms)
        cond-action-forms (for [[cond-form action-form] cond-action-pairs]
                            `(if ~cond-form
                               ~action-form
                               ~'it))]
    `(it-> ~expr ~@cond-action-forms)))

; #todo make look like this?
;(t/cond-it-> (parent-hid (hid->node hid))
;  {:when (or
;           (instance? MapEntryNode (hid->node it))
;           (instance? ArrayEntryNode (hid->node it)))
;   :then (parent-hid (hid->node it))})

(defmacro cond-it->
  "A threading macro like cond-> that always uses the symbol 'it' as the placeholder for the next threaded value.
  Works in both the conditional form and the value form:

      (let [params {:a 1 :b 1 :c nil :d nil}]
        (cond-it-> params
          (:a it)        (update it :b inc)
          (= (:b it) 2)  (assoc it :c \"here\")
          (:c it)        (assoc it :d \"again\")))

      ;=> {:a 1, :b 2, :c \"here\", :d \"again\"}"
  [& forms]
  (apply cond-it-impl forms))

; #todo #wip
(defmacro some-it->
  "Threads forms as with `it->`, terminates & returns `nil` if any expression is nil."
  [expr & forms]
  (let [binding-pairs (interleave (repeat 'it) forms)]
    `(let-some [~'it ~expr
                ~@binding-pairs]
               ~'it)))

(s/defn sorted-map-via-path :- tsk/Map
  "
  *************************************************************************
  ***** WARNING:  due to a bug in clojure.core/sorted-map-by,         *****
  *****           this crashes if namespaced keys are used.           *****
  *************************************************************************

  Given a source map, returns a sorted version of the same map. The value to sort
  by is specified via a path vector as with `clojure.core/get-in`, where the first
  element is always specified as `:*`, since the path must work for every top-level key
  in <src-map>. The sorting value must be acceptable to clojure.core/compare.
  Defaults to ascending sort order.  Returns an instance of `clojure.data.avl.AVLMap`.
  NOTE:  because of peculiarities of clojure.core/sorted-map-by, one cannot add new entries
  to the sorted map.  Instead, a new map must be created from a plain map.
  Usage:

      (sorted-map-via <src-map> <path-vec>)
      (sorted-map-via <src-map> <path-vec> <ascending?>)

  Example:

      (let [unsorted {:c {:val 3}
                      :a {:val 1}
                      :b {:val 2}}
            sorted   (sorted-map-via unsorted [:* :val])]
        (assert (= unsorted sorted))) "
  ; implicit sort order - ascending
  ([src-map :- tsk/Map
    path-vec :- tsk/Vec] (sorted-map-via-path src-map path-vec true))
  ; explicit sort order
  ([src-map :- tsk/Map
    path-vec :- tsk/Vec
    ascending? :- s/Bool]
   (assert-info (= :* (xfirst path-vec)) "First path element must be `:*`" (vals->map path-vec))
   (assert-info (pos? (count path-vec)) "path-vec must have at least 2 elements" (vals->map path-vec))
   (let [path-tail       (xrest path-vec)
         sortable-unique (fn [key]
                           (let [fetch-in-path (prepend key path-tail)
                                 sort-val      (fetch-in src-map fetch-in-path)]
                             [sort-val key]))
         comparator-fn   (fn [x y]
                           (let [compare-result (compare (sortable-unique x) (sortable-unique y))
                                 final-result   (cond-it-> compare-result
                                                  (not ascending?) (- it))]
                             final-result))
         sorted-map      (glue (avl/sorted-map-by comparator-fn) src-map)]
     sorted-map)))

;-----------------------------------------------------------------------------
(s/defn compare-increasing :- s/Bool
  "Returns true if each item is larger than its predecessor"
  [& xs :- [s/Any]]
  (assert (< 1 (count xs)))
  (every? neg?
          (for [[a b] (partition 2 1 xs)]
            (compare a b))))

(s/defn compare-increasing-or-equal :- s/Bool
  "Returns true if each item is larger or equal to its predecessor"
  [& xs :- [s/Any]]
  (assert (< 1 (count xs)))
  (every? nonpos?
          (for [[a b] (partition 2 1 xs)]
            (compare a b))))

; #todo => tupelo.tuple/less-than?
; #todo re-home lexical increasing/equal fns

; #todo already in tupelo.lexical - UNIFY!
; #todo => tupelo.tuple/compare
(defn ^:no-doc cmp-seq-lexi ; from generic compare from clojure.org
  [x y]
  (loop [x x
         y y]
    (if (seq x)
      (if (seq y)
        (let [c (compare (first x) (first y))]
          (if (zero? c)
            (recur (rest x) (rest y))
            c))
        1)          ; else we reached end of y first, so x > y
      (if (seq y)
        -1          ; we reached end of x first, so x < y
        0))))       ; Sequences contain same elements.  x = y

; #todo make variadic versions of these?
(s/defn increasing? :- s/Bool ; #todo => tupelo.tuple/less-than?
  "Returns true iff vector elements are in lexicographic increasing order:

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
  (neg? (cmp-seq-lexi a b)))

(s/defn increasing-or-equal? :- s/Bool ; #todo => tupelo.tuple/less-equal-than?
  "Returns true iff vector elements are equal or are in lexicographic increasing order:

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
  (nonpos? (cmp-seq-lexi a b)))

;---------------------------------------------------------------------------------------------------
#?(:clj             ; JVM stuff
   (do
     ;-----------------------------------------------------------------------------
     ; Java version stuff
     (s/defn version-str->semantic-vec :- [s/Int]
       "Returns the java version as a semantic vector of integers, like `11.0.17` => [11 0 17]"
       [s :- s/Str]
       (let [v1 (str/trim s)
             v2 (xsecond (re-matches #"([.0-9]+).*" v1)) ; remove any suffix like on `1.8.0-b097` or `1.8.0_234`
             v3 (str/split v2 #"\.")
             v4 (mapv #(Integer/parseInt %) v3)]
         v4))

     (s/defn java-version-str :- s/Str
       [] (System/getProperty "java.version"))

     (s/defn java-version-semantic :- [s/Int]
       [] (version-str->semantic-vec (java-version-str)))

     (s/defn java-version-min? :- s/Bool
       "Returns true if Java version is at least as great as supplied string.
       Sort is by lexicographic (alphabetic) order."
       [tgt-version-str :- s/Str]
       (let [tgt-version-vec    (version-str->semantic-vec tgt-version-str)
             actual-version-vec (java-version-semantic)
             result             (increasing-or-equal? tgt-version-vec actual-version-vec)]
         result))

     (assert-info (java-version-min? "1.7") "Must have at least Java 1.7" {:java-version (java-version-str)})

     (defn is-java-8-plus? [] (java-version-min? "1.8")) ; ***** NOTE: version string is still `1.8` *****
     (defn is-java-11-plus? [] (java-version-min? "11")) ; #todo need test
     (defn is-java-17-plus? [] (java-version-min? "17")) ; #todo need test

     (defmacro if-java-1-8-plus ; #todo need for java 9, 10, 11, ...
       "If JVM is Java 1.8 or higher, evaluates if-form into code. Otherwise, evaluates else-form."
       [if-form else-form]
       (if (is-java-8-plus?)
         `(do ~if-form)
         `(do ~else-form)))

     (defmacro if-java-1-11-plus ; #todo need test
       "If JVM is Java 1.11 or higher, evaluates if-form into code. Otherwise, evaluates else-form."
       [if-form else-form]
       (if (is-java-11-plus?)
         `(do ~if-form)
         `(do ~else-form)))

     (defmacro if-java-1-17-plus ; #todo need test
       "If JVM is Java 1.17 or higher, evaluates if-form into code. Otherwise, evaluates else-form."
       [if-form else-form]
       (if (is-java-17-plus?)
         `(do ~if-form)
         `(do ~else-form)))

     (defmacro when-java-1-11-plus ; #todo need test
       "If JVM is Java 1.11 or higher, evaluates forms into code. Otherwise, elide forms."
       [& forms]
       (when (is-java-11-plus?)
         `(do ~@forms)))

     ;-----------------------------------------------------------------------------
     ; Clojure version stuff
     ; #todo add is-clojure-1-8-max?
     ; #todo need clojure-1-8-plus-or-throw  ??
     (defn is-clojure-1-7-plus? []
       (let [{:keys [major minor]} *clojure-version*]
         (increasing-or-equal? [1 7] [major minor])))

     (defn is-clojure-1-8-plus? []
       (let [{:keys [major minor]} *clojure-version*]
         (increasing-or-equal? [1 8] [major minor])))

     (defn is-clojure-1-9-plus? []
       (let [{:keys [major minor]} *clojure-version*]
         (increasing-or-equal? [1 9] [major minor])))

     (defn is-clojure-1-10-plus? []
       (let [{:keys [major minor]} *clojure-version*]
         (increasing-or-equal? [1 10] [major minor])))

     (defn is-pre-clojure-1-8? [] (not (is-clojure-1-8-plus?)))
     (defn is-pre-clojure-1-9? [] (not (is-clojure-1-9-plus?)))
     (defn is-pre-clojure-1-10? [] (not (is-clojure-1-10-plus?)))

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

     (defmacro when-clojure-1-10-plus
       "Wraps code that should only be included for Clojure 1.10 or higher.  Otherwise, code is supressed."
       [& forms]
       (if (is-clojure-1-10-plus?)
         `(do ~@forms)))

     (defmacro when-not-clojure-1-9-plus
       "Wraps code that should only be included for Clojure versions prior to 1.9.  Otherwise, code is supressed."
       [& forms]
       (if (is-pre-clojure-1-9?)
         `(do ~@forms)))

     ;-----------------------------------------------------------------------------
     (when-clojure-1-9-plus
       (defn swap-out!
         "Just like clojure.core/swap!, but returns the old value"
         [tgt-atom swap-fn & args]
         (let [[old -new-] (apply swap-vals! tgt-atom swap-fn args)]
           old)))

     ;-----------------------------------------------------------------------------
     ; JVM type testing stuff

     (defn atom?
       "Returns true if x is a clojure.lang.Atom"
       [x] (= (type x) clojure.lang.Atom))

     (defn bigint?
       "Returns true if x is a clojure.lang.BigInt"
       [x] (= (type x) clojure.lang.BigInt))

     (defn biginteger?
       "Returns true if x is a java.math.BigInteger"
       [x] (= (type x) java.math.BigInteger))

     (defn bigdecimal?
       "Returns true if x is a java.math.BigDecimal (synonym for `clojure.core/decimal?`)"
       [x] (= (type x) java.math.BigDecimal))

     (defn int-val?
       "Returns true iff arg is an integer value of any Clojure/Java type
       (all int types, float/double, BigInt/BigInteger, BigDecimal, clojure.lang.Ratio)."
       [x]
       (cond
         (or (int? x) (integer? x)) true

         ; handles both java.lang.Float & java.lang.Double types
         (float? x) (let [x-dbl (double x)] (= x-dbl (Math/floor x-dbl)))

         (bigdecimal? x) (try
                           (let [bi-val (.toBigIntegerExact x)]
                             ; no exception => fraction was zero
                             true)
                           (catch Exception e
                             ; exception => fraction was non-zero
                             false))
         (ratio? x) (zero? (mod x 1))
         :else (throw (ex-info "Invalid type" {:x x}))))

     ))

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

                          #?@(:clj [(instance? java.io.InputStream item) (prettify-item (slurp item))]) ; #todo need test

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
                         (for [it (keep-if not-nil? (flatten [args]))]
                           ; Note that "sequential?" returns false for sets, strings, and the various
                           ; array types.
                           (cond
                             (or
                               (sequential? it)
                               (set? it)
                               (string? it)
                               (native-array? it)) (seq it)

                             #?@(:clj [(instance? java.io.InputStream it) (seq (slurp it))])

                             :else it)))
        ; Coerce any integer values into character equivalents (e.g. 65 -> \A), then combine
        ; into a single string.
        result         (apply str
                              (clojure.core/map char
                                                (keep-if not-nil? seq-of-scalars)))]
    result))

(defn print-versions
  "Print an information string with the current version of Clojure/ClojureScript [and Java]."
  []
  (let [version-str #?(:clj (format "Clojure %s    Java %s"
                                    (clojure-version) (System/getProperty "java.version"))
                       :cljs (str "ClojureScript " *clojurescript-version*))
        num-hyphen          (+ 6 (count version-str))
        hyphens             (str/join (repeat num-hyphen \-))
        version-str         (str "   " version-str)]
    (newline)
    (println hyphens)
    (println version-str)
    (println hyphens)))

(defn seq->str
  "Convert a seq into a string (using pr) with a space preceding each value"
  [seq-in]
  (with-out-str
    (doseq [it (seq seq-in)]
      (print \space)
      (pr it))))

;-----------------------------------------------------------------------------
(defmacro with-timer
  "Prints `id` and the elapsed (elapsed) execution time for a set of forms."
  [id & forms]
  `(let [start#   (System/nanoTime)
         result#  (do ~@forms)
         stop#    (System/nanoTime)
         elapsed# (double (- stop# start#))
         secs#    (/ elapsed# 1e9)]
     (println (format ":with-timer   %s   = %.3f sec" ~id secs#))
     result#))

(defmacro with-timer-x
  "Prints the form and its (elapsed) execution time."
  [form]
  `(let [start#   (System/nanoTime)
         result#  (do ~form)
         stop#    (System/nanoTime)
         elapsed# (double (- stop# start#))
         secs#    (/ elapsed# 1e9)]
     (println (format ":with-timer-x   %s   = %.3f sec" (str '~form) secs#))
     result#))

;-----------------------------------------------------------------------------

(defmacro let-some
  "Threads forms as with `when-some`, but allow more than 1 pair of binding forms."
  [bindings & forms]
  (let [num-bindings (count bindings)]
    (assert-info (even? num-bindings) (str "num-bindings must be even; value=" num-bindings) bindings)
    (if (pos? num-bindings)
      `(let [result# ~(cc/second bindings)]
         (when (not-nil? result#)
           (let [~(cc/first bindings) result#]
             (let-some ~(cc/drop 2 bindings) ~@forms))))
      `(do ~@forms))))


; #todo fix so doesn't hang if give infinite lazy seq
; #todo rename :strict -> :trunc
(defmacro map-let*
  "Usage:  (map-let* ctx bindings & forms)

  where ctx is a map with default values:
    {:strict true
     :lazy   false}"
  [context bindings & forms]
  (assert-info (not-empty? bindings) "map-let*: bindings cannot be empty=" bindings)
  (assert-info (even? (count bindings)) "map-let*: (count bindings) must be even=" bindings)
  (assert-info (pos? (count forms)) "map-let*: forms cannot be empty=" forms)
  (let [binding-pairs (partition 2 bindings)
        syms          (mapv xfirst binding-pairs)
        colls         (mapv xsecond binding-pairs)]
    `(do
       (assert-info (map? ~context) "map-let*: context must be a map=" ~context)
       (let [lazy#          (get ~context :lazy false)
             strict#        (get ~context :strict true)
             lengths#       (mapv count ~colls)
             lengths-equal# (apply = lengths#)
             map-fn#        (fn ~syms ~@forms)
             output-fn#     (if lazy# identity vec)]
         (when (and strict#
                    (not lengths-equal#))
           (throw (ex-info "map-let*: colls must all be same length" {:lens lengths#})))
         (output-fn# (map map-fn# ~@colls))))))

(defmacro map-let
  "Usage: (map-let bindings & forms)

  Given bindings and forms like

      (map-let [x xs
                y ys]
        (+ x y))

  will iterate over the collections [xs ys] assigning
  successive values of each collection to `x` & `y`, respectively.  Note that the sequences are
  consumed ***in parallel***, and are not nested as with `for` and `doseq`.
  The local symbols `x` & `y` can then be used in `forms` to generate the output mapping.
  Will throw if collections are not all of the same length. Not lazy."
  [bindings & forms]
  `(map-let* {:strict true
              :lazy   false}
             ~bindings ~@forms))

(s/defn xmap :- tsk/Vec
  "Like clojure.core/mapv, but throws if colls are not of equal length."
  [map-fn & colls]
  (assert-info (not-empty? colls) "colls cannot be empty" {})
  (let [col-lens (mapv count colls)]
    (assert-info (apply = col-lens) "xmap: colls must all be same length" (vals->map col-lens))
    (apply mapv map-fn colls)))

; #todo rename :strict -> :trunc
(defn zip*
  "Usage:
        (zip* ctx & colls)
  Like `zip` in Python.  Given 2 or more sequences `colls`, joins the i'th item from each
  collection into a vector, returning a vector of vectors. Context map `ctx` defaults to
  `{:strict true}`. If `:strict` is set, colls must be identical in length.
  Will accept infinite (lazy) sequences like `(range)`. Output is not lazy. "
  [ctx & colls]     ; #todo how use Schema with "rest" args?
  (assert (map? ctx))
  (assert #(every? sequential? colls))
  (let [num-colls  (count colls)
        strict-flg (get ctx :strict true)]
    (loop [result []
           colls  colls]
      (let [empty-flgs  (mapv empty? colls)
            num-empties (count (keep-if truthy? empty-flgs))]
        (if (zero? num-empties)
          (do
            (let [new-row     (mapv xfirst colls)
                  new-results (append result new-row)]
              (recur
                new-results
                (mapv xrest colls))))
          (do
            (when (and strict-flg
                       (not= num-empties num-colls))
              (throw (ex-info "zip*: collections are not all same length; empty-flgs="
                              (vals->map ctx empty-flgs))))
            result))))))

; #todo add schema; result = tsk/List[ tsk/Vector ]
; #todo add :trunc & assert;
(defn zip
  "Zips together vectors producing a vector of tuples (like Python zip).
  Example:

        (zip
          [:a :b :c]
          [ 1  2  3]
          [:x :y :z)

        ;=>  [ [:a 1 :x]
               [:b 2 :y]
               [:c 3 :z] ]
    Will accept infinite (lazy) sequences like `(range)`. Output is not lazy. "
  [& args]
  (assert #(every? sequential? args))
  (apply zip* {:strict true} args))

(defn zip-lazy
  "Usage:  `(zip-lazy coll1 coll2 ...)`

        (zip-lazy xs ys zs) => [ [x0 y0 z0]
                                 [x1 y1 z1]
                                 [x2 y2 z2]
                                 ... ]

  Returns a lazy result. Will truncate to the length of the shortest collection.
  A convenience wrapper for `(map vector coll1 coll2 ...)`.  "
  [& colls]         ; #todo how use Schema with "rest" args?
  (assert #(every? sequential? colls))
  (apply map vector colls))

(defn indexed
  "Given one or more collections, returns a lazy sequence of indexed tuples from the collections:

        (indexed xs ys zs) -> [ [0 x0 y0 z0]
                                [1 x1 y1 z1]
                                [2 x2 y2 z2]
                                ... ]
                                "
  [& colls]
  (apply zip-lazy (range) colls))

(defmacro lazy-cons
  "The simple way to create a lazy sequence:

        (defn lazy-next-int [n]
          (t/lazy-cons n (lazy-next-int (inc n))))

        (def all-ints (lazy-next-int 0))
        "
  [curr-val recursive-call-form]
  `(lazy-seq (cons ~curr-val ~recursive-call-form)))

; #todo enhance to handle BigDec
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
    (assert-info (or digits tol) "Must specify either :digits or :tol" opts)
    (when tol
      (assert-info (number? tol) ":tol must be a number" opts)
      (assert-info (pos? tol) ":tol must be positive" opts))
    (when digits
      (assert-info (integer? digits) ":digits must be an integer" opts)
      (assert-info (pos? digits) ":digits must positive" opts))
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
    (assert-info (= num-x num-y) ": x-vals & y-vals must be same length" (vals->map num-x num-y)))
  (every? truthy?
          (clojure.core/map #(apply rel= %1 %2 opts)
                            x-vals y-vals)))

(comment
  (defn deep-rel=   ; #todo add sets
    [a b]
    (or (= a b)
        (and (number? a) (number? b) (or (tupelo.core/rel= a b :tol 1e-5)
                                         (tupelo.core/rel= a b :digits 5)))
        (and (map? a) (map? b) (every? truthy? (map-let [[ak av] (->sorted-map-generic a)
                                                         [bk bv] (->sorted-map-generic b)]
                                                        (and (deep-rel= ak bk) (deep-rel= av bv)))))
        (and (sequential? a) (sequential? b) (every? truthy? (map-let [av a
                                                                       bv b]
                                                                      (deep-rel= av bv)))))))

; #todo => tupelo.misc
; #todo add sets
; #todo add ctx options map as 1st arg
; #todo add var-args pairwise mode
(defn deep-rel=
  [a b]
  (or (= a b)
      (and (number? a) (number? b) (or (tupelo.core/rel= a b :tol 1e-5)
                                       (tupelo.core/rel= a b :digits 5)))
      (and (map? a) (map? b) (every? truthy? (map-let [[ak av] (->sorted-map-generic a)
                                                       [bk bv] (->sorted-map-generic b)]
                                                      (and (deep-rel= ak bk) (deep-rel= av bv)))))
      (and (sequential? a) (sequential? b) (every? truthy? (map-let [av a
                                                                     bv b]
                                                                    (deep-rel= av bv))))))

; #todo need docs & tests
; #todo:  add
;            (thru start stop step) uses integer steps and
;            (rel= curr stop :tol step) as ending criteria
;  #todo range version => (butlast (thru ...))
(defn thru          ; #todo make lazy: (thruz ...) -> (thru* {:lazy true} ...)
  "Returns a vector of numbers. Like clojure.core/range, but is inclusive of the right boundary value.
  Uses rounding to calculate an integer number of steps
  Not lazy.

        (thru  1  3)            -> [1  2  3]
        (thru  1  5    2)       -> [1  3  5]
        (thru  1  1.3  0.1)     -> [1.0  1.1  1.2  1.3]
  "
  ([end] (thru 0 end))
  ([start end] (thru start end 1))
  ([start end step]
   (let [delta          (- (double end) (double start))
         nsteps-dbl     (/ (double delta) (double step))
         nsteps-int     (Math/round nsteps-dbl)
         rounding-error (Math/abs (- nsteps-dbl nsteps-int))]
     (assert-info (< rounding-error 1e-5)
                  "thru: non-integer number of steps \n   args:" (vals->map start end step rounding-error))
     (vec (clojure.core/map #(-> %
                                 (* step)
                                 (+ start))
                            (range (inc nsteps-int)))))))

; #todo need CLJS coercion ->char (char/str or int)
; #todo need CLJS coercion ->int (char/str or int)
; #todo need CLJS version of char? => len-1 string

; #todo need test, readme
; #todo merge into `thru` using a protocol for int, double, char, string, keyword, symbol, other?
(defn chars-thru    ; #todo add schema.
  "Given two characters (or numerical equivalents), returns a seq of characters
  (inclusive) from the first to the second.  Characters must be in ascending order."
  [start-char stop-char]
  ; #todo throw if not char or int
  (let [start-int (cond-it-> start-char
                    (not (integer? it)) (char->codepoint it))
        stop-int  (cond-it-> stop-char
                    (not (integer? it)) (char->codepoint it))]
    (assert-info (and (nonneg? start-int) (<= stop-int 65535))
                 "chars-thru: start/stop out of range" (vals->map start-char stop-char start-int stop-int))
    (assert-info (<= start-int stop-int) "chars-thru: start/stop out of order" (vals->map start-char stop-char start-int stop-int))
    (mapv codepoint->char
          (thru start-int stop-int))))

(s/defn repeat-dims :- [s/Any]
  "Like clojure.core/repeat, but accepts a vector of N dimensions:

        (t/repeat-dims [3] 9)    =>  [9 9 9]

        (t/repeat-dims [2 3] 9)  =>  [[9 9 9]
                                      [9 9 9]] "
  [dims :- [s/Num]
   val :- s/Any]
  (assert (pos? (count dims)))
  (assert (every? int-nonneg? dims))
  (let [dim-curr (xfirst dims)]
    (vec
      (if (= 1 (count dims))
        (repeat dim-curr val)
        (repeat dim-curr (repeat-dims (xrest dims) val))))))

; #todo rename to "get-in-safe" ???
; #todo make throw if not Associative arg (i.e. (get-in '(1 2 3) [0]) -> throw)
; #todo make throw if any index invalid
; #todo need safe (assoc-in m [ks] v) (assoc-in m [ks] v :missing-ok)
; #todo need safe (update-in m [ks] f & args)
(s/defn fetch-in :- s/Any
  "A fail-fast version of clojure.core/get-in. When invoked as (fetch-in mappy path),
   returns the value associated with path as for (clojure.core/get-in mappy path).
   Throws an Exception if the path path is not present in mappy."
  [mappy :- (s/cond-pre tsk/Map tsk/Vec)
   path :- tsk/Vec] ; #todo add arity to take default value like `get-in`
  (validate associative? mappy)
  (let [result (get-in mappy path ::not-found)]
    (if (= result ::not-found)
      (throw (ex-info "Key seq not present in map:" {:path path :mappy (snip mappy)}))
      result)))

(s/defn fetch :- s/Any
  "A fail-fast version of keyword/map lookup.  When invoked as (fetch the-map :the-key),
   returns the value associated with :the-key as for (clojure.core/get the-map :the-key).
   Throws an Exception if :the-key is not present in the-map."
  [the-map :- tsk/Map
   the-key :- s/Any]
  (fetch-in the-map [the-key]))

; #todo:  (grab [:person :address :zip] the-map)  => fetch-in
; #todo:  (grab-all :name :phone [:address :zip] the-map)
; #todo:      => (mapv #(grab % the-map) keys)
; #todo:  allow to use a default value like `get`
(s/defn grab :- s/Any
  "A fail-fast version of keyword/map lookup.  When invoked as (grab :the-key the-map),
   returns the value associated with :the-key as for (clojure.core/get the-map :the-key).
   Throws an Exception if :the-key is not present in the-map."
  [the-key :- s/Any
   the-map :- tsk/Map]
  (fetch-in the-map [the-key]))

(defrecord ^:no-doc SpliceItem [data])
(s/defn <> :- SpliceItem
  "Splice operator.

  Works with the `->vector` function to splice vectors/lists and insert
  their elements as with the unquote-spicing operator (~@).  Modeled
  on the Javascript React splice operator `<>`. Examples:

        (->vector 1 2 3      4 5 6   7 8 9)   =>  [1 2 3 4 5 6 7 8 9]
        (->vector 1 2 3 (<> [4 5 6]) 7 8 9)   =>  [1 2 3 4 5 6 7 8 9] "
  [data :- [s/Any]]
  (assert (sequential? data))
  (->SpliceItem data))

(s/defn ->vector :- [s/Any]
  "Wraps all args in a vector, as with `clojure.core/vector`. Will (recursively) recognize
  any embedded calls to the splice operator like `(<> [4 5 6)` (a la React)
  and insert their elements as with the unquote-spicing operator (~@). Examples:

        (->vector 1 2 3      4 5 6   7 8 9)   =>  [1 2 3 4 5 6 7 8 9]
        (->vector 1 2 3 (<> [4 5 6]) 7 8 9)   =>  [1 2 3 4 5 6 7 8 9]
        "
  [& args :- [s/Any]]
  (let [result (reduce (fn [accum item]
                         (let [it-use    (cond
                                           (sequential? item) [(apply ->vector item)]
                                           (instance? SpliceItem item) (apply ->vector (fetch item :data))
                                           :else [item])
                               accum-out (glue accum it-use)]
                           accum-out))
                       [] args)]
    result))

(s/defn unnest :- [s/Any] ; #todo readme
  "Given any set of arguments including vectors, maps, sets, & scalars, performs a depth-first
  recursive walk returning scalar args (int, string, keyword, etc) in a single 1-D vector."
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

(defn validate
  "(validate tst-fn tst-val)
  Used to validate intermediate results. Returns tst-val if the result of
  (tst-fn tst-val) is truthy.  Otherwise, throws ex-info with ex-data
  {:sample-val sample-val :tst-result tst-result}."
  [tst-fn tst-val]
  (let [tst-result (tst-fn tst-val)]
    (assert-info (truthy? tst-result) "validate: " (vals->map tst-val tst-result))
    tst-val))

(defn validate-or-default
  "Returns `sample-val` if `(is-valid? sample-val)` is truthy; else returns `default-val`"
  [is-valid? sample-val default-val]
  (if (is-valid? sample-val)
    sample-val
    default-val))

(defn with-nil-default
  "Returns `sample-val` if not nil; else returns `default-val`"
  [default-val sample-val]
  (validate-or-default not-nil? sample-val default-val))

(defmacro verify-form
  "
         (verify <some-expr>)

  Used to verify intermediate results. Returns value of `<some-expr>` if the result
  is truthy.  Otherwise, throws an Exception."
  [form]
  `(let [value# ~form]
     (if (truthy? value#)
       value#
       (throw (ex-info "verification failed  " '~form)))))

;-----------------------------------------------------------------------------
; #todo need option for (take 3 coll :exact) & drop; xtake xdrop

; #todo fix up for maps
(defn rand-elem
  "Returns a random element from a collection"
  [coll]
  (verify-form (not-nil? coll))
  (rand-nth (vec coll)))

; #todo: maybe make more general version?
(s/defn ^:no-doc vec-shuffle :- tsk/Vec
  "Given a data vector, returns a new vector consisting of elements from the supplied indexs."
  [data :- tsk/Vec
   idxs :- [s/Int]]
  (assert (= (count idxs) (count data))) ; #todo maybe remove this restriction?
  (let [data (it-> data ; ensure it is a vector for random access performance
                   (not (vector? data)) (vec data))]
    (forv [idx idxs]
      (nth data idx))))

;-----------------------------------------------------------------------------
; #todo convert to (submap-by-keys ctx m ks) & (submap-by-vals ctx m ks) variants
; #todo filter by pred in addition to set/list?
; #todo -> README
(s/defn submap-by-keys :- tsk/Map
  "Returns a new map containing entries with the specified keys. Throws for missing keys,
  unless `:missing-ok` is specified. Usage:

      (submap-by-keys {:a 1 :b 2} #{:a   }             )  =>  {:a 1}
      (submap-by-keys {:a 1 :b 2} #{:a :z} :missing-ok )  =>  {:a 1}
  "
  [map-arg :- tsk/Map
   keep-keys :- (s/if set? tsk/Set tsk/List)
   & opts]
  (let [keep-keys (set keep-keys)]
    (if (= opts [:missing-ok])
      (do
        (apply glue {}
               (for [key keep-keys]
                 (with-exception-default {}
                   {key (grab key map-arg)}))))
      (do
        (apply glue {}
               (for [key keep-keys]
                 {key (grab key map-arg)}))))))

; #todo -> README
(s/defn submap-by-vals :- tsk/Map
  "Returns a new map containing entries with the specified vals. Throws for missing vals,
  unless `:missing-ok` is specified. Usage:

      (submap-by-vals {:a 1 :b 2 :A 1} #{1  }             )  =>  {:a 1 :A 1}
      (submap-by-vals {:a 1 :b 2 :A 1} #{1 9} :missing-ok )  =>  {:a 1 :A 1} "
  [map-arg :- tsk/Map
   keep-vals :- (s/if set? tsk/Set tsk/List)
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
  "Returns true if the map entries (key-value pairs) of one map are a subset of the entries of
   another map.  Similar to clojure.set/subset?"
  [inner-map :- {s/Any s/Any} ; #todo
   outer-map :- {s/Any s/Any}] ; #todo
  (let [inner-set (set inner-map)
        outer-set (set outer-map)]
    (set/subset? inner-set outer-set)))

(s/defn keyvals :- [s/Any]
  "For any map m, returns the (alternating) keys & values of m as a vector, suitable for reconstructing m via
   `(apply hash-map (keyvals m))`. `(keyvals {:a 1 :b 2} => [:a 1 :b 2] ` "
  [m :- tsk/Map]
  (reduce into [] (seq m)))

(do                 ; #todo fix delete this???
  (s/defn ^:no-doc keyvals-seq-impl :- [s/Any]
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

  ; #todo convert to (keyvals (select-keys m ks))
  (s/defn keyvals-seq :- [s/Any]
    "For any map m, returns the (alternating) keys & values of m as a vector, suitable for reconstructing m via
     (apply hash-map (keyvals m)). (keyvals {:a 1 :b 2} => [:a 1 :b 2]

           Usage:  (keyvals-seq ctx) ctx-default: {:missing-ok false}
                   (keyvals-seq the-map the-keys) "
    ([ctx :- tsk/KeyMap]
     (let [defaults {:missing-ok false}]
       (keyvals-seq-impl (into defaults ctx))))
    ([the-map :- tsk/KeyMap
      the-keys :- [s/Any]]
     (keyvals-seq (vals->map the-map the-keys))))
  )

; #todo add reference to medley/deep-merge  ???

; #todo rename -> drop-idx
; #todo force to vector result
; #todo allow range to drop
(s/defn drop-at :- tsk/List
  "Removes an element from a collection at the specified index."
  [coll :- tsk/List
   index :- s/Int]
  (assert-info (nonneg? index) "Index cannot be negative " index)
  (assert-info (< index (count coll)) "Index cannot exceed collection length: " {:length (count coll) :index index})
  (glue (take index coll)
        (drop (inc index) coll)))

; #todo rename -> insert-idx
; #todo force to vector result
; #todo allow vector to insert
(s/defn insert-at :- tsk/List
  "Inserts an element into a collection at the specified index."
  [coll :- tsk/List
   index :- s/Int
   elem :- s/Any]
  (assert-info (nonneg? index) "Index cannot be negative " index)
  (assert-info (<= index (count coll)) "Index cannot exceed collection length: " {:length (count coll) :index index})
  (glue (take index coll) [elem]
        (drop index coll)))

; #todo rename -> elem-set
; #todo force to vector result
; #todo allow idx range to replace with vector (maybe not equal # of elems)
(s/defn replace-at :- tsk/List
  "Replaces an element in a collection at the specified index."
  [coll :- tsk/List
   index :- s/Int
   elem :- s/Any]
  (assert-info (nonneg? index) "Index cannot be negative " index)
  (when (<= (count coll) index)
    (throw (ex-info "Index cannot exceed collection length: " {:length (count coll) :index index})))
  (glue
    (take index coll)
    [elem]
    (drop (inc index) coll)))

; #todo use (idx    coll int-or-kw) as `get` replacement?
; #todo use (idx-in coll [kw's]) as `fetch-in` replacement?
; #todo allow (idx coll [low high]) like python xx( low:high )
; #todo multiple dimensions
(s/defn idx
  "Indexes into a vector, allowing negative index values"
  [coll :- tsk/List
   index-val :- s/Int]
  (assert-info (not-nil? coll) "idx: coll cannot be nil: " (vals->map coll))
  (let [data-vec (vec coll)
        N        (count data-vec)
        >>       (assert (pos? N))
        ii       (mod index-val N)
        >>       (assert-info (< ii (count coll)) "Index cannot exceed collection length: " {:len (count coll) :index ii})
        result   (clojure.core/get data-vec ii)]
    result))

(s/defn map-keys :- tsk/Map ; #todo README
  "Transforms each key in a map using the supplied `tx-fn`:

        (t/map-keys {1 :a 2 :b 3 :c} inc)                  =>  {  2 :a   3 :b 4   :c}
        (t/map-keys {1 :a 2 :b 3 :c} {1 101 2 202 3 303})  =>  {101 :a 202 :b 303 :c}"
  [map-in :- tsk/Map
   tx-fn :- tsk/Fn
   & tx-args]
  (let [tuple-seq-orig (vec map-in)
        tuple-seq-out  (for [[tuple-key tuple-val] tuple-seq-orig]
                         [(apply tx-fn tuple-key tx-args) tuple-val])
        map-out        (into {} tuple-seq-out)]
    map-out))

(s/defn map-vals :- tsk/Map ; #todo README ; #todo docstring, README
  "Transforms each value in a map using the supplied `tx-fn`:

        (t/map-vals {:a 1 :b 2 :c 3} inc)                  =>  {:a 2,   :b 3,   :c 4}
        (t/map-vals {:a 1 :b 2 :c 3} {1 101 2 202 3 303})  =>  {:a 101, :b 202, :c 303} "
  [map-in :- tsk/Map
   tx-fn :- tsk/Fn
   & tx-args]
  (let [tuple-seq-orig (vec map-in)
        tuple-seq-out  (for [[tuple-key tuple-val] tuple-seq-orig]
                         [tuple-key (apply tx-fn tuple-val tx-args)])
        map-out        (into {} tuple-seq-out)]
    map-out))

(def MapKeySpec (s/if set? #{s/Any} [s/Any])) ; #todo fix this...?
(s/defn validate-map-keys :- s/Any ; #todo docstring, README
  "Throws if any map key is not in the valid list. Returns the map."
  [tst-map :- tsk/Map
   valid-keys :- MapKeySpec]
  (let [valid-keys (set valid-keys)
        map-keys   (keys tst-map)]
    (when-not (every? truthy?
                      (forv [curr-key map-keys]
                        (contains-key? valid-keys curr-key)))
      (throw (ex-info "validate-map-keys: invalid key found " (vals->map tst-map valid-keys))))
    tst-map))

; #todo readme
(s/defn starts-with? :- s/Bool
  "Returns true when the initial elements of coll match those of tgt"
  [coll tgt-in]     ; #todo schema
  (let [tgt-vec (vec tgt-in)
        tgt-len (count tgt-vec)]
    (if (< (count coll) tgt-len)
      false
      (let [coll-vals (take tgt-len coll)]
        (= coll-vals tgt-vec)))))

; #todo readme
(defn index-using
  "Finds the first index N where (< N (count coll)) such that (pred (drop N coll)) is truthy.
  Returns `nil` if no match found."
  [pred coll]
  (let [all-vals (vec coll)
        num-vals (count all-vals)]
    (loop [i 0]
      (if (<= num-vals i)
        nil         ; did not find match
        (let [curr-vals (subvec all-vals i)]
          (if (pred curr-vals)
            i
            (recur (inc i))))))))

; #todo readme
(defn split-using   ; #todo schema
  "Splits a collection based on a predicate with a collection argument.
  Finds the first index N such that (pred (drop N coll)) is true. Returns a length-2 vector
  of
       [ (take N coll) (drop N coll) ]

  If pred is never satisified, `[ coll [] ]` is returned."
  [pred coll]
  (let [N (index-using pred (vec coll))]
    (if (nil? N)
      [coll []]
      [(take N coll) (drop N coll)])))

; #todo readme
(defn split-match   ; #todo schema
  "Splits a collection src by matching with a sub-sequence tgt of length L.
  Finds the first index N such that

       (= tgt (->> coll (drop N) (take L)))

  is true. Returns a length-2 vector of [ (take N coll) (drop N coll) ].
  If no match is found, `[ coll [] ]` is returned."
  [coll tgt]
  (split-using
    (fn [partial-coll] (starts-with? partial-coll (vec tgt)))
    (vec coll)))

; #todo readme
(s/defn partition-using
  "Partitions a collection into vector of segments based on a predicate with a collection argument.
  The first segment is initialized by removing the first element from `coll`, with subsequent
  elements similarly transferred as long as `(pred remaining-coll)` is falsey. When
  `(pred remaining-coll)` becomes truthy, the algorithm begins building the next segment.
  Thus, the first partition finds the smallest N (< 0 N) such that

        (pred (drop N coll))

  is true, and constructs the segment as

        (take N coll)

  If pred is never satisified, `[coll]` is returned."
  [pred :- s/Any    ; a predicate function taking a list arg
   coll :- tsk/List]
  (loop [vals   (vec coll)
         result []]
    (if (empty? vals)
      result
      (let [out-first  (take 1 vals)
            [out-rest unprocessed] (split-using pred (cc/rest vals))
            out-vals   (glue out-first out-rest)
            new-result (append result out-vals)]
        (recur unprocessed new-result)))))

(s/defn partition-when :- [tsk/Vec]
  "Given a data vector, calls `split-at` for all non-degenerate points to generate vector pairs
  `[data1 data2]`.  Presents these pairs to the predicate function `pred`, and partitions the data
   where indicated by a truthy result.  Example:

        (let [split-fn (fn [data1 data2]
                         (let [x (last data1)
                               y (first data2)]
                           (< (inc x) y)))]
          (is= [[1 2 3] [8 9 10] [99]]
            (t/partition-when split-fn
              [1 2 3 8 9 10 99])))
  "
  [pred :- tsk/Fn
   data :- tsk/Vec]
  (let [data       (vec data) ; ensure it is a vector so we can use `subvec`
        N          (count data)
        N-1        (dec N)
        ; We use `subvec` to partition the coll. Given a coll like [0 1 2], it makes
        ; no sense to give degenerate splits like {:data1 [] :data2 [0 1 2]}
        ; or {:data1 [0 1 2] :data2 []}. So, we need the split point in the range [1..(N-1)]
        split-idxs (reduce (fn [cum i]
                             (let [data1    (subvec data 0 i)
                                   data2    (subvec data i N)
                                   split?   (pred data1 data2)
                                   cum-next (if split?
                                              (append cum i)
                                              cum)]
                               cum-next))
                           []
                           (thru 1 N-1))

        ; Since we are using `subvec`, we must add in the "default" values at the start/end of the vector
        split-idxs (glue [0] split-idxs [N])
        idx-pairs  (partition 2 1 split-idxs)
        subvecs    (reduce (fn [cum [i-start i-end]]
                             ; remember that (subvec v i j) is the "slice" [i j)
                             (let [next-part (subvec data i-start i-end)
                                   next-cum  (append cum next-part)]
                               next-cum))
                           []
                           idx-pairs)]
    subvecs))

(s/defn iterate-n :- s/Any
  "Calls `(iterate f x)` n times, returning that result (indexed from 0); i.e.
        n=0   => x
        n=1   => (f x)
        n=2   => (f (f x))
  "
  [N :- s/Int
   f :- tsk/Fn
   x :- s/Any]
  (assert (int-nonneg? N))
  (last
    (take (inc N)   ; (take 0 <seq>) returns [], so we need (inc N) here to get a result
          (iterate f x))))

(s/defn interleave-all :- tsk/List
  "Interleave all items from input collections, without discarding any values"
  [& colls :- [tsk/List]]
  (assert (every? sequential? colls))
  (let [vecs          (mapv vec colls)
        num-vecs      (count colls)
        lengths       (mapv count colls)
        max-len       (apply max lengths)
        total-items   (apply + lengths)
        result-padded (forv [idx (range max-len)
                             ivec (range num-vecs)]
                        (let [curr-vec (get vecs ivec)
                              value    (get curr-vec idx ::dummy)]
                          value))
        result        (drop-if #(= ::dummy %) result-padded)]
    (assert (= (count result) total-items))
    result))

; #todo readme
(s/defn take-while-result :- tsk/List
  "Takes from a collection based on a predicate with a collection argument.
  Continues taking from the source collection until `(pred <taken-items>)` is falsey.
  If pred is never falsey, `coll` is returned."
  [pred coll]
  (assert-info (and (not-nil? coll) (not-empty? coll))
               "invalid source collection" {:coll coll})
  (loop [taken     []
         remaining (seq coll)]
    (if (empty? remaining)
      taken
      (let [taken-next     (append taken (xfirst remaining))
            remaining-next (xrest remaining)]
        (if (not (pred taken-next))
          taken
          (recur taken-next remaining-next))))))

(s/defn distinct-using :- tsk/List
  "Removes elements from a collection so that the result has no duplicates of `(keyfn <elem>)`.
  Employs a first-one-wins strategy. Not lazy."
  [keyfn :- tsk/Fn
   coll :- tsk/List]
  (loop [seen    #{}
         waiting coll
         keepers []]
    (if (empty? waiting)
      keepers
      (let [candidate (xfirst waiting)
            key       (keyfn candidate)]
        (if (contains? seen key)
          (recur seen (xrest waiting) keepers)
          (recur (conj seen key) (xrest waiting) (append keepers candidate)))))))

(s/defn val= :- s/Bool ; maybe value=  or   map=  (like set=)
  "Compares values for equality using clojure.core/=, treating records as plain map values:

        (defrecord SampleRec [a b])
        (assert (val= (->SampleRec 1 2) {:a 1 :b 2}))   ; fails for clojure.core/= "
  [& vals :- [s/Any]]
  (let [mapify   (fn [arg]
                   (if (map? arg)
                     (into {} arg)
                     arg))
        mapified (mapv #(walk/postwalk mapify %) vals)
        result   (apply = mapified)]
    result))


(s/defn set= :- s/Bool
  "Returns true if the collections are equal when converted to sets."
  [& colls :- [s/Any]]
  (truthy? (apply = (mapv set colls))))


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
  (assert-info (even? (count bindings)) "destruct: uneven number of bindings:" bindings)
  (assert-info (not-empty? bindings) "destruct: bindings empty:" bindings)
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

            ; #todo fix to work for "namespaced" calls like (t/restruct) & (t/restruct-all)
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
                                            restr-one-def  (get restruct-one-defs restr-one-data ::not-found)]
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
                                          (throw (ex-info "restruct:  aborting..." (:count (count datas)))))
                                        (list 'let ['restruct-fn restruct-only-def
                                                    'result (list 'restruct-fn)]
                                              'result))))
                                  res-one)]
        ; (do (nl) (spyx-pretty res-only))
        res-only))))

; #todo maybe (with-destruct ...) implies automatic (restruct) upon exit
(defmacro destruct
  "Natural destructuring:

       (let [data {:a 1
                   :b {:c 3
                       :d 4}}]
         ...
         (destruct [data {:a ?
                          :b {:c ?}}]
         ...

   then can use local values  a=1, c=3.  With vector data:

       (let [data [1 2 3 4 5]]
         ...
         (destruct [data [a b c]]
          ...

   then can use local values a=1 b=2 c=3.  Can use `(restruct)`, `(restruct data)`, or `(restruct-all)`
   to re-structure & return original data shape using current values."
  [bindings & forms]
  (destruct-impl bindings forms))

; #todo need a way to do
;(let [ctx {:a {:b 2
;               :c 3}}]
;  (within-it ctx [:a :b]
;    (inc it)))
;
;  => {:a {:b 3
;          :c 3}}
;
;  (destruct [ctx {:a {:b it}}   ; long version
;    (inc it)
;    (restruct))
;
;  #todo automated restructuring (maybe simplest)
;  (with-destruct [ctx {:a {:b ?}}
;    (inc b))


(defn restruct
  "within a `(destruct [<data> <shape>] ...)` form, `(restruct)` or `(restruct <data>)`
   causes re-structuring & return of original data shape using current values."
  [& args] (throw (ex-info "restruct: illegal usage - should never get here." args)))

(defn restruct-all
  "Within a form

      (destruct [data-1 <shape-1>
                 data-2 <shape-2] ...)

   causes re-structuring & return of original data shapes using
   current values as with

        (vals->map data-1 data-2 ...)
  "
  [& args] (throw (ex-info "restruct-all: illegal usage - should never get here." args)))

; #todo allow pred fn to replace entire node in search path:
; #todo    (fn [node] (and (contains? #{:horse :dog} (grab :animal/species node))
; #todo                 (<= 1 (grab :age node) 3 )))   ; an "adolescent" animal
(s/defn ^:no-doc wild-match-impl
  [ctx :- tsk/KeyMap ; #todo more precise schema needed { :submap-ok s/Bool ... }
   pattern :- s/Any
   value :- s/Any]
  (with-map-vals ctx [submap-ok subset-ok subvec-ok wildcard-ok pred-fn-ok]
    (let [result (truthy?
                   (cond
                     (= pattern value) true

                     (and wildcard-ok
                          (= pattern :*)) true

                     (and pred-fn-ok
                          (fn? pattern)) (pattern value)

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

                     :default false))]
      result)))

(defn wild-match-root? ; #todo readme
  [ctx-in]
  (let [ctx (glue {:submap-ok   false
                   :subset-ok   false
                   :subvec-ok   false
                   :wildcard-ok true
                   :pred-fn-ok  true}
                  ctx-in)]
    (with-map-vals ctx [pattern values]
      (every? truthy?
              (for [value values]
                (wild-match-impl ctx pattern value))))))

(defmulti wild-match?
          "Returns true if a pattern is matched by one or more values.  The special keyword :* (colon-star)
           in the pattern serves as a wildcard value.  Note that a wildcald can match either a primitive or a
           composite value: Classic usage:

               (wild-match? pattern & values)

           examples:

               (wild-match? {:a :* :b 2}
                            {:a 1  :b 2})         ;=> true

               (wild-match? [1 :* 3]
                            [1 2  3]
                            [1 9  3] ))           ;=> true

               (wild-match? {:a :*       :b 2}
                            {:a [1 2 3]  :b 2})   ;=> true

           wild-match? also accepts a context map; usage:

               (wild-match? ctx)

           example (default values shown):

               (wild-match?  { :submap-ok   false
                               :subset-ok   false
                               :subvec-ok   false
                               :wildcard-ok true
                               :pred-fn-ok  true
                               :pattern     <required param>
                               :values    [ <patttern-spec>+ ]   ; vector of 1 or more required
                             } )
        "
          (fn wild-match-dispatch-fn [& args]
            (if (and (= 1 (count args))
                     (map? (only args)))
              :ctx
              :classic)))

(defmethod wild-match? :ctx
  [ctx]
  (wild-match-root? ctx))

(defmethod wild-match? :classic
  [pattern & values]
  (verify-form #(pos? (count values)))
  (wild-match-root?
    (vals->map pattern values)))

(defn submatch?     ; #todo readme & test
  "Returns true if the first arg is (recursively) a subset/submap/subvec of the 2nd arg"
  [smaller larger]
  (let [ctx {:submap-ok   true
             :subset-ok   true
             :subvec-ok   true
             :wildcard-ok false
             :pred-fn-ok  false
             :pattern     smaller
             :values      [larger]}]
    (wild-match? ctx)))

(defn wild-submatch? ; #todo readme & test
  "Simple wrapper for wild-match? where all types of sub-matching are enabled."
  [pattern & values]
  (let [ctx {:submap-ok   true
             :subset-ok   true
             :subvec-ok   true
             :wildcard-ok true
             :pred-fn-ok  true
             :pattern     pattern
             :values      values}]
    (wild-match? ctx)))

(s/defn wild-item? :- s/Bool
  "Returns true if any element in a nested collection is the wildcard :*"
  [item :- s/Any]
  (has-some? #(= :* %) (unnest [item])))

(defn ^:no-doc set-match-impl
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


; #todo add test & README
(defn pretty
  "Shortcut for (clojure.pprint/pprint (unlazy-pretty data))."
  [data] (pprint/pprint (unlazy-pretty data)))

; #todo add test & README
(defn pretty-str
  "Returns a string that is the result of tupelo.core/pretty"
  [data] (with-out-str (pretty data)))

(def ^:no-doc ^:dynamic *walk-with-parents-readonly-flag* false) ; assumes not in readonly mode
(s/defn ^:no-doc walk-with-parents-impl :- s/Any
  [parents :- tsk/Vec
   data-in :- s/Any
   intc :- tsk/KeyMap] ; #todo {s/Keyword s/fn-schema}
  ; ensure data-in does not contain any MapEntry of ListEntry objects
  (when (or (map-entry? data-in) (list-entry? data-in))
    (throw (ex-info "User-level MapEntry and/or list-entry objects not allowed" (vals->map data-in))))
  (let [data-identity-fn        (fn [-parents- data] data)
        enter-fn                (or (:enter intc) data-identity-fn)
        leave-fn                (or (:leave intc) data-identity-fn)
        parents-next            (append parents data-in)
        data-post-enter         (cond-it-> (enter-fn parents data-in)
                                  *walk-with-parents-readonly-flag* data-in)
        data-post-walk-modified (cond
                                  (sequential? data-post-enter) (list-entries->vec
                                                                  (forv [listentry (list->entries data-post-enter)]
                                                                    (let [parents-next-le (append parents-next listentry)]
                                                                      (list-entry (grab :idx listentry)
                                                                                  (walk-with-parents-impl parents-next-le (grab :val listentry) intc)))))

                                  (map? data-post-enter) (into {}
                                                               (forv [mapentry data-post-enter]
                                                                 (let [me-key           (key mapentry)
                                                                       me-val           (val mapentry)
                                                                       parents-next-me  (append parents-next mapentry)
                                                                       parents-next-key (append parents-next-me {:type :map-key :value me-key})
                                                                       parents-next-val (append parents-next-me {:type :map-val :value me-val})]
                                                                   (map-entry
                                                                     (walk-with-parents-impl parents-next-key me-key intc)
                                                                     (walk-with-parents-impl parents-next-val me-val intc)))))

                                  (set? data-post-enter) (into #{}
                                                               (forv [elem data-post-enter]
                                                                 (walk-with-parents-impl parents-next elem intc)))

                                  ; otherwise, return data-in unaltered
                                  :else data-post-enter)

        data-post-walk          (cond-it-> data-post-walk-modified
                                  *walk-with-parents-readonly-flag* data-in)

        data-post-leave         (cond-it-> (leave-fn parents data-post-walk)
                                  *walk-with-parents-readonly-flag* data-in)]
    data-post-leave))

(s/defn walk-with-parents :- s/Any
  "Performs a depth-first traversal of a data structure, using an interceptor with signature:

      {:enter (fn [parents data] ...)
       :leave (fn [parents data] ...) }

   For each data node in the tree, the `:enter` function is called prior to walking
   the subtree rooted at that element, and the `:leave` function is called after
   walking the subtree. The result of each function replaces the data value.

   The `parents` arg to each interceptor function is a vector of elements from the
   root data value passed in.  Using dummy (i.e. noop) interceptors which simply
   print their args as a map, we have this example:

   Clojure maps & vectors/lists have special processing.  They are broken up into a sequence of
   MapEntry/ListEntry elements, which are included in the :parents vector before walking the child
   data values. In this way, a map val can easily determine its correspond key or vice versa, and a
   vector/list/seq element can easily determine its index.

         (walk-with-parents  {:a 1 :b {:c 3}}}  <noop-intc>) =>

             :enter => {:parents [],                                                       :data {:a 1, :b {:c 3}}}
             :enter => {:parents [{:a 1, :b {:c 3}} [:a 1]],                               :data :a}
             :leave => {:parents [{:a 1, :b {:c 3}} [:a 1]],                               :data :a}
             :enter => {:parents [{:a 1, :b {:c 3}} [:a 1]],                               :data 1}
             :leave => {:parents [{:a 1, :b {:c 3}} [:a 1]],                               :data 1}
             :enter => {:parents [{:a 1, :b {:c 3}} [:b {:c 3}]],                          :data :b}
             :leave => {:parents [{:a 1, :b {:c 3}} [:b {:c 3}]],                          :data :b}
             :enter => {:parents [{:a 1, :b {:c 3}} [:b {:c 3}]],                          :data {:c 3}}
             :enter => {:parents [{:a 1, :b {:c 3}} [:b {:c 3}] {:c 3} [:c 3]],            :data :c}
             :leave => {:parents [{:a 1, :b {:c 3}} [:b {:c 3}] {:c 3} [:c 3]],            :data :c}
             :enter => {:parents [{:a 1, :b {:c 3}} [:b {:c 3}] {:c 3} [:c 3]],            :data 3}
             :leave => {:parents [{:a 1, :b {:c 3}} [:b {:c 3}] {:c 3} [:c 3]],            :data 3}
             :leave => {:parents [{:a 1, :b {:c 3}} [:b {:c 3}]],                          :data {:c 3}}
             :leave => {:parents [],                                                       :data {:a 1, :b {:c 3}}}

             NOTE: in above, items in the :parents like `[:a 1]` are #clojure.lang.MapEntry values.

         (walk-with-parents  [10 [20 21]]  <noop-intc>) =>

             :enter => {:parents [],
                        :data [10 [20 21]]}
             :enter => {:parents [[10 [20 21]] #t.c.ListEntry{:index 0, :value 10}],
                        :data 10}
             :enter => {:parents [[10 [20 21]] #t.c.ListEntry{:index 1, :value [20 21]}],
                        :data [20 21]}
             :enter => {:parents [[10 [20 21]] #t.c.ListEntry{:index 1, :value [20 21]} [20 21] #t.c.ListEntry{:index 0, :value 20}],
                        :data 20}
             :enter => {:parents [[10 [20 21]] #t.c.ListEntry{:index 1, :value [20 21]} [20 21] #t.c.ListEntry{:index 1, :value 21}],
                        :data 21}

       NOTE: in above, `#t.c.ListEntry` stands for `#tupelo.core.ListEntry`, an analog of #clojure.lang.MapEntry
  "
  [data :- s/Any
   interceptor :- tsk/KeyMap]
  (let [enter-fn (:enter interceptor) ; may be nil
        leave-fn (:leave interceptor)] ; may be nil
    (when (and (nil? enter-fn) (nil? leave-fn))
      (throw (ex-info "Invalid interceptor. :enter and :leave functions cannot both be nil." (vals->map interceptor))))
    ; ensure data does not contain any MapEntry of ListEntry objects
    ;(walk/postwalk (s/fn [data]
    ;                 (with-result data
    ;                   (if (or (map-entry? data)
    ;                         (list-entry? data))
    ;                     (throw (ex-info "User-level MapEntry and/or list-entry objects not allowed" (vals->map data))))))
    ;  data)
    (walk-with-parents-impl [] data interceptor)))

(s/defn walk-with-parents-readonly :- s/Any
  "Walks a data structure as with `walk-with-parents`, but in a read-only mode
  (interceptor function return values are ignored). Use for side-effects
  such as printing or validation (throw Exception to indicate validation failure).
  Returns input value (can be used for chaining). "
  [data :- s/Any
   intc :- tsk/KeyMap] ;  #todo fix problem with s/fn-schema {s/Keyword s/fn-schema}
  (binding [*walk-with-parents-readonly-flag* true]
    (walk-with-parents data intc)))

;---------------------------------------------------------------------------------------------------
#?(:clj
   (do
     ; #todo add dynamic vars (& test):
     ;   *snipped-sequential-leaders* (default 2)
     ;   *snipped-sequential-trailers* (default 1)
     ;   *snipped-map-leaders* (default 2)
     ;   *snipped-map-trailers* (default 1)

     (def SNIP-TOKEN :<----------snip----------->)

     (s/defn ^:no-doc snip-seq-heads :- tsk/List
       [snip-sizes :- [s/Int]
        data-list :- tsk/List]
       (vec         ; always return a vector
         (let [snip-total (apply + snip-sizes)
               data-len   (count data-list)]
           (if (<= data-len snip-total)
             data-list
             (let [num-parts  (count snip-sizes)
                   part-size  (quot data-len num-parts) ; truncates
                   parts      (vec (take num-parts (partition part-size data-list))) ; drop any leftovers due to truncation
                   parts-keep (apply glue
                                     (map-let [part parts
                                               keep-curr snip-sizes]
                                              (append (xtake keep-curr part) SNIP-TOKEN)))]
               parts-keep)))))

     (s/defn ^:no-doc snip-seq-tail :- tsk/List
       [keep-tail :- s/Int
        data-list :- tsk/List]
       (vec         ; always return a vector
         (let [data-num (count data-list)]
           (if (<= data-num keep-tail)
             data-list
             (take-last keep-tail data-list)))))

     (s/defn ^:no-doc snip-seq :- tsk/List
       [snip-sizes :- [s/Int]
        data-list :- tsk/List]
       (vec         ; always return a vector
         (let [num-snips (count snip-sizes)]
           (assert (pos? num-snips))
           (assert (every? int-pos? snip-sizes))
           (if (= 1 num-snips)
             (snip-seq-heads snip-sizes data-list)
             (let [snip-total (apply + snip-sizes)]
               (if (<= (count data-list) snip-total)
                 data-list
                 (let [snip-size-tail  (xlast snip-sizes)
                       snipped-tail    (snip-seq-tail snip-size-tail data-list)

                       snip-sizes-main (butlast snip-sizes)
                       data-main       (drop-last snip-size-tail data-list)
                       snipped-main    (snip-seq-heads snip-sizes-main data-main)
                       result          (glue snipped-main snipped-tail)]
                   result)))))))

     ; *****  Must use this function to turn off `#ordered/set (...)` print result!!! (or `spyx-pretty` or `pprint`)  *****
     (defn coerce-flatland-ordered->normal-print!
       " ***** Will disable the custom printing like `#ordered/set (...)`  "
       []
       (remove-method print-method flatland.ordered.map.OrderedMap)
       (remove-method print-method flatland.ordered.set.OrderedSet))

     (def SnipCtx {:snip-sizes [s/Int]
                   :data       s/Any})

     ; #todo - make recursive
     (s/defn ^:no-doc snip-impl :- s/Any
       [ctx :- SnipCtx]
       (with-map-vals ctx [snip-sizes data]
         (with-nil-default data ; return unchanged if no match
                           (cond
                             (sequential? data) (snip-seq snip-sizes (seq data)) ; coerce to a seq in case it's something weird

                             (map? data) (let [result-seq  (snip-seq snip-sizes (seq (->sorted-map-generic data)))
                                               parts       (partition-by #(= SNIP-TOKEN %) result-seq)
                                               parts-data  (drop-if #(= [SNIP-TOKEN] %) parts)
                                               parts-snip  (forv [idx (range (count parts-data))]
                                                             [[(str->kw (format "<snip-key-%d>" idx))
                                                               (str->kw (format "<snip-val-%d>" idx))]])
                                               parts-fused (drop-last (interleave parts-data parts-snip))
                                               result      (reduce (fn [accum item]
                                                                     (into accum item))
                                                                   (omap/ordered-map)
                                                                   parts-fused)]
                                           result)

                             (set? data) (let [result-seq  (snip-seq snip-sizes (seq (->sorted-set-generic data)))
                                               parts       (partition-by #(= SNIP-TOKEN %) result-seq)
                                               parts-data  (drop-if #(= [SNIP-TOKEN] %) parts)
                                               parts-snip  (forv [idx (range (count parts-data))]
                                                             [(str->kw (format "<snip-%d>" idx))])
                                               parts-fused (drop-last (interleave parts-data parts-snip))
                                               result      (reduce (fn [accum item]
                                                                     (into accum item))
                                                                   (oset/ordered-set)
                                                                   parts-fused)]
                                           result)))))


     (s/defn snip* :- s/Any
       "Snips a large data structure into a smaller representative snapshot.
       ctx is like:

             {:snip-sizes [4 3] :data data}
       "
       [ctx :- SnipCtx]
       (with-map-vals ctx [snip-sizes data]
         (walk/postwalk (fn [arg]
                          (let [ctx-arg (glue ctx {:data arg})]
                            (snip-impl ctx-arg)))
                        data)))

     (s/defn snip :- s/Any
       "Returns snipped data with defaulting to first 4 and last 3 along each dimension"
       [data :- s/Any]
       (snip* {:snip-sizes [4 3] :data data}))

     ))             ; :clj

; bottom
;***************************************************************************************************
;***************************************************************************************************
;***************************************************************************************************
#?(:clj
   (do

     (ns-unmap *ns* 'first) ; #todo -> (set-tupelo-strict! true/false)
     (ns-unmap *ns* 'second)
     (ns-unmap *ns* 'rest)
     (ns-unmap *ns* 'next)
     (ns-unmap *ns* 'last)

     ;----------------------------------------------------------------------------
     (when-clojure-1-9-plus
       (require
         '[clojure.spec.alpha :as sp]
         '[clojure.spec.gen.alpha :as gen]
         '[clojure.spec.test.alpha :as stest]))


     ; #todo Need safe versions of:
     ; #todo    + - * /  (others?)  (& :strict :safe reassignments)
     ; #todo    and, or    (& :strict :safe reassignments)
     ; #todo    = not=   (others?)  (& :strict :safe reassignments)
     ; #todo    (drop-last N coll)  (take-last N coll)
     ; #todo    subvec
     ; #todo    others???

     (comment
       (is= (merge-deep ; #todo need a merge-deep where
              {:a {:b 2}}
              {:a {:c 3}})
            {:a {:b 2
                 :c 3}}))

     ;-----------------------------------------------------------------------------
     ; clojure.spec stuff
     (when-clojure-1-9-plus
       (sp/def ::anything (sp/spec (constantly true) :gen gen/any-printable))
       (sp/def ::nothing (sp/spec (constantly false)))

       ; #todo how to test the :ret part?
       (sp/fdef truthy?
                :args (sp/cat :arg ::anything)
                :ret boolean?)

       (sp/fdef falsey?
                :args (sp/cat :arg ::anything)
                :ret boolean?
                :fn #(= (:ret %) (not (truthy? (-> % :args :arg))))))

     ; #todo gogo ---------------------------------------------------------------------------------------------------

     ; #todo max-key -> t/max-by

     (s/defn sublist :- tsk/List ; #todo make CLJS version
       "Like clojure.core/subvec, but works for any sequence (remniscent of java.util.List/subList)"
       ([listy :- tsk/List
         idx-low :- s/Int]
        (sublist listy idx-low (count listy)))
       ([listy :- tsk/List
         idx-low :- s/Int
         idx-bound :- s/Int]
        (.subList listy idx-low idx-bound)))

     (defn chan->lazy-seq ; #todo add schema, add tests, readme
       "Accepts a core.async channel and returns the contents as a lazy list."
       [chan]
       (let [curr-item (async/<!! chan)] ; #todo ta/take-now!
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
       "Creates a 'generator function' that returns a lazy seq of results
       via `yield` (a la Python)."
       [& forms]
       `(let [~'lazy-gen-output-buffer (async/chan *lazy-gen-buffer-size*)]
          (async/go
            ~@forms
            (async/close! ~'lazy-gen-output-buffer))
          (chan->lazy-seq ~'lazy-gen-output-buffer)))

     (defmacro yield ; #todo put-now/put-later & dynamic
       "Within a 'generator function' created by `lazy-gen`, populates the
       result lazy seq with the supplied value (a la Python). Returns the value."
       [value]
       `(do
          (async/>! ~'lazy-gen-output-buffer ~value)
          ~value))

     (defmacro yield-all ; #todo maybe pattern after `restruct` and make function + dynamic value???
       "Within a 'generator function' created by `lazy-gen`, populates the
       result lazy seq with each item from the supplied collection. Returns the collection."
       [values]
       `(do
          (doseq [value# ~values]
            (yield value#))
          (vec ~values)))

     ; #todo make replace-in that is like assoc-in but verifies path first !!! (merge with replace-at)

     (defmacro matches?
       "A shortcut to clojure.core.match/match to aid in testing.  Returns true if the data value
        matches the pattern value.  Underscores serve as wildcard values. Usage:

            (matches? pattern & values)

        sample:

            (matches?  [1 _ 3] [1 2 3] )         ;=> true
            (matches?  {:a _ :b _       :c 3}
                       {:a 1 :b [1 2 3] :c 3}
                       {:a 2 :b 99      :c 3}
                       {:a 3 :b nil     :c 3} )  ;=> true

        Note that a wildcald can match either a primitive or a composite value."
       [pattern & values]
       `(and ~@(forv [value values]
                 `(ccm/match ~value
                             ~pattern true
                             :else false))))

     (defn macro?
       "Returns true if a quoted symbol resolves to a macro. Usage:

             (println (macro? 'and))  ;=> true "
       [s]
       (-> s resolve meta :macro boolean))
     ; from Alex Miller StackOverflow answer 2017-5-6

     ; #todo maybe ns-assoc, ns-dissoc, ns-get for intern/ns-unmap

     ; #todo maybe add explicit arg checking
     ; #todo   map->entries, entries->map
     ; #todo   str->chars, chars->str
     ; #todo   set->vec, vec->set
     ; #todo   line-seq et al not lazy (+ tupelo.lazy orig)

     ))

;(defn refer-tupelo  ; #todo delete?
;  "Refer a number of commonly used tupelo.core functions into the current namespace so they can
;   be used without namespace qualification."
;  [& args]
;  (refer 'tupelo.core :only
;   '[
;     not-nil? not-empty? has-some? has-none?
;
;     forv map-let* map-let
;     when-clojure-1-8-plus when-clojure-1-9-plus
;     glue glue-rows
;     macro?
;     append prepend grab dissoc-in fetch fetch-in
;     submap? submap-by-keys submap-by-vals keyvals keyvals-seq validate-map-keys map-keys map-vals
;     validate only it-> keep-if drop-if zip zip* zip-lazy indexed
;     strcat nl pretty pretty-str json->edn edn->json range-vec thru rel= all-rel=
;     drop-at insert-at replace-at idx
;     starts-with? int->kw kw->int
;     xfirst xsecond xthird xfourth xlast xbutlast xrest xreverse
;     kw->sym kw->str str->sym str->kw str->chars sym->kw sym->str
;     split-using split-match partition-using
;     wild-item? submatch? val=
;     increasing? increasing-or-equal? ->vector unwrap xvec
;     fibonacci-seq fibo-thru fibo-nth unnest
;     with-exception-default lazy-cons lazy-gen yield yield-all
;    ] )
;  (let [flags (set args)]
;    (when (contains? flags :dev)
;      ; (refer 'tupelo.core :only '[   ])
;    )
;    (when (contains? flags :strict)
;      ; #todo unlink/relink troublesome clojure.core stuff
;    )))

;---------------------------------------------------------------------------------------------------
; ~/tupelo > lein test :only tupelo.core
; lein test user
; Ran 0 tests containing 0 assertions.     ***** Nearly silent failure *****
; 0 failures, 0 errors.
;
; ~/tupelo > lein test :only tst.tupelo.core
; lein test tst.tupelo.core
; Ran 8 tests containing 44 assertions.     ***** Runs correctly *****
; 0 failures, 0 errors.
;
; ~/tupelo > lein test :only tst.tupelo.core/convj-test
; lein test tst.tupelo.core
; Ran 1 tests containing 3 assertions.
; 0 failures, 0 errors.
;
; #todo make it handle either tst.orig.namespace or orig.namespace-test
; #todo make it a macro to accept unquoted namespace values
