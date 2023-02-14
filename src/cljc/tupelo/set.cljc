;   Copyright (c) Alan Thompson. All rights reserved.
;   The use and distribution terms for this software are covered by the Eclipse Public License 1.0
;   (http://opensource.org/licenses/eclipse-1.0.php) which can be found in the file epl-v10.html at
;   the root of this distribution.  By using this software in any fashion, you are agreeing to be
;   bound by the terms of this license.  You must not remove this notice, or any other, from this
;   software.
(ns tupelo.set
  "Tupelo - Making Clojure even sweeter"
  (:refer-clojure :exclude [remove])
  (:require
    [clojure.set]
    [schema.core :as s]
    ))

; #todo wrap these functions and throw if non-set argument found!
;-----------------------------------------------------------------------------
; for convenience of requiring only 1 ns
(def difference            clojure.set/difference)
(def index                 clojure.set/index)
(def intersection          clojure.set/intersection)
(def join                  clojure.set/join)
(def map-invert            clojure.set/map-invert)
(def project               clojure.set/project)
(def rename                clojure.set/rename)
(def rename-keys           clojure.set/rename-keys)
(def select                clojure.set/select)
(def subset?               clojure.set/subset?)
(def superset?             clojure.set/superset?)
;-----------------------------------------------------------------------------

(defn union [& args]
  (assert (every? set? args))
  (apply clojure.set/union args))

(s/defn add :- #{s/Any}
  "Adds a value to a set, creating the set if necessary."
  [tgt-set :- (s/maybe #{s/Any})
   & values :- [s/Any]]
  (let [result (or tgt-set #{})]
    (apply clojure.core/conj result values)))

(s/defn remove :- #{s/Any}
  "Removes a values from a set iff present, creating the set if necessary."
  [tgt-set :- (s/maybe #{s/Any})
   & values :- [s/Any]]
  (let [result (or tgt-set #{})]
    (apply clojure.core/disj result values))) ; disj from empty set is a noop

