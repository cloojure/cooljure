;   Copyright (c) Alan Thompson. All rights reserved. 
;   The use and distribution terms for this software are covered by the Eclipse Public
;   License 1.0 (http://opensource.org/licenses/eclipse-1.0.php) which can be found in the
;   file epl-v10.html at the root of this distribution.  By using this software in any
;   fashion, you are agreeing to be bound by the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns cooljure.parse-test
  (:require [cooljure.parse             :as cool-parse]
            [clojure.test               :refer :all] ))

; AWTAWT TODO: copy in other parse fns & tests

(deftest string->number
  (testing "parseLong"
    (is (= 15                              (cool-parse/parseLong "15")))
    (is (= -5                              (cool-parse/parseLong "-5")))
    (is (= 99999                           (cool-parse/parseLong "99999")))
    (is (= 9876543210                      (cool-parse/parseLong "9876543210")))
    (is (thrown? NumberFormatException     (cool-parse/parseLong "98765432109876543210")))
    (is (thrown? NumberFormatException     (cool-parse/parseLong " "))) )

  (testing "parseLong with :or"
    (is (= 15           (cool-parse/parseLong "15"                      :or nil )))
    (is (= -5           (cool-parse/parseLong "-5"                      :or nil )))
    (is (= 99999        (cool-parse/parseLong "99999"                   :or nil )))
    (is (= 9876543210   (cool-parse/parseLong "9876543210"              :or nil )))
    (is (= nil          (cool-parse/parseLong "98765432109876543210"    :or nil )))
    (is (= nil          (cool-parse/parseLong " "                       :or nil ))) 
    (is (= 0            (cool-parse/parseLong "xyz"                     :or 0   ))) 
  )

)
