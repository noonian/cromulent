(ns cromulent.smoke-test
  "The cross-runtime facts of cromulent.smoke, asserted here on the
  JVM and Jolt; orrery's node build asserts the same on ClojureScript."
  (:require [clojure.test :refer [deftest is]]
            [cromulent.smoke :as smoke]))

(deftest the-same-facts-on-this-runtime
  (doseq [c (smoke/checks)]
    (is (:ok? c) (pr-str (dissoc c :ok?)))))
