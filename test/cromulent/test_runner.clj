(ns cromulent.test-runner
  "Entry point for `jolt test` / `jolt -M:test` and `clojure -M:test`."
  (:require [clojure.test :as t]
            [cromulent.core-test]
            [cromulent.pattern-test]
            [cromulent.rewrite-test]
            [cromulent.extract-test]))

(defn -main [& _]
  (let [{:keys [fail error]} (t/run-tests 'cromulent.core-test
                                          'cromulent.pattern-test
                                          'cromulent.rewrite-test
                                          'cromulent.extract-test)]
    (System/exit (if (pos? (+ fail error)) 1 0))))
