(ns cromulent.platform
  "What differs per runtime: the clock. The library's only other
  reader conditionals are the exception class in four catch clauses,
  two in cromulent.rewrite and two in cromulent.derivation. :clj is the JVM and Jolt (Jolt's reader features are
  #{:jolt :clj :default}); :default is ClojureScript, in the browser
  or on node. The pattern is catalytic.defaults in catalytic-buffer:
  one file knows the platform, the rest of the library is plain
  Clojure.")

(defn now-ms
  "Milliseconds on a monotonic clock, fractional. Only the difference
  between two readings means anything."
  []
  #?(:clj (/ (double (System/nanoTime)) 1e6)
     :default (js/performance.now)))
