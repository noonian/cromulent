(ns cromulent.bench
  "Throughput fixtures for the core, run the same way on both runtimes:

     clojure -M:bench        jolt -M:bench        (or jolt build, native)

  Inputs come from a small LCG so both runtimes build identical
  e-graphs. Numbers are printed as a table; IDEA.md records them."
  (:require [cromulent.core :as eg]))

(defn- now-ms [] (/ (double (System/nanoTime)) 1e6))

(defn- lcg
  "A deterministic stream: (lcg seed) returns a fn of no args yielding
  the next number in [0, 32768). The classic ANSI C rand(): state
  s' = (1103515245·s + 12345) mod 2^31, full period by Hull–Dobell,
  and the value is the top 15 bits (s' div 2^16) because the low bits
  of any power-of-two-modulus LCG cycle with tiny periods. Not a good
  generator, but identical on every runtime, which is what a bench
  needs; `rand-int` cannot be seeded portably."
  [seed]
  (let [state (atom seed)]
    (fn [] (quot (swap! state #(mod (+ (* % 1103515245) 12345) 2147483648)) 65536))))

(def ^:private leaves [:a :b :c :d :e 0 1 2 3])
(def ^:private ops [[:+ 2] [:* 2] [:neg 1]])

(defn- rand-term [next! depth]
  (if (or (zero? depth) (< (mod (next!) 4) 1))
    (nth leaves (mod (next!) (count leaves)))
    (let [[op arity] (nth ops (mod (next!) (count ops)))]
      (into [op] (repeatedly arity #(rand-term next! (dec depth)))))))

(defn- timed [f]
  (let [t0 (now-ms), r (f), t1 (now-ms)]
    [(- t1 t0) r]))

(defn add-terms
  "Add n random terms of depth <= d."
  [n d]
  (let [next! (lcg 42)
        terms (vec (repeatedly n #(rand-term next! d)))
        [ms g] (timed #(reduce (fn [g t] (first (eg/add g t))) (eg/egraph) terms))]
    {:fixture "add-terms" :n n :ms ms :nodes (eg/node-count g) :classes (eg/class-count g) :egraph g}))

(defn union-rebuild
  "u random unions on g, then one rebuild."
  [g u]
  (let [next! (lcg 7)
        n (:next-id g)
        pairs (vec (repeatedly u (fn [] [(mod (next!) n) (mod (next!) n)])))
        [ms-u g] (timed #(reduce (fn [g [a b]] (first (eg/union g a b))) g pairs))
        [ms-r g] (timed #(eg/rebuild g))]
    {:fixture "union+rebuild" :n u :ms (+ ms-u ms-r) :union-ms ms-u :rebuild-ms ms-r
     :nodes (eg/node-count g) :classes (eg/class-count g)}))

(defn chain
  "A left-nested sum of n atoms; union every atom with the first, so
  the whole chain collapses through congruence in one rebuild."
  [n]
  (let [atoms (mapv #(keyword (str "a" %)) (range n))
        t (reduce (fn [acc a] [:+ acc a]) (first atoms) (rest atoms))
        [g _] (eg/add (eg/egraph) t)
        [g a0] (eg/add g (first atoms))
        [ms-u g] (timed #(reduce (fn [g a] (first (eg/union g a0 (second (eg/add g a))))) g (rest atoms)))
        [ms-r g] (timed #(eg/rebuild g))]
    {:fixture "chain-collapse" :n n :ms (+ ms-u ms-r) :union-ms ms-u :rebuild-ms ms-r
     :nodes (eg/node-count g) :classes (eg/class-count g)}))

(defn- row [{:keys [fixture n ms nodes classes]}]
  (println (format "%-16s n=%-7d %8.1f ms   nodes=%-7d classes=%d" fixture n (double ms) nodes classes)))

(defn -main [& _]
  (println "cromulent bench")
  (let [a (add-terms 20000 4)]
    (row a)
    (row (union-rebuild (:egraph a) 2000)))
  (row (chain 2000))
  (System/exit 0))
