(ns cromulent.bench
  "Throughput fixtures for the core, run the same way on both runtimes:

     clojure -M:bench        jolt -M:bench        (or jolt build, native)

  Inputs come from a small LCG so both runtimes build identical
  e-graphs. Numbers are printed as a table; IDEA.md records them."
  (:require [cromulent.core :as eg]
            [cromulent.extract :as ex]
            [cromulent.pattern :as pat]
            [cromulent.platform :as platform]
            [cromulent.rewrite :as rw]))

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
  (let [t0 (platform/now-ms), r (f), t1 (platform/now-ms)]
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

(defn ematch
  "Match pattern p against g."
  [g label p]
  (let [[ms matches] (timed #(pat/ematch g p))]
    {:fixture (str "ematch " label) :n (count matches) :ms ms
     :nodes (eg/node-count g) :classes (eg/class-count g)}))

(def egg-rules
  "The rule set of egg's README."
  [(rw/rule "commute-add" '[:+ ?a ?b] '[:+ ?b ?a])
   (rw/rule "commute-mul" '[:* ?a ?b] '[:* ?b ?a])
   (rw/rule "add-0" '[:+ ?a 0] '?a)
   (rw/rule "mul-0" '[:* ?a 0] 0)
   (rw/rule "mul-1" '[:* ?a 1] '?a)])

(def ac-rules
  [(rw/rule "comm" '[:+ ?a ?b] '[:+ ?b ?a])
   (rw/rule "assoc" '[:+ [:+ ?a ?b] ?c] '[:+ ?a [:+ ?b ?c]])])

(defn embiggen
  "Run rules on g under opts."
  [g label rules opts]
  (let [[ms res] (timed #(rw/embiggen g rules opts))
        g (:egraph res)]
    {:fixture (str "embiggen " label) :n (:iterations res) :ms ms
     :nodes (eg/node-count g) :classes (eg/class-count g) :stop (:stop-reason res)}))

(defn ac-sum
  "Saturate a sum of n atoms under commutativity and associativity:
  experiment 1 of ../design/ac-problem.md, the baseline the AC work
  is measured against. Expect 2^n - 1 classes and 3^n - 2^(n+1) + 1 + n
  nodes."
  [n]
  (let [atoms (mapv #(keyword (str "a" %)) (range n))
        t (reduce (fn [acc a] [:+ acc a]) (first atoms) (rest atoms))
        [g _] (eg/add (eg/egraph) t)]
    (assoc (embiggen g (str "ac-sum " n) ac-rules {:scheduler :simple :node-limit 1000000 :time-limit-ms 600000})
           :n n)))

(defn extract
  "Cost every class of g under ast-size."
  [g]
  (let [[ms best] (timed #(ex/best-costs g ex/ast-size))]
    {:fixture "extract (all classes)" :n (count (remove nil? best)) :ms ms
     :nodes (eg/node-count g) :classes (eg/class-count g)}))

(defn- row [{:keys [fixture n ms nodes classes stop]}]
  (println (format "%-24s n=%-7d %8.1f ms   nodes=%-7d classes=%-6d %s"
                   fixture n (double ms) nodes classes (if stop (name stop) ""))))

(defn -main [& _]
  (println "cromulent bench")
  (let [a (add-terms 20000 4)
        g (:egraph a)]
    (row a)
    (row (ematch g "[:+ ?a [:* ?b ?c]]" '[:+ ?a [:* ?b ?c]]))
    (row (ematch g "[:+ ?x ?x]" '[:+ ?x ?x]))
    (row (union-rebuild g 2000))
    (row (extract g))
    (row (embiggen g "egg rules, 2 iters" egg-rules {:scheduler :simple :iter-limit 2 :node-limit 1000000})))
  (row (chain 2000))
  (row (ac-sum 7))
  (row (ac-sum 8))
  (row (ac-sum 10))
  (System/exit 0))
