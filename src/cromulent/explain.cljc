(ns cromulent.explain
  "Explanations: why the e-graph holds two terms equal, as a derivation
  cromulent.derivation checks. Needs an e-graph made with :explain?
  (cromulent.core/egraph), whose journal records every node as it was
  born and every union that merged two classes.

  The unions are the edges of a forest over the node ids (Nieuwenhuis
  and Oliveras; egg's explain), and two ids in one class are joined by
  one path in it. Each edge on the path becomes a step by its reason:

    :congruence   the two nodes have the same operator and children
                  that were equal when the edge was made: a :cong
                  step over the explanations of the children, which use
                  only earlier edges, so the expansion ends
    a rule's      the rule's instance, up to congruence at both ends:
                  the nodes the rule applied to were born with the
                  children their classes had then, not with the terms
                  the bindings name now, and the witnesses the runner
                  recorded say which nodes stand where
    anything else an :asserted step carrying the reason

  An id denotes the term it was born as (`term`). The derivations
  are plain, unshared data: a long run can make a long one (Flatt et al.
  2022, arxiv.org/abs/2209.03398)."
  (:require [cromulent.core :as eg]
            [cromulent.pattern :as pat]
            [cromulent.term :as term]))

(defn- journal [g]
  (or (:journal g)
      (throw (ex-info "no journal: make the e-graph with (egraph {:explain? true})" {}))))

(defn- context [g]
  (let [{:keys [births unions]} (journal g)]
    {:births births
     :unions unions
     ;; id -> [[neighbour edge-index] ...]
     :adj (reduce-kv (fn [m i [a b]]
                       (-> m
                           (update a (fnil conj []) [b i])
                           (update b (fnil conj []) [a i])))
                     {}
                     unions)
     :terms (volatile! {})
     :edges (volatile! {})}))

(defn- term-of [ctx id]
  (or (get @(:terms ctx) id)
      (let [n (nth (:births ctx) id)
            t (if (term/compound? n)
                (term/make (term/operator n) (mapv #(term-of ctx %) (term/children n)))
                n)]
        (vswap! (:terms ctx) assoc id t)
        t)))

(defn term
  "The term id was born as: its node as `add-node` stored it, each child
  the term its child id was born as."
  [g id]
  (term-of (context g) id))

;; ---------------------------------------------------------------------------
;; derivations, kept small as they are built

(defn- refl? [p] (= :refl (nth p 0)))

(defn- sym* [p]
  (case (nth p 0)
    :refl p
    :sym (nth p 1)
    [:sym p]))

(defn- trans* [ps]
  (let [ps (remove nil? ps)
        steps (->> ps
                   (mapcat #(if (= :trans (nth % 0)) (rest %) [%]))
                   (remove refl?))]
    (case (count steps)
      0 (first ps)
      1 (first steps)
      (into [:trans] steps))))

(defn- cong* [op ps]
  (if (every? refl? ps)
    [:refl (term/make op (mapv #(nth % 1) ps))]
    [:cong op (vec ps)]))

;; ---------------------------------------------------------------------------
;; the forest

(defn- path
  "The edges from a to b in the forest, as [from to edge-index]
  triples, or nil when they are not joined."
  [ctx a b]
  (let [adj (:adj ctx)]
    (loop [frontier [a], prev {a nil}]
      (cond
        (contains? prev b)
        (loop [x b, steps ()]
          (if (= x a)
            (vec steps)
            (let [[y i] (get prev x)]
              (recur y (conj steps [y x i])))))

        (empty? frontier) nil

        :else
        (let [[frontier prev]
              (reduce (fn [acc x]
                        (reduce (fn [[f p] [y i]]
                                  (if (contains? p y) [f p] [(conj f y) (assoc p y [x i])]))
                                acc
                                (get adj x)))
                      [[] prev]
                      frontier)]
          (recur frontier prev))))))

(declare edge-derivation)

(defn- between
  "A derivation of: the term a was born as equals the term b was born as."
  [ctx a b]
  (if (= a b)
    [:refl (term-of ctx a)]
    (let [steps (or (path ctx a b)
                    (throw (ex-info "no explanation: the journal does not join these ids" {:a a :b b})))]
      (trans* (mapv (fn [[x _ i]]
                      (let [[ea _ :as edge] (nth (:unions ctx) i)
                            p (edge-derivation ctx i edge)]
                        (if (= x ea) p (sym* p))))
                    steps)))))

(defn- subst [p sigma]
  (cond
    (pat/variable? p) (get sigma p)
    (term/compound? p) (term/make (term/operator p) (mapv #(subst % sigma) (term/children p)))
    :else p))

(defn- instance-derivation
  "A derivation of: the term n was born as equals pattern p's instance under
  the bindings, w being p's witness."
  [ctx n p w]
  (if (term/compound? p)
    (let [nid (nth w 0)
          born (nth (:births ctx) nid)]
      (trans* [(between ctx n nid)
               (cong* (term/operator p)
                      (mapv (fn [c pc wc] (instance-derivation ctx c pc wc))
                            (term/children born) (term/children p) (subvec w 1)))]))
    ;; a variable's witness is its binding, a leaf's its node
    (between ctx n w)))

(defn- rule-derivation [ctx a b {:keys [rule lhs rhs bindings lhs-witness rhs-witness computed?]}]
  (let [sigma (into {} (map (fn [[v id]] [v (term-of ctx id)])) bindings)
        left (when lhs-witness (instance-derivation ctx a lhs lhs-witness))
        right (when rhs-witness (instance-derivation ctx b rhs rhs-witness))
        l (if lhs-witness (subst lhs sigma) (term-of ctx a))
        r (if rhs-witness (subst rhs sigma) (term-of ctx b))]
    (trans* [left
             (if (or computed? (nil? lhs-witness) (nil? rhs-witness))
               [:computed rule l r]
               [:rule rule (select-keys sigma (pat/variables lhs))])
             (when right (sym* right))])))

(defn- edge-derivation
  "A derivation of the equation edge i records, from its first id to its
  second."
  [ctx i [a b reason]]
  (or (get @(:edges ctx) i)
      (let [p (cond
                (= :congruence reason)
                (let [na (nth (:births ctx) a), nb (nth (:births ctx) b)]
                  (cong* (term/operator na)
                         (mapv #(between ctx %1 %2) (term/children na) (term/children nb))))

                (and (map? reason) (contains? reason :rule))
                (rule-derivation ctx a b reason)

                :else [:asserted (term-of ctx a) (term-of ctx b) reason])]
        (vswap! (:edges ctx) assoc i p)
        p)))

;; ---------------------------------------------------------------------------
;; the questions

(defn explain
  "A derivation of: the terms ids a and b were born as are equal, or nil
  when they are in different classes. g must have a journal."
  [g a b]
  (let [ctx (context g)]
    (when (= (eg/find g a) (eg/find g b))
      (between ctx a b))))

(defn- locate
  "[id d] for ground term t in g: id a node whose class holds t,
  d a derivation of: t equals the term id was born as."
  [ctx g t]
  (if (term/compound? t)
    (let [kids (mapv #(locate ctx g %) (term/children t))
          nid (or (eg/node-id g (term/make (term/operator t) (mapv #(eg/find g (nth % 0)) kids)))
                  (throw (ex-info "term not in the e-graph" {:term t})))
          born (nth (:births ctx) nid)]
      [nid (cong* (term/operator t)
                  (mapv (fn [[cid p] c] (trans* [p (between ctx cid c)]))
                        kids (term/children born)))])
    [(or (eg/node-id g t) (throw (ex-info "term not in the e-graph" {:term t})))
     [:refl t]]))

(defn explain-terms
  "A derivation of: ground terms s and t are equal, or nil when g does not
  hold them equal. Both must be in g, which must be rebuilt and have a
  journal."
  [g s t]
  (let [ctx (context g)
        [a ps] (locate ctx g s)
        [b pt] (locate ctx g t)]
    (when (= (eg/find g a) (eg/find g b))
      (trans* [ps (between ctx a b) (sym* pt)]))))
