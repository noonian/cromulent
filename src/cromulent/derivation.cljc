(ns cromulent.derivation
  "A checker for equational derivations, the ones cromulent.explain
  writes. It shares no code with the e-graph: it reads terms through
  cromulent.term and substitutes into patterns itself, so a derivation
  it accepts follows from the rules whatever the e-graph got wrong.

  A derivation is a proof in equational logic with the rules as its
  axioms: it shows that an equation follows from them, not that the
  equation is true, and its trusted steps are hypotheses it rests on.
  It is called a derivation and not a proof so that the word proof
  stays free for a kernel's (ideas/explanations.md, section 4).

  A derivation is data, and derives an equation between two terms:

    [:refl t]                 t = t
    [:sym d]                  b = a, when d derives a = b
    [:trans d1 ... dn]        a = c, each di's right side the next's left
    [:cong op [d1 ... dk]]    op(a1 ... ak) = op(b1 ... bk), di deriving ai = bi
    [:rule name sigma]        lhs[sigma] = rhs[sigma] for the rule of that name,
                              sigma a map from its variables to terms
    [:computed name s t]      s = t, by a rule whose right-hand side was
                              computed, or a searcher's: trusted
    [:asserted s t reason]    s = t, asserted by a caller or an analysis: trusted

  The checker confirms that a derivation follows from the rules and the
  trusted steps; it never judges whether a rule is true. A rule with a
  guard is checked as its two sides and reported as trusted, since its
  guard is not checked."
  (:require [cromulent.term :as term]))

(defn- variable? [x]
  (and (symbol? x)
       (let [n (name x)]
         (and (< 1 (count n)) (= \? (nth n 0))))))

(defn- subst
  "Pattern p with every variable replaced by its term in sigma."
  [p sigma]
  (cond
    (variable? p) (if (contains? sigma p)
                    (get sigma p)
                    (throw (ex-info "unbound variable" {:variable p})))
    (term/compound? p) (term/make (term/operator p) (mapv #(subst % sigma) (term/children p)))
    :else p))

(defn- by-name [rules]
  (if (map? rules) rules (into {} (map (juxt :name identity)) rules)))

(defn- fail [path step problem & {:as more}]
  (throw (ex-info problem (merge {::invalid true :path path :step step :problem problem} more))))

(defn- conclude
  "[a b], the equation step derives. Trusted steps are added to
  trusted, a volatile vector. path is where step sits in the derivation."
  [step rules trusted path]
  (when-not (and (vector? step) (keyword? (first step)))
    (fail path step "not a derivation step"))
  (case (nth step 0)
    :refl [(nth step 1) (nth step 1)]

    :sym (let [[a b] (conclude (nth step 1) rules trusted (conj path 1))] [b a])

    :trans
    (let [eqs (map-indexed (fn [i p] (conclude p rules trusted (conj path (inc i)))) (subvec step 1))]
      (when (empty? eqs) (fail path step "an empty chain"))
      (reduce (fn [[a b] [i [c d]]]
                (if (= b c)
                  [a d]
                  (fail (conj path (inc i)) (nth step (inc i)) "does not start where the chain left off"
                        :expected b :found c)))
              (first eqs)
              (map vector (range 1 (count eqs)) (rest eqs))))

    :cong
    (let [[_ op ps] step
          eqs (map-indexed (fn [i p] (conclude p rules trusted (conj path 2 i))) ps)]
      [(term/make op (mapv first eqs)) (term/make op (mapv second eqs))])

    :rule
    (let [[_ name sigma] step
          r (get rules name)]
      (cond
        (nil? r) (fail path step "no rule of that name" :rule name)
        (or (fn? (:lhs r)) (not (some? (:rhs r))) (fn? (:rhs r)))
        (fail path step "the rule is not a pattern on both sides; its steps are :computed" :rule name))
      (when (:when r) (vswap! trusted conj {:guard name :sigma sigma}))
      (try
        [(subst (:lhs r) sigma) (subst (:rhs r) sigma)]
        (catch #?(:clj Exception :default :default) e
          (fail path step (ex-message e) :rule name))))

    :computed
    (let [[_ name s t] step]
      (when-not (contains? rules name) (fail path step "no rule of that name" :rule name))
      (vswap! trusted conj {:computed name :lhs s :rhs t})
      [s t])

    :asserted
    (let [[_ s t reason] step]
      (vswap! trusted conj {:asserted reason :lhs s :rhs t})
      [s t])

    (fail path step "not a derivation step")))

(defn check
  "Check derivation d against rules (a sequence of rule maps, as
  cromulent.rewrite builds them, or a map from name to rule).
  {:ok? true :lhs a :rhs b :trusted [...]} when d derives a = b, the
  steps taken on trust listed; {:ok? false :path [...] :step s
  :problem \"...\"} naming the first step that does not follow, path
  the indexes that lead to it from d."
  [d rules]
  (let [trusted (volatile! [])]
    (try
      (let [[a b] (conclude d (by-name rules) trusted [])]
        {:ok? true :lhs a :rhs b :trusted @trusted})
      (catch #?(:clj Exception :default :default) e
        (if (::invalid (ex-data e))
          (assoc (dissoc (ex-data e) ::invalid) :ok? false)
          (throw e))))))

(defn derives?
  "Does d derive a = b from rules?"
  [d rules a b]
  (let [{:keys [ok? lhs rhs]} (check d rules)]
    (and ok? (= a lhs) (= b rhs))))
