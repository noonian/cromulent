(ns cromulent.rewrite
  "Rewrites and the equality-saturation runner.

  A rewrite is a map:

    {:name \"mul-2-to-shift\"
     :lhs  '[:* ?a 2]               ; a pattern, or a searcher
                                    ; (fn [eg] [{:class id :bindings {?a id ...}} ...])
     :rhs  '[:<< ?a 1]              ; a pattern over the lhs variables, or
                                    ; (fn [eg bindings] pattern-or-nil)
     :when (fn [eg bindings] bool)} ; optional guard

  `rule` and `bidirectional` build them. A searcher in place of the
  left-hand pattern is egg's Searcher as a function: it may find its
  matches any way it likes, such as by reading analysis data, and its
  bindings feed the right-hand side exactly as a pattern's would. A
  computed :rhs returns a pattern that is instantiated under the same
  bindings, or nil to decline the match; that is how a rule folds
  constants or consults analysis data. A searcher's match may also
  carry its own :rhs, a pattern over its bindings, which takes
  precedence over the rule's: one rule can then say a different thing
  about every class (bendix's normal-form rules), and such a rule
  passes nil as its :rhs.

  Both the guard and a computed :rhs see the e-graph as it was when
  the iteration's search ran, not the one being built by the other
  applications of the same iteration, so an iteration's result does
  not depend on the order of rules or matches.

  `embiggen` (alias `saturate`) runs iterations of egg's phases:
  search every rule against the same e-graph, apply every match
  (instantiate the right-hand side, union it with the matched class),
  rebuild, then decide whether to stop. It stops when saturated (no
  union changed the partition and the scheduler has nothing held
  back) or when it hits an iteration, node or time limit.

  Schedulers decide which of a rule's matches an iteration applies.
  `simple-scheduler` applies them all; `backoff-scheduler` is egg's:
  a rule whose match count exceeds its budget is banned for a number
  of iterations, and both the budget and the ban double each time it
  happens. A scheduler is a map of three functions, so the AC
  experiments can supply their own."
  (:require [cromulent.core :as eg]
            [cromulent.pattern :as pat]))

;; ---------------------------------------------------------------------------
;; rules

(defn rule
  "A rewrite from lhs to rhs. lhs is a pattern or a searcher
  (fn [eg] matches). rhs is a pattern whose variables all occur in
  lhs, or (fn [eg bindings] pattern-or-nil), or nil when every match
  of a searcher carries its own :rhs. Options: :when, a guard
  (fn [eg bindings] bool)."
  [name lhs rhs & {guard :when}]
  (when-not (or (fn? rhs) (fn? lhs))
    (let [unbound (remove (pat/variables lhs) (pat/variables rhs))]
      (when (seq unbound)
        (throw (ex-info "rhs variables not bound by lhs"
                        {:rule name :lhs lhs :rhs rhs :unbound (set unbound)})))))
  (cond-> {:name name :lhs lhs :rhs rhs}
    guard (assoc :when guard)))

(defn bidirectional
  "Two rewrites, lhs => rhs named name and rhs => lhs named name-rev.
  Both sides must be patterns over the same variables."
  [name lhs rhs]
  [(rule name lhs rhs)
   (rule (str name "-rev") rhs lhs)])

;; ---------------------------------------------------------------------------
;; schedulers
;;
;; {:init     (fn [rules opts] state)
;;  :search   (fn [state iter rule search-thunk] [state' matches])
;;  :can-stop (fn [state iter] [state' bool])
;;  :report   (fn [state iter] map)}          ; optional; merged into the iteration's stats

(def simple-scheduler
  "Every match of every rule, every iteration."
  {:init (fn [_ _] nil)
   :search (fn [state _ _ search] [state (search)])
   :can-stop (fn [state _] [state true])})

(defn backoff-scheduler
  "egg's BackoffScheduler. A rule whose matches in one iteration exceed
  match-limit (times 2 for every previous ban) is banned for ban-length
  iterations (times 2 for every previous ban) and its matches are
  dropped. Saturation is only declared when no rule is banned; if one
  is, the bans are shortened so the earliest expires and the run goes
  on."
  [{:keys [match-limit ban-length] :or {match-limit 1000 ban-length 5}}]
  {:init (fn [_ _] {})
   :search (fn [state iter rule search]
             (let [name (:name rule)
                   {:keys [banned-until times-banned]
                    :or {banned-until 0 times-banned 0}} (get state name)]
               (if (< iter banned-until)
                 [state []]
                 (let [ms (search)]
                   (if (> (count ms) (bit-shift-left match-limit times-banned))
                     [(assoc state name {:banned-until (+ iter (bit-shift-left ban-length times-banned))
                                         :times-banned (inc times-banned)})
                      []]
                     [state ms])))))
   :can-stop (fn [state iter]
               (let [banned (filter (fn [[_ s]] (> (:banned-until s) iter)) state)]
                 (if (empty? banned)
                   [state true]
                   (let [delta (- (reduce min (map (comp :banned-until val) banned)) iter)]
                     [(reduce (fn [st [n s]] (assoc st n (update s :banned-until - delta)))
                              state
                              banned)
                      false]))))
   :report (fn [state iter]
             {:banned (into #{} (keep (fn [[n s]] (when (> (:banned-until s) iter) n))) state)})})

(defn- resolve-scheduler [s opts]
  (case s
    :simple simple-scheduler
    :backoff (backoff-scheduler opts)
    (if (map? s)
      s
      (throw (ex-info "unknown scheduler" {:scheduler s})))))

;; ---------------------------------------------------------------------------
;; the runner

(defn- now-ms [] (/ (double (System/nanoTime)) 1e6))

(defn- search-rule
  "Every match of rule in g."
  [g {:keys [lhs]}]
  (if (fn? lhs) (lhs g) (pat/ematch g lhs)))

(defn- apply-rule
  "Apply every match of rule to g. snapshot is the e-graph the matches
  were found in, which is what the guard and a computed rhs see.
  Returns [g' n-applied], counting only matches whose union merged two
  classes. A match carrying :rhs supplies its own right-hand side. An
  exception raised while applying (an analysis refusing a
  merge, say) is rethrown with the rule's name and the match in its
  data."
  [snapshot g rule matches]
  (let [{:keys [rhs], guard :when} rule]
    (reduce (fn [[g n] {:keys [class bindings] :as m}]
              (try
                (if (and guard (not (guard snapshot bindings)))
                  [g n]
                  (let [p (cond
                            (contains? m :rhs) (:rhs m)
                            (fn? rhs) (rhs snapshot bindings)
                            :else rhs)]
                    (if (nil? p)
                      [g n]
                      (let [[g id] (pat/instantiate g p bindings)]
                        (if (= (eg/find g id) (eg/find g class))
                          [g n]
                          [(first (eg/union g id class)) (inc n)])))))
                (catch Exception e
                  (throw (ex-info (str "rule " (:name rule) " failed: " (ex-message e))
                                  (assoc (or (ex-data e) {}) :rule (:name rule) :match m)
                                  e)))))
            [g 0]
            matches)))

(defn- check-rules [rules]
  (let [names (map :name rules)]
    (when (not= (count names) (count (set names)))
      (throw (ex-info "rule names must be distinct" {:names names})))
    (doseq [r rules]
      (when-not (and (contains? r :lhs) (contains? r :rhs))
        (throw (ex-info "not a rule" {:rule r}))))))

(defn embiggen
  "Saturate g under rules. Options and their defaults:

    :iter-limit    30       iterations
    :node-limit    10000    stop once the e-graph has more nodes than this
    :time-limit-ms 5000
    :scheduler     :backoff | :simple | a scheduler map
    :match-limit   1000     backoff: matches per rule per iteration
    :ban-length    5        backoff: iterations
    :timeline?     false    keep the e-graph after every iteration
    :check         nil      (fn [g] problem-or-nil): a dev-mode oracle run on the
                            rebuilt e-graph after each rule's applications;
                            a problem throws ex-info naming the rule

  Returns {:egraph g' :iterations n :stop-reason r :stats [...] :ms t}
  where r is :saturated, :iter-limit, :node-limit or :time-limit and
  each entry of :stats is
  {:iter i :nodes n :classes m :matches {name k} :applied {name k}
   :search-ms :apply-ms :rebuild-ms} plus whatever the scheduler
  reports. With :timeline?, :timeline holds the e-graph before the
  first iteration and after each one."
  ([g rules] (embiggen g rules {}))
  ([g rules {:keys [iter-limit node-limit time-limit-ms scheduler timeline? check]
             :or {iter-limit 30 node-limit 10000 time-limit-ms 5000 scheduler :backoff}
             :as opts}]
   (let [rules (vec rules)
         _ (check-rules rules)
         sched (resolve-scheduler scheduler opts)
         t0 (now-ms)
         g (eg/rebuild g)
         result (fn [g stats timeline reason]
                  (cond-> {:egraph g :iterations (count stats) :stop-reason reason
                           :stats stats :ms (- (now-ms) t0)}
                    timeline? (assoc :timeline timeline)))]
     (loop [g g, state ((:init sched) rules opts), stats [], timeline [g]]
       (let [iter (inc (count stats))]
         (cond
           (> iter iter-limit) (result g stats timeline :iter-limit)
           (> (- (now-ms) t0) time-limit-ms) (result g stats timeline :time-limit)
           :else
           (let [t-search (now-ms)
                 [state found] (reduce (fn [[state found] rule]
                                         (let [[state ms] ((:search sched) state iter rule
                                                           #(search-rule g rule))]
                                           [state (conj found ms)]))
                                       [state []]
                                       rules)
                 t-apply (now-ms)
                 [g' applied] (reduce (fn [[g' applied] [rule ms]]
                                        (let [[g' n] (apply-rule g g' rule ms)
                                              g' (if (and check (pos? n))
                                                   (let [g' (eg/rebuild g')]
                                                     (when-let [problem (check g')]
                                                       (throw (ex-info (str "rule " (:name rule) " failed the check")
                                                                       {:rule (:name rule) :problem problem})))
                                                     g')
                                                   g')]
                                          [g' (assoc applied (:name rule) n)]))
                                      [g {}]
                                      (map vector rules found))
                 t-rebuild (now-ms)
                 g' (eg/rebuild g')
                 t-end (now-ms)
                 nodes (eg/node-count g')
                 stat (merge {:iter iter :nodes nodes :classes (eg/class-count g')
                              :matches (zipmap (map :name rules) (map count found))
                              :applied applied
                              :search-ms (- t-apply t-search)
                              :apply-ms (- t-rebuild t-apply)
                              :rebuild-ms (- t-end t-rebuild)}
                             (when-let [report (:report sched)] (report state iter)))
                 stats (conj stats stat)
                 timeline (if timeline? (conj timeline g') timeline)
                 ;; the scheduler is only asked whether it can stop when
                 ;; nothing was applied, as in egg: that is when backoff
                 ;; releases its bans instead of declaring saturation
                 [state can-stop?] (if (every? zero? (vals applied))
                                     ((:can-stop sched) state iter)
                                     [state false])]
             (cond
               can-stop? (result g' stats timeline :saturated)
               (> nodes node-limit) (result g' stats timeline :node-limit)
               :else (recur g' state stats timeline)))))))))

(def saturate "Alias of `embiggen`." embiggen)
