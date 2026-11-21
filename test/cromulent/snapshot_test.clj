(ns cromulent.snapshot-test
  (:require [clojure.edn :as edn]
            [clojure.test :refer [deftest is testing]]
            [clojure.test.check :as tc]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [cromulent.check :as check]
            [cromulent.core :as eg]
            [cromulent.explain :as x]
            [cromulent.extract :as ex]
            [cromulent.gen :as cg]
            [cromulent.rewrite :as rw]
            [cromulent.smoke :as smoke]
            [cromulent.snapshot :as snap]))

(defn- through-edn
  "x written as EDN text and read back."
  [x]
  (edn/read-string (binding [*print-length* nil *print-level* nil] (pr-str x))))

(defn- round-trip [g opts]
  (snap/restore (through-edn (snap/snapshot g)) opts))

(defn- scripted
  "g after the ops of a cromulent.gen script, without the final rebuild,
  so it may have pending work."
  [g ops]
  (reduce (fn [g [op & args]]
            (case op
              :add (first (eg/add g (first args)))
              :union (let [[g a] (eg/add g (first args))
                           [g b] (eg/add g (second args))]
                       (first (eg/union g a b)))
              :rebuild (eg/rebuild g)))
          g ops))

(def ^:private cf {:analyses [smoke/const-fold]})

(deftest the-shape
  (let [[g _] (eg/add (eg/egraph cf) [:+ 1 [:* 2 :x]])
        s (snap/snapshot g)]
    (is (= 1 (:cromulent/snapshot s)))
    (is (= [:const-fold] (:analyses s)))
    (is (not (contains? (:egraph s) :analyses)))
    (is (= g (snap/restore s cf)))
    (is (= g (round-trip g cf)) "through EDN")
    (is (= (eg/egraph) (snap/restore (snap/snapshot (eg/egraph))))
        "no analyses, none needed")))

(deftest round-trips-through-edn
  (testing "any state, analyses on: equal, and rebuild after restore is rebuild before snapshot"
    (is (:pass? (tc/quick-check
                 100
                 (prop/for-all [ops cg/script-gen]
                   (let [g (scripted (eg/egraph cf) ops)
                         g' (round-trip g cf)]
                     (and (= g g')
                          (= (eg/rebuild g) (eg/rebuild g'))
                          (empty? (check/violations (eg/rebuild g'))))))))))
  (testing "a journaled e-graph: the journal travels and explanations read the same"
    (is (:pass? (tc/quick-check
                 50
                 (prop/for-all [ops cg/script-gen]
                   (let [g (eg/rebuild (scripted (eg/egraph {:explain? true}) ops))
                         g' (round-trip g {})
                         ids (range (:next-id g))]
                     (and (= g g')
                          (every? (fn [i] (= (x/explain g i (eg/find g i))
                                             (x/explain g' i (eg/find g' i))))
                                  ids)))))))))

(deftest pending-work-travels
  (let [g (eg/egraph cf)
        [g fa] (eg/add g [:f :a])
        [g fb] (eg/add g [:f :b])
        [g a] (eg/add g :a)
        [g b] (eg/add g :b)
        [g _] (eg/union g a b)
        g' (round-trip g cf)]
    (is (:dirty? g'))
    (is (not= (eg/find g' fa) (eg/find g' fb)) "congruence not yet restored")
    (let [r (eg/rebuild g')]
      (is (= (eg/find r fa) (eg/find r fb)))
      (is (= (eg/rebuild g) r))
      (is (empty? (check/violations r))))))

(deftest a-saturated-e-graph-is-a-fixture
  (let [[g r] (eg/add (eg/egraph) (smoke/sum-of 5))
        g (:egraph (rw/embiggen g smoke/ac-rules {:scheduler :simple}))
        g' (round-trip g {})]
    (is (= g g'))
    (is (= (ex/extract g r) (ex/extract g' r)))
    (let [[g'' id] (eg/add g' (smoke/sum-of 5))]
      (is (= g' g'') "the hashcons finds the term: nothing added")
      (is (= (eg/find g r) (eg/find g'' id))))))

(deftest refusals
  (let [fn-data {:name :closure
                 :make (fn [_ _ _] (fn [] :not-data))
                 :merge (fn [_ a _] a)}
        atom-state {:name :stateful
                    :make (fn [_ _ _] nil)
                    :merge (fn [_ a _] a)
                    :modify (fn [g _] (assoc-in g [:analysis-state :stateful] (atom 0)))}]
    (testing "an analysis keeping a function in its data is named"
      (let [[g _] (eg/add (eg/egraph {:analysis fn-data}) :a)
            e (try (snap/snapshot g) nil (catch Exception e e))]
        (is (some? e))
        (is (= :closure (:analysis (ex-data e))))
        (is (= [:classes 0 :data :closure] (:path (ex-data e))))))
    (testing "and one keeping an atom as its state"
      (let [[g _] (eg/add (eg/egraph {:analysis atom-state}) :a)
            g (eg/rebuild g)
            e (try (snap/snapshot g) nil (catch Exception e e))]
        (is (= :stateful (:analysis (ex-data e))))
        (is (= [:analysis-state :stateful] (:path (ex-data e))))))
    (testing "a leaf that is not data"
      (let [[g _] (eg/add (eg/egraph) [:f (Object.)])
            e (try (snap/snapshot g) nil (catch Exception e e))]
        (is (some? e))
        (is (nil? (:analysis (ex-data e))))))
    (testing "restore: analyses that do not match, in name or order"
      (let [s (snap/snapshot (eg/egraph cf))]
        (is (thrown? Exception (snap/restore s)))
        (is (thrown? Exception (snap/restore s {:analyses [smoke/const-fold fn-data]})))
        (is (thrown? Exception (snap/restore (snap/snapshot (eg/egraph {:analyses [smoke/const-fold fn-data]}))
                                             {:analyses [fn-data smoke/const-fold]})))))
    (testing "restore: another version, or not a snapshot"
      (let [s (snap/snapshot (eg/egraph))]
        (is (thrown? Exception (snap/restore (assoc s :cromulent/snapshot 2))))
        (is (thrown? Exception (snap/restore (dissoc s :egraph))))
        (is (thrown? Exception (snap/restore (eg/egraph))))))))

;; ---------------------------------------------------------------------------
;; runs

(defn- step-n [run k]
  (loop [run run, k k]
    (if (or (zero? k) (:stop-reason run)) run (recur (rw/step run) (dec k)))))

(defn- run-out [run]
  (rw/finish (loop [run run] (if (:stop-reason run) run (recur (rw/step run))))))

(defn- untimed [stats]
  (mapv #(dissoc % :search-ms :apply-ms :rebuild-ms) stats))

(defn- same-run? [a b]
  (and (= (:egraph a) (:egraph b))
       (= (:stop-reason a) (:stop-reason b))
       (= (:iterations a) (:iterations b))
       (= (untimed (:stats a)) (untimed (:stats b)))))

(deftest resuming-is-the-same-run
  (is (:pass? (tc/quick-check
               60
               (prop/for-all [ts cg/terms-gen
                              rules cg/rules-gen
                              k (gen/choose 0 6)
                              scheduler (gen/elements [:simple :backoff])]
                 (let [g (:egraph (cg/add-terms (eg/egraph cf) ts))
                       opts {:scheduler scheduler :match-limit 8 :ban-length 2
                             :iter-limit 10 :node-limit 400 :time-limit-ms 60000}
                       straight (rw/embiggen g rules opts)
                       saved (through-edn (snap/snapshot-run (step-n (rw/start g rules opts) k)))
                       resumed (run-out (snap/restore-run saved rules (merge opts cf)))]
                   (same-run? straight resumed)))))))

(deftest resuming-the-blowup-after-every-iteration
  ;; random rules mostly saturate in an iteration or two; this run takes
  ;; seven, and under backoff it bans and releases rules on the way
  (let [[g _] (eg/add (eg/egraph) (smoke/sum-of 5))]
    (doseq [opts [{:scheduler :simple}
                  {:scheduler :backoff :match-limit 4 :ban-length 2}]]
      (let [straight (rw/embiggen g smoke/ac-rules opts)]
        (when (= :backoff (:scheduler opts))
          (is (some (comp seq :banned) (:stats straight))))
        (doseq [k (range (inc (:iterations straight)))]
          (let [saved (through-edn (snap/snapshot-run (step-n (rw/start g smoke/ac-rules opts) k)))]
            (is (same-run? straight (run-out (snap/restore-run saved smoke/ac-rules opts)))
                (str (:scheduler opts) ", snapshot after " k))))))))

(deftest resuming-past-a-limit
  (let [[g r] (eg/add (eg/egraph) (smoke/sum-of 5))
        opts {:scheduler :simple}
        straight (rw/embiggen g smoke/ac-rules opts)
        stopped (step-n (rw/start g smoke/ac-rules (assoc opts :iter-limit 3)) 99)
        saved (through-edn (snap/snapshot-run stopped))]
    (is (= :iter-limit (:stop-reason stopped)))
    (testing "the same limit stops it again, without an iteration"
      (let [again (run-out (snap/restore-run saved smoke/ac-rules (assoc opts :iter-limit 3)))]
        (is (= 3 (:iterations again)))
        (is (= :iter-limit (:stop-reason again)))))
    (testing "a higher one finishes the run"
      (is (same-run? straight (run-out (snap/restore-run saved smoke/ac-rules opts))))
      (is (= {:cost 9 :term [:+ :a0 [:+ :a1 [:+ :a2 [:+ :a3 :a4]]]]}
             (ex/extract (:egraph (run-out (snap/restore-run saved smoke/ac-rules opts))) r))))
    (testing "a node limit that still holds is kept"
      (let [capped (step-n (rw/start g smoke/ac-rules (assoc opts :node-limit 50)) 99)
            saved (through-edn (snap/snapshot-run capped))]
        (is (= :node-limit (:stop-reason capped)))
        (is (same-run? (rw/finish capped)
                       (run-out (snap/restore-run saved smoke/ac-rules (assoc opts :node-limit 50)))))
        (is (same-run? straight (run-out (snap/restore-run saved smoke/ac-rules opts))))))))

(deftest a-run's-timeline
  (let [[g _] (eg/add (eg/egraph) (smoke/sum-of 4))
        opts {:scheduler :simple :timeline? true}
        straight (rw/embiggen g smoke/ac-rules opts)
        saved (through-edn (snap/snapshot-run (step-n (rw/start g smoke/ac-rules opts) 2)))
        resumed (run-out (snap/restore-run saved smoke/ac-rules opts))]
    (is (= 3 (count (:timeline saved))))
    (is (= (:timeline straight) (:timeline resumed)))))

(deftest run-refusals
  (let [[g _] (eg/add (eg/egraph) :a)
        run (rw/start g smoke/ac-rules {:scheduler :simple})
        s (snap/snapshot-run run)]
    (is (thrown? Exception (snap/restore-run s (reverse smoke/ac-rules))) "rules in another order")
    (is (thrown? Exception (snap/restore-run s (take 1 smoke/ac-rules))) "a rule missing")
    (is (thrown? Exception (snap/restore-run (assoc s :cromulent/run-snapshot 0) smoke/ac-rules)))
    (is (thrown? Exception (snap/snapshot-run (assoc run :state {:x (atom 0)})))
        "a scheduler keeping state that is not data")))
