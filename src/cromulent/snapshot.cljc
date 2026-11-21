(ns cromulent.snapshot
  "Snapshots: an e-graph, or a run, as plain data that outlives the
  process. See ideas/serialization.md.

  Everything in the e-graph map is data except :analyses, whose maps
  hold functions. A snapshot is the map without them, plus their
  names, in order; `restore` takes the analyses from the caller, as
  `cromulent.core/egraph` does, and refuses a list whose names differ.

    (snapshot g)                         ; => {:cromulent/snapshot 1
                                         ;     :analyses [:const-fold]
                                         ;     :egraph {...}}
    (restore snap {:analyses [const-fold]})

  A snapshot is taken in any state: pending work travels, so `rebuild`
  after `restore` gives what `rebuild` before `snapshot` would have.
  The packed hashcons keys travel as they are (`:ops` and `:op-names`
  come with them) and stay under 2^53, so a snapshot made on the JVM
  restores in ClojureScript; a Ratio in a leaf or in analysis data
  does not exist there.

  A run (cromulent.rewrite/start, `step`) holds compiled rules and the
  scheduler, which are functions; `snapshot-run` keeps the rest: the
  e-graph, the scheduler's state (backoff's bans), which epoch each
  rule last applied at, the stats, the elapsed time and the timeline.
  `restore-run` takes the rules and options again and gives the run
  that stepping on would have continued, so k iterations, a snapshot,
  a restore and the rest are the same run as one straight through.
  Rules that keep their own state outside the e-graph are the
  caller's to save; resuming without it is correct, only slower.

  Encoding is the caller's: a snapshot is a map of maps, vectors,
  sets, numbers, keywords, symbols and strings, so `pr-str` and
  `clojure.edn/read-string` round-trip it (bind *print-length* and
  *print-level* to nil), and so do Transit, Nippy and Fressian. EDN
  is about 240 bytes a node: for fixtures and small e-graphs.

  The contract: analysis data and :analysis-state hold only data (no
  functions, atoms, records or host objects), and so do leaves,
  operators and journal reasons. `snapshot` checks the whole map and
  refuses with the path of the first value that is not, naming the
  analysis when it is an analysis's, rather than write something that
  fails to read back."
  (:require [cromulent.core :as eg]
            [cromulent.platform :as platform]
            [cromulent.rewrite :as rw]
            [malli.core :as m]))

(def version
  "The format of the snapshots this namespace writes. `restore`
  refuses any other."
  1)

;; ---------------------------------------------------------------------------
;; what counts as data

(defn- scalar?
  "The common scalars, cheap to test. uuids and insts are tested after
  the collections: `inst?` is a protocol check, slow when it fails."
  [x]
  (or (number? x) (keyword? x) (string? x) (symbol? x) (nil? x)
      (boolean? x) (char? x)))

(defn- not-data
  "nil when x is plain data, else {:path p :value v}: v the first value
  found that is not, p the keys and indexes from x down to it (a set
  element is its own key, as `get-in` reads it; a map key that is not
  data is reported as the value at its map)."
  [x]
  (cond
    (scalar? x) nil
    (record? x) {:path () :value x}
    (map? x) (reduce-kv (fn [_ k v]
                          (if (not-data k)
                            (reduced {:path () :value k})
                            (when-let [p (not-data v)]
                              (reduced (update p :path conj k)))))
                        nil x)
    (vector? x) (let [n (count x)]
                  (loop [i 0]
                    (when (< i n)
                      (if-let [p (not-data (nth x i))]
                        (update p :path conj i)
                        (recur (inc i))))))
    (set? x) (some (fn [e] (when-let [p (not-data e)] (update p :path conj e))) x)
    (seq? x) (loop [s (seq x), i 0]
               (when s
                 (if-let [p (not-data (first s))]
                   (update p :path conj i)
                   (recur (next s) (inc i)))))
    (or (uuid? x) (inst? x)) nil
    :else {:path () :value x}))

(defn- owner
  "The analysis a path into an e-graph map belongs to, or nil."
  [[k i d a]]
  (cond
    (and (= k :classes) (= d :data)) a
    (= k :analysis-state) i))

(defn- refuse-unless-data [x what]
  (when-let [{:keys [path value]} (not-data x)]
    (let [path (vec path)
          analysis (when (= what :egraph) (owner path))]
      (throw (ex-info (str (if analysis
                             (str "analysis " (pr-str analysis) " keeps")
                             (str "the " (name what) " holds"))
                           " a value that is not data, at " (pr-str path)
                           ": " (pr-str value))
                      (cond-> {:path path :value value}
                        analysis (assoc :analysis analysis)))))))

;; ---------------------------------------------------------------------------
;; e-graphs

(def snapshot-schema
  "The shape of an e-graph snapshot. `restore` checks it; the e-graph
  inside is checked by cromulent.check, if the caller wants that."
  [:map
   [:cromulent/snapshot :int]
   [:analyses [:vector :any]]
   [:egraph [:map
             [:next-id :int]
             [:uf vector?]
             [:classes vector?]
             [:analysis-state map?]]]])

(def ^:private snapshot? (m/validator snapshot-schema))

(defn snapshot
  "g as plain data: {:cromulent/snapshot version :analyses [name ...]
  :egraph map}, the map being g without :analyses. Throws ex-info, with
  the :path and :value and, when it is an analysis's, the :analysis,
  if g holds a value that is not data. g need not be rebuilt."
  [g]
  (let [m (dissoc g :analyses)]
    (refuse-unless-data m :egraph)
    {:cromulent/snapshot version
     :analyses (mapv :name (:analyses g))
     :egraph m}))

(defn- check-version [snap k]
  (when-not (= version (get snap k))
    (throw (ex-info (str "snapshot version " (pr-str (get snap k))
                         ", this cromulent reads " version)
                    {:version (get snap k) :reads version}))))

(defn restore
  "The e-graph snap was taken of, with the analyses given as
  `cromulent.core/egraph` takes them: :analyses, a vector, or
  :analysis, one. Their names must be the snapshot's, in order; a
  snapshot of an e-graph with no analyses needs none. Throws ex-info
  for anything that is not a snapshot of this version."
  ([snap] (restore snap {}))
  ([snap {:keys [analysis analyses]}]
   (check-version snap :cromulent/snapshot)
   (when-not (snapshot? snap)
     (throw (ex-info "not an e-graph snapshot" {:explain (m/explain snapshot-schema snap)})))
   (let [analyses (vec (concat (when analysis [analysis]) analyses))
         given (mapv :name analyses)]
     (when-not (= given (:analyses snap))
       (throw (ex-info (str "the snapshot was taken with analyses " (pr-str (:analyses snap))
                            ", restored with " (pr-str given))
                       {:expected (:analyses snap) :given given})))
     (assoc (:egraph snap) :analyses analyses))))

;; ---------------------------------------------------------------------------
;; runs

(defn snapshot-run
  "run (cromulent.rewrite/start, `step`) as plain data:

    {:cromulent/run-snapshot version
     :egraph      the e-graph's snapshot
     :rules       the rules' names, in order
     :state       the scheduler's state
     :seen        rule name -> the epoch it last applied its matches at
     :stats       the iterations' stats
     :stop-reason the run's, or nil
     :ms          time the run has taken so far
     :timeline    snapshots of the timeline's e-graphs, when it kept one}

  Every e-graph of a timeline is written whole: the structure they
  share in memory is not shared on disk. Throws ex-info, as `snapshot`
  does, if any of it is not data; a scheduler of the caller's own must
  keep data as its state to be saved."
  [{:keys [egraph rules state seen stats stop-reason t0 timeline]}]
  (refuse-unless-data state :scheduler-state)
  (refuse-unless-data seen :seen)
  (refuse-unless-data stats :stats)
  (cond-> {:cromulent/run-snapshot version
           :egraph (snapshot egraph)
           :rules (mapv :name rules)
           :state state
           :seen seen
           :stats stats
           :stop-reason stop-reason
           :ms (- (platform/now-ms) t0)}
    timeline (assoc :timeline (mapv snapshot timeline))))

(defn restore-run
  "The run snap was taken of, ready to `step` on, given its rules
  again (the same names in the same order) and options: those of
  `cromulent.rewrite/embiggen`, plus :analyses or :analysis for its
  e-graphs as `restore` takes them. The limits count the whole run:
  :iter-limit its iterations and :time-limit-ms its time, the time
  between the snapshot and the restore excepted, so a run stopped by a
  limit goes on under a higher one. A stop reason that still holds is
  kept: :saturated, and :node-limit while the e-graph has more nodes
  than the :node-limit given; the iteration and time limits are
  checked again by the next `step`. With :timeline? the timeline goes on from the snapshot's, or
  starts at the restored e-graph if the snapshot kept none. The
  options need not be the original run's; with the same ones the run
  is the one that stepping on would have made."
  ([snap rules] (restore-run snap rules {}))
  ([snap rules opts]
   (check-version snap :cromulent/run-snapshot)
   (let [names (mapv :name rules)]
     (when-not (= names (:rules snap))
       (throw (ex-info (str "the run was snapshot with rules " (pr-str (:rules snap))
                            ", restored with " (pr-str names))
                       {:expected (:rules snap) :given names}))))
   (let [g (restore (:egraph snap) opts)
         run (rw/start g rules opts)]
     (assoc run
            :state (:state snap)
            :seen (:seen snap)
            :stats (:stats snap)
            :t0 (- (platform/now-ms) (:ms snap))
            :timeline (when (:timeline? opts)
                        (if-let [tl (:timeline snap)]
                          (mapv #(restore % opts) tl)
                          [(:egraph run)]))
            :stop-reason (case (:stop-reason snap)
                           :saturated :saturated
                           ;; 10000 is embiggen's default
                           :node-limit (when (> (eg/node-count g) (get opts :node-limit 10000))
                                         :node-limit)
                           nil)))))
