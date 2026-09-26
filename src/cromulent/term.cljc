(ns cromulent.term
  "The seam between the user's term shape and the engine.

  v1 representation: tagged vectors. A compound node is a vector whose
  first element is the operator and whose remaining elements are its
  children; anything that is not a vector is a leaf. E-nodes use the
  same shape with children replaced by e-class ids.

  Every core algorithm reaches the representation only through this
  namespace, so changing it (a packed key, a record, a protocol) is a
  change here and nowhere else.")

(defn compound?
  "Is t a compound node (operator + children) rather than a leaf?"
  [t]
  (vector? t))

(defn operator
  "The operator of a compound node."
  [t]
  (nth t 0))

(defn children
  "The children of a compound node, as a vector."
  [t]
  (subvec t 1))

(defn arity
  "Number of children of a compound node."
  [t]
  (dec (count t)))

(defn child
  "The i-th child (from 0) of a compound node."
  [t i]
  (nth t (inc i)))

(defn make
  "A compound node from an operator and a sequence of children."
  [op children]
  (if (vector? children)
    (case (count children)
      0 [op]
      1 [op (nth children 0)]
      2 [op (nth children 0) (nth children 1)]
      (into [op] children))
    (into [op] children)))

(defn- rank [x]
  (cond (number? x) 0 (keyword? x) 1 (symbol? x) 2 (string? x) 3 (vector? x) 4 :else 5))

(defn compare-nodes
  "A total order on e-nodes and leaves that is the same on every
  runtime: leaves before compound nodes, then by arity, then element
  by element with numbers before keywords before symbols before
  strings before vectors, and anything else by its printed form."
  [a b]
  (let [ra (rank a), rb (rank b)]
    (cond
      (not= ra rb) (compare ra rb)
      (= 4 ra) (let [c (compare (count a) (count b))]
                 (if (not= 0 c)
                   c
                   (loop [i 0]
                     (if (= i (count a))
                       0
                       (let [c (compare-nodes (nth a i) (nth b i))]
                         (if (not= 0 c) c (recur (inc i))))))))
      (= 5 ra) (compare (pr-str a) (pr-str b))
      :else (compare a b))))

(defn map-children
  "Apply f to every child of a compound node; a leaf is returned as it
  is. Returns the very same node when no child changes."
  [f t]
  (if (compound? t)
    (let [n (count t)]
      (loop [i 1, t t]
        (if (< i n)
          (let [c (nth t i), c' (f c)]
            (recur (inc i) (if (= c c') t (assoc t i c'))))
          t)))
    t))
