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

(defn make
  "A compound node from an operator and a sequence of children."
  [op children]
  (into [op] children))

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
