(ns cromulent.extract-test
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.test.check :as tc]
            [clojure.test.check.properties :as prop]
            [cromulent.core :as eg]
            [cromulent.extract :as ex]
            [cromulent.gen :as cg]
            [cromulent.term :as term]))

(deftest ast-size-is-node-count
  (is (= 1 (ex/ast-size :a [])))
  (is (= 4 (ex/ast-size [:+ 0 0] [1 2]))))

(deftest smallest-term-wins
  (let [[g r] (eg/add (eg/egraph) [:+ 0 [:* 1 :a]])
        [g a] (eg/add g :a)
        [g _] (eg/union g r a)
        g (eg/rebuild g)]
    (is (= {:cost 1 :term :a} (ex/extract g r)))
    (is (= {:cost 1 :term :a} (ex/yoink g r)))
    (is (= {:cost 3 :term [:* 1 :a]} (ex/extract g (second (eg/add g [:* 1 :a])))))))

(deftest cost-functions-encode-taste
  (let [[g m] (eg/add (eg/egraph) [:* :a 2])
        [g s] (eg/add g [:<< :a 1])
        [g _] (eg/union g m s)
        g (eg/rebuild g)
        expensive-mul (fn [node child-costs]
                        (+ (if (and (term/compound? node) (= :* (term/operator node))) 10 1)
                           (reduce + child-costs)))]
    (is (= {:cost 3 :term [:* :a 2]} (ex/extract g m)) "a tie under ast-size goes to the smaller term")
    (is (= {:cost 3 :term [:<< :a 1]} (ex/extract g m expensive-mul)))))

(deftest ties-do-not-depend-on-ids
  ;; x + y = y + x under f, with the two sums added in either order and
  ;; the union asked either way round: the ids differ, the extracted
  ;; terms do not
  (let [run (fn [t1 t2 flip?]
              (let [[g a] (eg/add (eg/egraph) t1)
                    [g b] (eg/add g t2)
                    [g f] (eg/add g [:f t1])
                    g (eg/rebuild (first (if flip? (eg/union g b a) (eg/union g a b))))]
                [(ex/extract g a) (ex/extract g f)]))
        xy [:+ :x :y], yx [:+ :y :x]]
    (is (= [{:cost 3 :term xy} {:cost 4 :term [:f xy]}]
           (run xy yx false) (run xy yx true) (run yx xy false) (run yx xy true))
        "the smaller term, at the root and under a parent")))

(deftest the-table-holds-the-term-of-every-class
  (let [[g s] (eg/add (eg/egraph) [:+ [:* :a 1] :b])
        table (ex/best-costs g ex/ast-size)
        product (eg/lookup g [:* (eg/lookup g :a) (eg/lookup g 1)])]
    (is (= {:cost 5 :node [:+ product (eg/lookup g :b)] :term [:+ [:* :a 1] :b]} (nth table s)))
    (is (= {:cost 3 :node [:* (eg/lookup g :a) (eg/lookup g 1)] :term [:* :a 1]} (nth table product)))))

(deftest vector-costs-compare-lexicographically
  ;; [shifts size]: fewer shifts first, then the smaller term
  (let [[g m] (eg/add (eg/egraph) [:* :a 2])
        [g s] (eg/add g [:<< :a 1])
        [g _] (eg/union g m s)
        g (eg/rebuild g)
        no-shift (fn [node child-costs]
                   [(+ (if (and (term/compound? node) (= :<< (term/operator node))) 1 0)
                       (reduce + 0 (map first child-costs)))
                    (reduce + 1 (map second child-costs))])]
    (is (= {:cost [0 3] :term [:* :a 2]} (ex/extract g m no-shift)))
    (is (= {:cost [0 3] :term [:<< :a 1]}
           (ex/extract g m (fn [node child-costs]
                             [(+ (if (and (term/compound? node) (= :* (term/operator node))) 1 0)
                                 (reduce + 0 (map first child-costs)))
                              (reduce + 1 (map second child-costs))])))
        "and the other way round")))

(deftest cycles-are-harmless
  (let [[g x] (eg/add (eg/egraph) :x)
        [g x0] (eg/add g [:+ :x 0])
        [g _] (eg/union g x x0)
        g (eg/rebuild g)]
    (is (= {:cost 1 :term :x} (ex/extract g x0)))))

(deftest extractor-shares-one-table
  (let [[g s] (eg/add (eg/egraph) [:+ [:* :a 1] [:* :b 1]])
        best (ex/extractor g)]
    (is (= {:cost 7 :term [:+ [:* :a 1] [:* :b 1]]} (best s)))
    (is (= {:cost 3 :term [:* :a 1]} (best (second (eg/add g [:* :a 1])))))
    (is (= {:cost 1 :term 1} (best (second (eg/add g 1)))))))

;; ---------------------------------------------------------------------------
;; properties

(deftest extracted-terms-are-members-and-minimal
  ;; for every class: the extracted term is in the class, its cost is
  ;; its size, and no input term of the class is smaller
  (let [res (tc/quick-check
             200
             (prop/for-all [ops cg/script-gen]
               (let [{:keys [egraph terms]} (cg/run-script (eg/egraph) ops)
                     best (ex/extractor egraph)
                     by-class (group-by #(cg/id-of egraph %) terms)]
                 (every? (fn [r]
                           (let [{:keys [cost term]} (best r)
                                 [g' id] (eg/add egraph term)]
                             (and (= r (eg/find g' id))
                                  (= (:next-id g') (:next-id egraph))
                                  (= cost (cg/size term))
                                  (every? #(<= cost (cg/size %)) (get by-class r)))))
                         (eg/roots egraph)))))]
    (is (:pass? res) (pr-str res))))
