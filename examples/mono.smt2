(declare-sort a 0)
(declare-datatypes (b) ((list (nil))))
(assert-not (forall ((xs (list a)) (ys (list a))) (= xs ys)))
(check-sat)
