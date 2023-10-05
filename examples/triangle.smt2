(declare-fun x () Int)
(declare-fun y () Int)

(assert (>= x 0))
(assert (>= y 0))
(assert (<= (+ x y) 50))

(check-sat)
(get-model)
