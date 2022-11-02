(declare-fun x () Int)
(declare-fun y () Int)

(assert (<= (+ (* x x) (* y y)) (* 50 50)))
(assert (>= y 0))
(assert (>= x 0))
