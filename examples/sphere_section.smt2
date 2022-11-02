(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)

(assert (<= (+ (* x x) (* y y) (* z z)) (* 50 50)))
(assert (>= y 0))
(assert (>= x 0))
(assert (>= z 0))
