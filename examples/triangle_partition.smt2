(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(declare-fun a () Int)
(declare-fun b () Int)

(assert (>= x 0))
(assert (<= 0 x))
(assert (>= b 0))
(assert (>= z 0))
(assert (= (+ y z) a))
(assert (>= y 0))
(assert (<= (+ x a) 50))
(assert (<= b 10))
