(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun A () Bool)
(assert
  (let ((i1 (ite A (<= (+ (* 2 x) (* (- 1) y)) (- 4))
                   (= (* y 5) (- 2 x)))))
    (and
      i1
      (or (> x y) (= A (< (* 3 x) (+ (- 1) (* 1 (+ x y)))))))))
(check-sat)
(exit)
