(set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun A () Bool)
(assert
  (let ((i1 (ite A (<= (+ (* 2.0 x) (* (/ 1 3) y)) (- 4))
                   (= (* y 1.5) (- 2 x)))))
    (and
      i1
      (or (> x y) (= A (< (* 3 x) (+ (- 1) (* (/ 1 5) (+ x y)))))))))
(check-sat)
(exit)
