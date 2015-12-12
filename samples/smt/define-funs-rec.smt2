(set-logic QF_UFLIA)
(define-funs-rec
  ((even ((x Int)) Bool)
   (odd ((x Int)) Bool))
  ((ite (= x 0) true (odd (- x 1)))
   (ite (= x 0) true (odd (- x 1)))))
(check-sat)
