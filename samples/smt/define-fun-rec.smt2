(set-logic QF_UFLIA)
(define-fun-rec fact ((n Int)) Int
  (ite (<= n 0)
       1
       (* n (fact (- n 1)))))
(check-sat)
