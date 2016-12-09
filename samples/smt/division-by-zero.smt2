(set-option :produce-models true)
(set-logic QF_LRA)
(declare-const x1 Real)
(declare-const x2 Real)

(define-fun y1 () Real (/ x1 0))
(define-fun y2 () Real (/ x2 0))
(check-sat) ; sat
(get-value (x1 x2 y1 y2))
(get-model)

(assert (not (= y1 y2)))
(check-sat) ; sat
(get-value (x1 x2 y1 y2))
(get-model)

(assert (= x1 x2))
(check-sat) ; unsat
