(get-option :global-declarations)

(set-option :global-declarations false)
(get-option :global-declarations)
(set-logic QF_UFLRA)

(push)
(declare-const x1 Bool)
(pop)
(declare-const x1 Real)

(reset)

(set-option :global-declarations true)
(get-option :global-declarations)
(set-logic QF_UFLRA)

(push)
(define-fun x2 () Real 1.0)
(pop)
(assert (= x2 1.0))
(check-sat)
