; http://sun.iwu.edu/~mliffito/publications/jar_liffiton_CAMUS.pdf
; φ= (x1) ∧ (¬x1) ∧ (¬x1∨x2) ∧ (¬x2) ∧ (¬x1∨x3) ∧ (¬x3)
; MUSes(φ) = {{C1, C2}, {C1, C3, C4}, {C1, C5, C6}}
; MCSes(φ) = {{C1}, {C2, C3, C5}, {C2, C3, C6}, {C2, C4, C5}, {C2, C4, C6}}
(set-option :produce-unsat-assumptions true)
(set-logic QF_UF)
(declare-fun x1 () Bool)
(declare-fun x2 () Bool)
(declare-fun x3 () Bool)
(assert (! x1 :named C1))
(assert (! (not x1) :named C2))
(assert (! (or (not x1) x2) :named C3))
(assert (! (not x2) :named C4))
(assert (! (or (not x1) x3) :named C5))
(assert (! (not x3) :named C6))
(check-sat)
(get-unsat-core)
