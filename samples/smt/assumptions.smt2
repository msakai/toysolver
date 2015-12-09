(set-option :produce-unsat-assumptions true)
(set-logic QF_UF)
(declare-fun a () Bool)
(declare-fun b () Bool)
(assert (or a b))
(check-sat-assuming ((not a) (not b)))
(get-unsat-assumptions)
