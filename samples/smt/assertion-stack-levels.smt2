(set-logic QF_UF)
(declare-fun a () Bool)
(declare-fun b () Bool)
(assert (or a b))

(get-info :assertion-stack-levels)

(push 1)
(get-info :assertion-stack-levels)
(pop 1)

(get-info :assertion-stack-levels)
