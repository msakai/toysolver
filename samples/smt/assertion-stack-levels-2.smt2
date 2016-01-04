(set-logic QF_UF)
(declare-fun a () Bool)
(declare-fun b () Bool)
(assert (or a b))

(get-info :assertion-stack-levels)

; NOTE: omitting arguments of push/pop is not allowed in SMT-LIB2
; but many solver implement the omission.
(push)
(get-info :assertion-stack-levels)
(pop)

(get-info :assertion-stack-levels)
