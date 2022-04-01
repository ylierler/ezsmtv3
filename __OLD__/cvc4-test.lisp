(set-info :smt-lib-version 2.6)
(set-option :produce-models true)

(declare-const x Bool)
(declare-const z Bool)
(declare-const never Bool)

(assert (or z x))
(assert (or (not z) x))
(assert (or (not x) never))
(assert (or (not z) (not x)))
(assert (or z (not x)))
(assert (or x (not never)))
(assert (not never))

(check-sat)
(get-value (x))
