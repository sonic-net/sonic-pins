; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(declare-fun standard_metadata.egress_spec () (_ BitVec 9))
(assert
 (let (($x37 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x37)))
(assert
 (let ((?x27 (ite true standard_metadata.ingress_port standard_metadata.egress_spec)))
 (let (($x29 (= ?x27 (_ bv511 9))))
 (or $x29 (or (or false (= ?x27 (_ bv0 9))) (= ?x27 (_ bv1 9)))))))
(assert
 (let ((?x27 (ite true standard_metadata.ingress_port standard_metadata.egress_spec)))
 (let (($x29 (= ?x27 (_ bv511 9))))
 (and (and (not $x29) true) (= (- 1) (- 1))))))
(check-sat)

