; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(declare-fun standard_metadata.egress_spec () (_ BitVec 9))
(assert
 (let (($x43 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x43)))
(assert
 (let (($x32 (not false)))
 (let ((?x34 (ite $x32 standard_metadata.ingress_port standard_metadata.egress_spec)))
 (or (or (= ?x34 (_ bv455 9)) (= ?x34 (_ bv0 9))) (= ?x34 (_ bv1 9))))))
(assert
 (let (($x32 (not false)))
 (let ((?x34 (ite $x32 standard_metadata.ingress_port standard_metadata.egress_spec)))
 (let (($x36 (= ?x34 (_ bv455 9))))
 (and (and (not $x36) $x32) (= (- 1) (- 1)))))))
(check-sat)

