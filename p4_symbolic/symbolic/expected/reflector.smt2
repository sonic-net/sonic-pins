; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(declare-fun standard_metadata.egress_spec () (_ BitVec 9))
(assert
 (let (($x42 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x42)))
(assert
 (let ((?x33 (ite true standard_metadata.ingress_port standard_metadata.egress_spec)))
 (or (or (= ?x33 (_ bv455 9)) (= ?x33 (_ bv0 9))) (= ?x33 (_ bv1 9)))))
(assert
 (let ((?x33 (ite true standard_metadata.ingress_port standard_metadata.egress_spec)))
 (let (($x35 (= ?x33 (_ bv455 9))))
 (and (and (not $x35) true) (= (- 1) (- 1))))))
(check-sat)

