; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(declare-fun standard_metadata.egress_spec () (_ BitVec 9))
(assert
 (let (($x35 (= standard_metadata.ingress_port (_ bv1 9))))
 (and (and (distinct standard_metadata.ingress_port (_ bv511 9)) true) (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x35))))
(assert
 (let ((?x25 (ite true standard_metadata.ingress_port standard_metadata.egress_spec)))
 (let (($x27 (= ?x25 (_ bv511 9))))
 (or $x27 (or (or false (= ?x25 (_ bv0 9))) (= ?x25 (_ bv1 9)))))))
(assert
 (let ((?x25 (ite true standard_metadata.ingress_port standard_metadata.egress_spec)))
 (let (($x27 (= ?x25 (_ bv511 9))))
 (and (and (not $x27) true) (= (- 1) (- 1))))))
(check-sat)

