; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(declare-fun standard_metadata.egress_spec () (_ BitVec 9))
(assert
 (let (($x49 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x49)))
(assert
 (let ((?x28 (concat (_ bv0 8) (_ bv0 1))))
 (let (($x29 (= standard_metadata.ingress_port ?x28)))
 (let (($x31 (and true $x29)))
 (let (($x32 (and true (not $x29))))
 (let ((?x37 (ite $x32 ?x28 (ite $x31 (concat (_ bv0 8) (_ bv1 1)) standard_metadata.egress_spec))))
 (let (($x41 (= ?x37 (_ bv511 9))))
 (or $x41 (or (or false (= ?x37 (_ bv0 9))) (= ?x37 (_ bv1 9)))))))))))
(assert
 (let ((?x28 (concat (_ bv0 8) (_ bv0 1))))
 (let (($x29 (= standard_metadata.ingress_port ?x28)))
 (let (($x31 (and true $x29)))
 (let (($x38 (ite $x29 $x31 false)))
 (let (($x32 (and true (not $x29))))
 (let ((?x37 (ite $x32 ?x28 (ite $x31 (concat (_ bv0 8) (_ bv1 1)) standard_metadata.egress_spec))))
 (let (($x41 (= ?x37 (_ bv511 9))))
 (and (and (not $x41) $x38) (= (- 1) (- 1)))))))))))
(check-sat)

; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(declare-fun standard_metadata.egress_spec () (_ BitVec 9))
(assert
 (let (($x49 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x49)))
(assert
 (let ((?x28 (concat (_ bv0 8) (_ bv0 1))))
 (let (($x29 (= standard_metadata.ingress_port ?x28)))
 (let (($x31 (and true $x29)))
 (let (($x32 (and true (not $x29))))
 (let ((?x37 (ite $x32 ?x28 (ite $x31 (concat (_ bv0 8) (_ bv1 1)) standard_metadata.egress_spec))))
 (let (($x41 (= ?x37 (_ bv511 9))))
 (or $x41 (or (or false (= ?x37 (_ bv0 9))) (= ?x37 (_ bv1 9)))))))))))
(assert
 (let (($x32 (and true (not (= standard_metadata.ingress_port (concat (_ bv0 8) (_ bv0 1)))))))
 (let ((?x28 (concat (_ bv0 8) (_ bv0 1))))
 (let (($x29 (= standard_metadata.ingress_port ?x28)))
 (let (($x39 (ite $x29 false $x32)))
 (let (($x31 (and true $x29)))
 (let ((?x37 (ite $x32 ?x28 (ite $x31 (concat (_ bv0 8) (_ bv1 1)) standard_metadata.egress_spec))))
 (let (($x41 (= ?x37 (_ bv511 9))))
 (and (and (not $x41) $x39) (= (- 1) (- 1)))))))))))
(check-sat)

