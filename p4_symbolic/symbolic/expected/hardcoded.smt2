; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(declare-fun standard_metadata.egress_spec () (_ BitVec 9))
(assert
 (let (($x55 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x55)))
(assert
 (let ((?x35 (concat (_ bv0 8) (_ bv0 1))))
 (let (($x36 (= standard_metadata.ingress_port ?x35)))
 (let (($x32 (not false)))
 (let (($x38 (and $x32 $x36)))
 (let (($x39 (and $x32 (not $x36))))
 (let ((?x44 (ite $x39 ?x35 (ite $x38 (concat (_ bv0 8) (_ bv1 1)) standard_metadata.egress_spec))))
 (or (or (= ?x44 (_ bv455 9)) (= ?x44 (_ bv0 9))) (= ?x44 (_ bv1 9))))))))))
(assert
 (let ((?x35 (concat (_ bv0 8) (_ bv0 1))))
 (let (($x36 (= standard_metadata.ingress_port ?x35)))
 (let (($x32 (not false)))
 (let (($x38 (and $x32 $x36)))
 (let (($x45 (ite $x36 $x38 false)))
 (let (($x39 (and $x32 (not $x36))))
 (let ((?x44 (ite $x39 ?x35 (ite $x38 (concat (_ bv0 8) (_ bv1 1)) standard_metadata.egress_spec))))
 (let (($x48 (= ?x44 (_ bv455 9))))
 (and (and (not $x48) $x45) (= (- 1) (- 1))))))))))))
(check-sat)

; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(declare-fun standard_metadata.egress_spec () (_ BitVec 9))
(assert
 (let (($x55 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x55)))
(assert
 (let ((?x35 (concat (_ bv0 8) (_ bv0 1))))
 (let (($x36 (= standard_metadata.ingress_port ?x35)))
 (let (($x32 (not false)))
 (let (($x38 (and $x32 $x36)))
 (let (($x39 (and $x32 (not $x36))))
 (let ((?x44 (ite $x39 ?x35 (ite $x38 (concat (_ bv0 8) (_ bv1 1)) standard_metadata.egress_spec))))
 (or (or (= ?x44 (_ bv455 9)) (= ?x44 (_ bv0 9))) (= ?x44 (_ bv1 9))))))))))
(assert
 (let (($x32 (not false)))
 (let (($x39 (and $x32 (not (= standard_metadata.ingress_port (concat (_ bv0 8) (_ bv0 1)))))))
 (let ((?x35 (concat (_ bv0 8) (_ bv0 1))))
 (let (($x36 (= standard_metadata.ingress_port ?x35)))
 (let (($x46 (ite $x36 false $x39)))
 (let ((?x44 (ite $x39 ?x35 (ite (and $x32 $x36) (concat (_ bv0 8) (_ bv1 1)) standard_metadata.egress_spec))))
 (let (($x48 (= ?x44 (_ bv455 9))))
 (and (and (not $x48) $x46) (= (- 1) (- 1)))))))))))
(check-sat)

