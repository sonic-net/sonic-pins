; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(declare-fun standard_metadata.egress_spec () (_ BitVec 9))
(assert
 (let (($x54 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x54)))
(assert
 (let ((?x34 (concat (_ bv0 8) (_ bv0 1))))
 (let (($x35 (= standard_metadata.ingress_port ?x34)))
 (let (($x37 (and true $x35)))
 (let (($x38 (and true (not $x35))))
 (let ((?x43 (ite $x38 ?x34 (ite $x37 (concat (_ bv0 8) (_ bv1 1)) standard_metadata.egress_spec))))
 (or (or (= ?x43 (_ bv455 9)) (= ?x43 (_ bv0 9))) (= ?x43 (_ bv1 9)))))))))
(assert
 (let ((?x34 (concat (_ bv0 8) (_ bv0 1))))
 (let (($x35 (= standard_metadata.ingress_port ?x34)))
 (let (($x37 (and true $x35)))
 (let (($x44 (ite $x35 $x37 false)))
 (let (($x38 (and true (not $x35))))
 (let ((?x43 (ite $x38 ?x34 (ite $x37 (concat (_ bv0 8) (_ bv1 1)) standard_metadata.egress_spec))))
 (let (($x47 (= ?x43 (_ bv455 9))))
 (and (and (not $x47) $x44) (= (- 1) (- 1)))))))))))
(check-sat)

; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(declare-fun standard_metadata.egress_spec () (_ BitVec 9))
(assert
 (let (($x54 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x54)))
(assert
 (let ((?x34 (concat (_ bv0 8) (_ bv0 1))))
 (let (($x35 (= standard_metadata.ingress_port ?x34)))
 (let (($x37 (and true $x35)))
 (let (($x38 (and true (not $x35))))
 (let ((?x43 (ite $x38 ?x34 (ite $x37 (concat (_ bv0 8) (_ bv1 1)) standard_metadata.egress_spec))))
 (or (or (= ?x43 (_ bv455 9)) (= ?x43 (_ bv0 9))) (= ?x43 (_ bv1 9)))))))))
(assert
 (let (($x38 (and true (not (= standard_metadata.ingress_port (concat (_ bv0 8) (_ bv0 1)))))))
 (let ((?x34 (concat (_ bv0 8) (_ bv0 1))))
 (let (($x35 (= standard_metadata.ingress_port ?x34)))
 (let (($x45 (ite $x35 false $x38)))
 (let (($x37 (and true $x35)))
 (let ((?x43 (ite $x38 ?x34 (ite $x37 (concat (_ bv0 8) (_ bv1 1)) standard_metadata.egress_spec))))
 (let (($x47 (= ?x43 (_ bv455 9))))
 (and (and (not $x47) $x45) (= (- 1) (- 1)))))))))))
(check-sat)

