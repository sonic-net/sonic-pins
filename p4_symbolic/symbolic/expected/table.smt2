; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(declare-fun standard_metadata.egress_spec () (_ BitVec 9))
(assert
 (let (($x53 (= standard_metadata.ingress_port (_ bv1 9))))
 (and (and (distinct standard_metadata.ingress_port (_ bv511 9)) true) (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x53))))
(assert
 (let ((?x26 (concat (_ bv0 8) (_ bv0 1))))
 (let (($x32 (and true (= standard_metadata.ingress_port (concat (_ bv0 8) (_ bv1 1))))))
 (let (($x35 (and true (not (and true (= standard_metadata.ingress_port ?x26))))))
 (let ((?x30 (concat (_ bv0 8) (_ bv1 1))))
 (let (($x28 (and true (= standard_metadata.ingress_port ?x26))))
 (let (($x33 (and true $x28)))
 (let ((?x47 (ite $x33 ?x30 (ite (and $x35 $x32) ?x26 standard_metadata.egress_spec))))
 (let (($x38 (= ?x47 (_ bv511 9))))
 (or $x38 (or (or false (= ?x47 (_ bv0 9))) (= ?x47 (_ bv1 9)))))))))))))
(assert
 (let (($x32 (and true (= standard_metadata.ingress_port (concat (_ bv0 8) (_ bv1 1))))))
 (let (($x28 (and true (= standard_metadata.ingress_port (concat (_ bv0 8) (_ bv0 1))))))
 (let (($x33 (and true $x28)))
 (let ((?x46 (ite $x33 0 (ite (and true $x32) 1 (- 1)))))
 (let ((?x26 (concat (_ bv0 8) (_ bv0 1))))
 (let ((?x44 (ite (and (and true (not $x28)) $x32) ?x26 standard_metadata.egress_spec)))
 (let ((?x30 (concat (_ bv0 8) (_ bv1 1))))
 (let ((?x47 (ite $x33 ?x30 ?x44)))
 (let (($x38 (= ?x47 (_ bv511 9))))
 (and (and (not $x38) true) (= ?x46 (- 1)))))))))))))
(check-sat)

; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(declare-fun standard_metadata.egress_spec () (_ BitVec 9))
(assert
 (let (($x53 (= standard_metadata.ingress_port (_ bv1 9))))
 (and (and (distinct standard_metadata.ingress_port (_ bv511 9)) true) (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x53))))
(assert
 (let ((?x26 (concat (_ bv0 8) (_ bv0 1))))
 (let (($x32 (and true (= standard_metadata.ingress_port (concat (_ bv0 8) (_ bv1 1))))))
 (let (($x35 (and true (not (and true (= standard_metadata.ingress_port ?x26))))))
 (let ((?x30 (concat (_ bv0 8) (_ bv1 1))))
 (let (($x28 (and true (= standard_metadata.ingress_port ?x26))))
 (let (($x33 (and true $x28)))
 (let ((?x47 (ite $x33 ?x30 (ite (and $x35 $x32) ?x26 standard_metadata.egress_spec))))
 (let (($x38 (= ?x47 (_ bv511 9))))
 (or $x38 (or (or false (= ?x47 (_ bv0 9))) (= ?x47 (_ bv1 9)))))))))))))
(assert
 (let (($x32 (and true (= standard_metadata.ingress_port (concat (_ bv0 8) (_ bv1 1))))))
 (let (($x28 (and true (= standard_metadata.ingress_port (concat (_ bv0 8) (_ bv0 1))))))
 (let (($x33 (and true $x28)))
 (let ((?x46 (ite $x33 0 (ite (and true $x32) 1 (- 1)))))
 (let ((?x26 (concat (_ bv0 8) (_ bv0 1))))
 (let ((?x44 (ite (and (and true (not $x28)) $x32) ?x26 standard_metadata.egress_spec)))
 (let ((?x30 (concat (_ bv0 8) (_ bv1 1))))
 (let ((?x47 (ite $x33 ?x30 ?x44)))
 (let (($x38 (= ?x47 (_ bv511 9))))
 (let (($x116 (and (not $x38) true)))
 (and $x116 (= ?x46 0)))))))))))))
(check-sat)

; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(declare-fun standard_metadata.egress_spec () (_ BitVec 9))
(assert
 (let (($x53 (= standard_metadata.ingress_port (_ bv1 9))))
 (and (and (distinct standard_metadata.ingress_port (_ bv511 9)) true) (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x53))))
(assert
 (let ((?x26 (concat (_ bv0 8) (_ bv0 1))))
 (let (($x32 (and true (= standard_metadata.ingress_port (concat (_ bv0 8) (_ bv1 1))))))
 (let (($x35 (and true (not (and true (= standard_metadata.ingress_port ?x26))))))
 (let ((?x30 (concat (_ bv0 8) (_ bv1 1))))
 (let (($x28 (and true (= standard_metadata.ingress_port ?x26))))
 (let (($x33 (and true $x28)))
 (let ((?x47 (ite $x33 ?x30 (ite (and $x35 $x32) ?x26 standard_metadata.egress_spec))))
 (let (($x38 (= ?x47 (_ bv511 9))))
 (or $x38 (or (or false (= ?x47 (_ bv0 9))) (= ?x47 (_ bv1 9)))))))))))))
(assert
 (let (($x32 (and true (= standard_metadata.ingress_port (concat (_ bv0 8) (_ bv1 1))))))
 (let (($x28 (and true (= standard_metadata.ingress_port (concat (_ bv0 8) (_ bv0 1))))))
 (let (($x33 (and true $x28)))
 (let ((?x46 (ite $x33 0 (ite (and true $x32) 1 (- 1)))))
 (let ((?x26 (concat (_ bv0 8) (_ bv0 1))))
 (let ((?x44 (ite (and (and true (not $x28)) $x32) ?x26 standard_metadata.egress_spec)))
 (let ((?x30 (concat (_ bv0 8) (_ bv1 1))))
 (let ((?x47 (ite $x33 ?x30 ?x44)))
 (let (($x38 (= ?x47 (_ bv511 9))))
 (and (and (not $x38) true) (= ?x46 1))))))))))))
(check-sat)

