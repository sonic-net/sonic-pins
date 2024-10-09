; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(declare-fun standard_metadata.egress_spec () (_ BitVec 9))
(assert
 (let (($x46 (= standard_metadata.ingress_port (_ bv1 9))))
 (and (and (distinct standard_metadata.ingress_port (_ bv511 9)) true) (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x46))))
(assert
 (let ((?x26 (concat (_ bv0 8) (_ bv0 1))))
 (let (($x27 (= standard_metadata.ingress_port ?x26)))
 (let (($x29 (and true $x27)))
 (let (($x30 (and true (not $x27))))
 (let ((?x35 (ite $x30 ?x26 (ite $x29 (concat (_ bv0 8) (_ bv1 1)) standard_metadata.egress_spec))))
 (let (($x39 (= ?x35 (_ bv511 9))))
 (or $x39 (or (or false (= ?x35 (_ bv0 9))) (= ?x35 (_ bv1 9)))))))))))
(assert
 (let ((?x26 (concat (_ bv0 8) (_ bv0 1))))
 (let (($x27 (= standard_metadata.ingress_port ?x26)))
 (let (($x29 (and true $x27)))
 (let (($x36 (ite $x27 $x29 false)))
 (let (($x30 (and true (not $x27))))
 (let ((?x35 (ite $x30 ?x26 (ite $x29 (concat (_ bv0 8) (_ bv1 1)) standard_metadata.egress_spec))))
 (let (($x39 (= ?x35 (_ bv511 9))))
 (and (and (not $x39) $x36) (= (- 1) (- 1)))))))))))
(check-sat)

; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(declare-fun standard_metadata.egress_spec () (_ BitVec 9))
(assert
 (let (($x46 (= standard_metadata.ingress_port (_ bv1 9))))
 (and (and (distinct standard_metadata.ingress_port (_ bv511 9)) true) (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x46))))
(assert
 (let ((?x26 (concat (_ bv0 8) (_ bv0 1))))
 (let (($x27 (= standard_metadata.ingress_port ?x26)))
 (let (($x29 (and true $x27)))
 (let (($x30 (and true (not $x27))))
 (let ((?x35 (ite $x30 ?x26 (ite $x29 (concat (_ bv0 8) (_ bv1 1)) standard_metadata.egress_spec))))
 (let (($x39 (= ?x35 (_ bv511 9))))
 (or $x39 (or (or false (= ?x35 (_ bv0 9))) (= ?x35 (_ bv1 9)))))))))))
(assert
 (let (($x30 (and true (not (= standard_metadata.ingress_port (concat (_ bv0 8) (_ bv0 1)))))))
 (let ((?x26 (concat (_ bv0 8) (_ bv0 1))))
 (let (($x27 (= standard_metadata.ingress_port ?x26)))
 (let (($x37 (ite $x27 false $x30)))
 (let (($x29 (and true $x27)))
 (let ((?x35 (ite $x30 ?x26 (ite $x29 (concat (_ bv0 8) (_ bv1 1)) standard_metadata.egress_spec))))
 (let (($x39 (= ?x35 (_ bv511 9))))
 (and (and (not $x39) $x37) (= (- 1) (- 1)))))))))))
(check-sat)

