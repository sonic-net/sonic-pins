; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(declare-fun standard_metadata.egress_spec () (_ BitVec 9))
(assert
 (let (($x45 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x45)))
(assert
 (let ((?x26 (concat (_ bv0 8) (_ bv0 1))))
 (let (($x27 (= standard_metadata.ingress_port ?x26)))
 (let (($x29 (and true $x27)))
 (let (($x30 (and true (not $x27))))
 (let ((?x35 (ite $x30 ?x26 (ite $x29 (concat (_ bv0 8) (_ bv1 1)) standard_metadata.egress_spec))))
 (let (($x37 (= ?x35 (_ bv511 9))))
 (or $x37 (or (or false (= ?x35 (_ bv0 9))) (= ?x35 (_ bv1 9)))))))))))
(assert
 (let ((?x26 (concat (_ bv0 8) (_ bv0 1))))
 (let (($x27 (= standard_metadata.ingress_port ?x26)))
 (let (($x29 (and true $x27)))
 (let (($x30 (and true (not $x27))))
 (let ((?x35 (ite $x30 ?x26 (ite $x29 (concat (_ bv0 8) (_ bv1 1)) standard_metadata.egress_spec))))
 (let (($x37 (= ?x35 (_ bv511 9))))
 (and (and (not $x37) $x29) (= (- 1) (- 1))))))))))
(check-sat)

; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(declare-fun standard_metadata.egress_spec () (_ BitVec 9))
(assert
 (let (($x45 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x45)))
(assert
 (let ((?x26 (concat (_ bv0 8) (_ bv0 1))))
 (let (($x27 (= standard_metadata.ingress_port ?x26)))
 (let (($x29 (and true $x27)))
 (let (($x30 (and true (not $x27))))
 (let ((?x35 (ite $x30 ?x26 (ite $x29 (concat (_ bv0 8) (_ bv1 1)) standard_metadata.egress_spec))))
 (let (($x37 (= ?x35 (_ bv511 9))))
 (or $x37 (or (or false (= ?x35 (_ bv0 9))) (= ?x35 (_ bv1 9)))))))))))
(assert
 (let (($x30 (and true (not (= standard_metadata.ingress_port (concat (_ bv0 8) (_ bv0 1)))))))
 (let ((?x26 (concat (_ bv0 8) (_ bv0 1))))
 (let (($x27 (= standard_metadata.ingress_port ?x26)))
 (let (($x29 (and true $x27)))
 (let ((?x35 (ite $x30 ?x26 (ite $x29 (concat (_ bv0 8) (_ bv1 1)) standard_metadata.egress_spec))))
 (let (($x37 (= ?x35 (_ bv511 9))))
 (and (and (not $x37) $x30) (= (- 1) (- 1))))))))))
(check-sat)

