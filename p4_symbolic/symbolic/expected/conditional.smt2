; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(declare-fun standard_metadata.egress_spec () (_ BitVec 9))
(declare-fun ethernet.dst_addr () (_ BitVec 48))
(assert
 (let (($x64 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x64)))
(assert
 (let (($x34 (= standard_metadata.ingress_port (concat (_ bv0 8) (_ bv0 1)))))
 (let (($x36 (and true $x34)))
 (let (($x37 (and true (not $x34))))
 (let ((?x50 (ite (and true (not (and true (= ethernet.dst_addr (_ bv1 48))))) (_ bv511 9) (ite $x37 (_ bv511 9) (ite $x36 (_ bv511 9) standard_metadata.egress_spec)))))
 (let (($x45 (= ethernet.dst_addr (_ bv1 48))))
 (let (($x46 (and true $x45)))
 (let (($x47 (and true $x46)))
 (let ((?x55 (ite $x47 (_ bv1 9) ?x50)))
 (let (($x57 (= ?x55 (_ bv511 9))))
 (or $x57 (or (or false (= ?x55 (_ bv0 9))) (= ?x55 (_ bv1 9))))))))))))))
(assert
 (let (($x34 (= standard_metadata.ingress_port (concat (_ bv0 8) (_ bv0 1)))))
 (let (($x36 (and true $x34)))
 (let (($x42 (ite $x34 $x36 false)))
 (let (($x37 (and true (not $x34))))
 (let ((?x50 (ite (and true (not (and true (= ethernet.dst_addr (_ bv1 48))))) (_ bv511 9) (ite $x37 (_ bv511 9) (ite $x36 (_ bv511 9) standard_metadata.egress_spec)))))
 (let (($x45 (= ethernet.dst_addr (_ bv1 48))))
 (let (($x46 (and true $x45)))
 (let (($x47 (and true $x46)))
 (let ((?x55 (ite $x47 (_ bv1 9) ?x50)))
 (let (($x57 (= ?x55 (_ bv511 9))))
 (and (and (not $x57) $x42) (= (- 1) (- 1))))))))))))))
(check-sat)

; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(declare-fun standard_metadata.egress_spec () (_ BitVec 9))
(declare-fun ethernet.dst_addr () (_ BitVec 48))
(assert
 (let (($x64 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x64)))
(assert
 (let (($x34 (= standard_metadata.ingress_port (concat (_ bv0 8) (_ bv0 1)))))
 (let (($x36 (and true $x34)))
 (let (($x37 (and true (not $x34))))
 (let ((?x50 (ite (and true (not (and true (= ethernet.dst_addr (_ bv1 48))))) (_ bv511 9) (ite $x37 (_ bv511 9) (ite $x36 (_ bv511 9) standard_metadata.egress_spec)))))
 (let (($x45 (= ethernet.dst_addr (_ bv1 48))))
 (let (($x46 (and true $x45)))
 (let (($x47 (and true $x46)))
 (let ((?x55 (ite $x47 (_ bv1 9) ?x50)))
 (let (($x57 (= ?x55 (_ bv511 9))))
 (or $x57 (or (or false (= ?x55 (_ bv0 9))) (= ?x55 (_ bv1 9))))))))))))))
(assert
 (let (($x37 (and true (not (= standard_metadata.ingress_port (concat (_ bv0 8) (_ bv0 1)))))))
 (let (($x34 (= standard_metadata.ingress_port (concat (_ bv0 8) (_ bv0 1)))))
 (let (($x43 (ite $x34 false $x37)))
 (let ((?x41 (ite $x37 (_ bv511 9) (ite (and true $x34) (_ bv511 9) standard_metadata.egress_spec))))
 (let ((?x50 (ite (and true (not (and true (= ethernet.dst_addr (_ bv1 48))))) (_ bv511 9) ?x41)))
 (let (($x45 (= ethernet.dst_addr (_ bv1 48))))
 (let (($x46 (and true $x45)))
 (let (($x47 (and true $x46)))
 (let ((?x55 (ite $x47 (_ bv1 9) ?x50)))
 (let (($x57 (= ?x55 (_ bv511 9))))
 (and (and (not $x57) $x43) (= (- 1) (- 1))))))))))))))
(check-sat)

; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(declare-fun standard_metadata.egress_spec () (_ BitVec 9))
(declare-fun ethernet.dst_addr () (_ BitVec 48))
(assert
 (let (($x64 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x64)))
(assert
 (let (($x34 (= standard_metadata.ingress_port (concat (_ bv0 8) (_ bv0 1)))))
 (let (($x36 (and true $x34)))
 (let (($x37 (and true (not $x34))))
 (let ((?x50 (ite (and true (not (and true (= ethernet.dst_addr (_ bv1 48))))) (_ bv511 9) (ite $x37 (_ bv511 9) (ite $x36 (_ bv511 9) standard_metadata.egress_spec)))))
 (let (($x45 (= ethernet.dst_addr (_ bv1 48))))
 (let (($x46 (and true $x45)))
 (let (($x47 (and true $x46)))
 (let ((?x55 (ite $x47 (_ bv1 9) ?x50)))
 (let (($x57 (= ?x55 (_ bv511 9))))
 (or $x57 (or (or false (= ?x55 (_ bv0 9))) (= ?x55 (_ bv1 9))))))))))))))
(assert
 (let (($x45 (= ethernet.dst_addr (_ bv1 48))))
 (let (($x46 (and true $x45)))
 (let (($x47 (and true $x46)))
 (let ((?x52 (ite $x47 0 (- 1))))
 (let (($x34 (= standard_metadata.ingress_port (concat (_ bv0 8) (_ bv0 1)))))
 (let (($x36 (and true $x34)))
 (let (($x37 (and true (not $x34))))
 (let ((?x50 (ite (and true (not $x46)) (_ bv511 9) (ite $x37 (_ bv511 9) (ite $x36 (_ bv511 9) standard_metadata.egress_spec)))))
 (let ((?x55 (ite $x47 (_ bv1 9) ?x50)))
 (let (($x57 (= ?x55 (_ bv511 9))))
 (and (and (not $x57) true) (= ?x52 (- 1))))))))))))))
(check-sat)

; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(declare-fun standard_metadata.egress_spec () (_ BitVec 9))
(declare-fun ethernet.dst_addr () (_ BitVec 48))
(assert
 (let (($x64 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x64)))
(assert
 (let (($x34 (= standard_metadata.ingress_port (concat (_ bv0 8) (_ bv0 1)))))
 (let (($x36 (and true $x34)))
 (let (($x37 (and true (not $x34))))
 (let ((?x50 (ite (and true (not (and true (= ethernet.dst_addr (_ bv1 48))))) (_ bv511 9) (ite $x37 (_ bv511 9) (ite $x36 (_ bv511 9) standard_metadata.egress_spec)))))
 (let (($x45 (= ethernet.dst_addr (_ bv1 48))))
 (let (($x46 (and true $x45)))
 (let (($x47 (and true $x46)))
 (let ((?x55 (ite $x47 (_ bv1 9) ?x50)))
 (let (($x57 (= ?x55 (_ bv511 9))))
 (or $x57 (or (or false (= ?x55 (_ bv0 9))) (= ?x55 (_ bv1 9))))))))))))))
(assert
 (let (($x45 (= ethernet.dst_addr (_ bv1 48))))
 (let (($x46 (and true $x45)))
 (let (($x47 (and true $x46)))
 (let ((?x52 (ite $x47 0 (- 1))))
 (let (($x34 (= standard_metadata.ingress_port (concat (_ bv0 8) (_ bv0 1)))))
 (let (($x36 (and true $x34)))
 (let (($x37 (and true (not $x34))))
 (let ((?x50 (ite (and true (not $x46)) (_ bv511 9) (ite $x37 (_ bv511 9) (ite $x36 (_ bv511 9) standard_metadata.egress_spec)))))
 (let ((?x55 (ite $x47 (_ bv1 9) ?x50)))
 (let (($x57 (= ?x55 (_ bv511 9))))
 (let (($x100 (and (not $x57) true)))
 (and $x100 (= ?x52 0))))))))))))))
(check-sat)

