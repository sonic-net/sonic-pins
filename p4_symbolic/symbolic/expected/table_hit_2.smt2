(ingress) $got_cloned$: false
(ingress) h1.$extracted$: false
(ingress) h1.$valid$: (ite true true false)
(ingress) h1.f1: h1.f1
(ingress) h1.f2: h1.f2
(ingress) h1.f3: h1.f3
(ingress) h1.f4: h1.f4
(ingress) scalars.$extracted$: false
(ingress) scalars.$valid$: false
(ingress) standard_metadata.$extracted$: false
(ingress) standard_metadata.$valid$: false
(ingress) standard_metadata._padding: standard_metadata._padding
(ingress) standard_metadata.checksum_error: #b0
(ingress) standard_metadata.deq_qdepth: #b0000000000000000000
(ingress) standard_metadata.deq_timedelta: #x00000000
(ingress) standard_metadata.egress_global_timestamp: #x000000000000
(ingress) standard_metadata.egress_port: standard_metadata.egress_port
(ingress) standard_metadata.egress_rid: #x0000
(ingress) standard_metadata.egress_spec: #b000000000
(ingress) standard_metadata.enq_qdepth: #b0000000000000000000
(ingress) standard_metadata.enq_timestamp: #x00000000
(ingress) standard_metadata.ingress_global_timestamp: #x000000000000
(ingress) standard_metadata.ingress_port: standard_metadata.ingress_port
(ingress) standard_metadata.instance_type: #x00000000
(ingress) standard_metadata.mcast_grp: #x0000
(ingress) standard_metadata.packet_length: standard_metadata.packet_length
(ingress) standard_metadata.parser_error: #x00000000
(ingress) standard_metadata.priority: #b000

(parsed) $got_cloned$: false
(parsed) h1.$extracted$: (ite true true false)
(parsed) h1.$valid$: (ite true true false)
(parsed) h1.f1: h1.f1
(parsed) h1.f2: h1.f2
(parsed) h1.f3: h1.f3
(parsed) h1.f4: h1.f4
(parsed) scalars.$extracted$: false
(parsed) scalars.$valid$: false
(parsed) standard_metadata.$extracted$: false
(parsed) standard_metadata.$valid$: false
(parsed) standard_metadata._padding: standard_metadata._padding
(parsed) standard_metadata.checksum_error: #b0
(parsed) standard_metadata.deq_qdepth: #b0000000000000000000
(parsed) standard_metadata.deq_timedelta: #x00000000
(parsed) standard_metadata.egress_global_timestamp: #x000000000000
(parsed) standard_metadata.egress_port: standard_metadata.egress_port
(parsed) standard_metadata.egress_rid: #x0000
(parsed) standard_metadata.egress_spec: #b000000000
(parsed) standard_metadata.enq_qdepth: #b0000000000000000000
(parsed) standard_metadata.enq_timestamp: #x00000000
(parsed) standard_metadata.ingress_global_timestamp: #x000000000000
(parsed) standard_metadata.ingress_port: standard_metadata.ingress_port
(parsed) standard_metadata.instance_type: #x00000000
(parsed) standard_metadata.mcast_grp: #x0000
(parsed) standard_metadata.packet_length: standard_metadata.packet_length
(parsed) standard_metadata.parser_error: (ite (and true (not true)) #x00000002 #x00000000)
(parsed) standard_metadata.priority: #b000

(egress) $got_cloned$: false
(egress) h1.$extracted$: (ite true true false)
(egress) h1.$valid$: (ite true true false)
(egress) h1.f1: h1.f1
(egress) h1.f2: h1.f2
(egress) h1.f3: h1.f3
(egress) h1.f4: h1.f4
(egress) scalars.$extracted$: false
(egress) scalars.$valid$: false
(egress) standard_metadata.$extracted$: false
(egress) standard_metadata.$valid$: false
(egress) standard_metadata._padding: standard_metadata._padding
(egress) standard_metadata.checksum_error: #b0
(egress) standard_metadata.deq_qdepth: #b0000000000000000000
(egress) standard_metadata.deq_timedelta: #x00000000
(egress) standard_metadata.egress_global_timestamp: #x000000000000
(egress) standard_metadata.egress_port: (let ((a!1 (= (ite (and true true (= h1.f1 #xff)) 0 (- 1)) (- 1)))
      (a!2 (distinct (ite (and true true (= h1.f1 #xff)) 0 (- 1)) (- 1))))
(let ((a!3 (ite (and true a!2 true (= h1.f2 #xff))
                #b000000010
                (ite (and true true (= h1.f1 #xff))
                     #b000000001
                     (ite true (concat #x00 #b0) #b000000000)))))
(let ((a!4 (ite (and true a!1 true (= h1.f3 #xff)) #b000000011 a!3)))
  (ite (not (= a!4 #b111111111)) a!4 standard_metadata.egress_port))))
(egress) standard_metadata.egress_rid: #x0000
(egress) standard_metadata.egress_spec: (let ((a!1 (= (ite (and true true (= h1.f1 #xff)) 0 (- 1)) (- 1)))
      (a!2 (distinct (ite (and true true (= h1.f1 #xff)) 0 (- 1)) (- 1))))
(let ((a!3 (ite (and true a!2 true (= h1.f2 #xff))
                #b000000010
                (ite (and true true (= h1.f1 #xff))
                     #b000000001
                     (ite true (concat #x00 #b0) #b000000000)))))
  (ite (and true a!1 true (= h1.f3 #xff)) #b000000011 a!3)))
(egress) standard_metadata.enq_qdepth: #b0000000000000000000
(egress) standard_metadata.enq_timestamp: #x00000000
(egress) standard_metadata.ingress_global_timestamp: #x000000000000
(egress) standard_metadata.ingress_port: standard_metadata.ingress_port
(egress) standard_metadata.instance_type: #x00000000
(egress) standard_metadata.mcast_grp: #x0000
(egress) standard_metadata.packet_length: standard_metadata.packet_length
(egress) standard_metadata.parser_error: (ite (and true (not true)) #x00000002 #x00000000)
(egress) standard_metadata.priority: #b000

(solver constraints)
; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(declare-fun h1.f1 () (_ BitVec 8))
(declare-fun h1.f2 () (_ BitVec 8))
(declare-fun h1.f3 () (_ BitVec 8))
(assert
 (let (($x95 (= standard_metadata.ingress_port (_ bv7 9))))
 (let (($x90 (= standard_metadata.ingress_port (_ bv6 9))))
 (let (($x85 (= standard_metadata.ingress_port (_ bv5 9))))
 (let (($x80 (= standard_metadata.ingress_port (_ bv4 9))))
 (let (($x75 (= standard_metadata.ingress_port (_ bv3 9))))
 (let (($x71 (= standard_metadata.ingress_port (_ bv2 9))))
 (let (($x67 (= standard_metadata.ingress_port (_ bv1 9))))
 (let (($x72 (or (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x67) $x71)))
 (or (or (or (or (or $x72 $x75) $x80) $x85) $x90) $x95))))))))))
(assert
 (let (($x18 (= h1.f1 (_ bv255 8))))
 (let (($x23 (and true $x18)))
 (let (($x27 (and true $x23)))
 (let ((?x36 (ite $x27 0 (- 1))))
 (let (($x39 (and (distinct ?x36 (- 1)) true)))
 (let (($x40 (and true $x39)))
 (let (($x43 (and $x40 (and true (= h1.f2 (_ bv255 8))))))
 (let (($x49 (= ?x36 (- 1))))
 (let (($x50 (and true $x49)))
 (let (($x53 (and $x50 (and true (= h1.f3 (_ bv255 8))))))
 (let ((?x58 (ite $x53 (_ bv3 9) (ite $x43 (_ bv2 9) (ite $x27 (_ bv1 9) (ite true (concat (_ bv0 8) (_ bv0 1)) (_ bv0 9)))))))
 (let (($x78 (or (or (or (or false (= ?x58 (_ bv0 9))) (= ?x58 (_ bv1 9))) (= ?x58 (_ bv2 9))) (= ?x58 (_ bv3 9)))))
 (let (($x98 (or (or (or (or $x78 (= ?x58 (_ bv4 9))) (= ?x58 (_ bv5 9))) (= ?x58 (_ bv6 9))) (= ?x58 (_ bv7 9)))))
 (let (($x34 (= ?x58 (_ bv511 9))))
 (or $x34 $x98))))))))))))))))
(check-sat)
