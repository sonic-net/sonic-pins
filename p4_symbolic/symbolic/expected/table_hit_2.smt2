(ingress) $got_cloned$: false
(ingress) $got_recirculated$: false
(ingress) h1.$extracted$: false
(ingress) h1.$valid$: true
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
(parsed) $got_recirculated$: false
(parsed) h1.$extracted$: true
(parsed) h1.$valid$: true
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
(egress) $got_recirculated$: false
(egress) h1.$extracted$: true
(egress) h1.$valid$: true
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
(egress) standard_metadata.egress_port: (let ((a!1 (ite (and true (and true (= h1.f1 #xff))) 0 (- 1)))
      (a!2 (ite (and true (= h1.f1 #xff)) #b000000001 (concat #x00 #b0))))
(let ((a!3 (ite (and true (distinct a!1 (- 1)))
                (ite (and true (= h1.f2 #xff)) #b000000010 a!2)
                a!2)))
(let ((a!4 (ite (and true (= a!1 (- 1)))
                (ite (and true (= h1.f3 #xff)) #b000000011 a!3)
                a!3)))
  (ite (not (= a!4 #b111111111)) a!4 standard_metadata.egress_port))))
(egress) standard_metadata.egress_rid: #x0000
(egress) standard_metadata.egress_spec: (let ((a!1 (ite (and true (and true (= h1.f1 #xff))) 0 (- 1)))
      (a!2 (ite (and true (= h1.f1 #xff)) #b000000001 (concat #x00 #b0))))
(let ((a!3 (ite (and true (distinct a!1 (- 1)))
                (ite (and true (= h1.f2 #xff)) #b000000010 a!2)
                a!2)))
  (ite (and true (= a!1 (- 1)))
       (ite (and true (= h1.f3 #xff)) #b000000011 a!3)
       a!3)))
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
 (let (($x28 (= h1.f1 (_ bv255 8))))
(let (($x25 (and true $x28)))
(let ((?x34 (ite $x25 (_ bv1 9) (concat (_ bv0 8) (_ bv0 1)))))
(let ((?x27 (ite (and true $x25) 0 (- 1))))
(let (($x35 (and (distinct ?x27 (- 1)) true)))
(let (($x36 (and true $x35)))
(let ((?x43 (ite $x36 (ite (and true (= h1.f2 (_ bv255 8))) (_ bv2 9) ?x34) ?x34)))
(let (($x46 (= ?x27 (- 1))))
(let (($x47 (and true $x46)))
(let ((?x54 (ite $x47 (ite (and true (= h1.f3 (_ bv255 8))) (_ bv3 9) ?x43) ?x43)))
(let (($x78 (or (or (or (or false (= ?x54 (_ bv0 9))) (= ?x54 (_ bv1 9))) (= ?x54 (_ bv2 9))) (= ?x54 (_ bv3 9)))))
(let (($x98 (or (or (or (or $x78 (= ?x54 (_ bv4 9))) (= ?x54 (_ bv5 9))) (= ?x54 (_ bv6 9))) (= ?x54 (_ bv7 9)))))
(let (($x60 (= ?x54 (_ bv511 9))))
(or $x60 $x98)))))))))))))))
(check-sat)
