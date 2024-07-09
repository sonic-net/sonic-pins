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
(parsed) standard_metadata.parser_error: #x00000000
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
(egress) standard_metadata.egress_port: (ite (and (not (= h1.f1 #xff)) (= h1.f3 #xff))
     #b000000011
     (ite (and (= h1.f1 #xff) (= h1.f2 #xff))
          #b000000010
          (ite (= h1.f1 #xff) #b000000001 #b000000000)))
(egress) standard_metadata.egress_rid: #x0000
(egress) standard_metadata.egress_spec: (ite (and (not (= h1.f1 #xff)) (= h1.f3 #xff))
     #b000000011
     (ite (and (= h1.f1 #xff) (= h1.f2 #xff))
          #b000000010
          (ite (= h1.f1 #xff) #b000000001 #b000000000)))
(egress) standard_metadata.enq_qdepth: #b0000000000000000000
(egress) standard_metadata.enq_timestamp: #x00000000
(egress) standard_metadata.ingress_global_timestamp: #x000000000000
(egress) standard_metadata.ingress_port: standard_metadata.ingress_port
(egress) standard_metadata.instance_type: #x00000000
(egress) standard_metadata.mcast_grp: #x0000
(egress) standard_metadata.packet_length: standard_metadata.packet_length
(egress) standard_metadata.parser_error: #x00000000
(egress) standard_metadata.priority: #b000

(solver constraints)
; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(declare-fun h1.f1 () (_ BitVec 8))
(declare-fun h1.f2 () (_ BitVec 8))
(declare-fun h1.f3 () (_ BitVec 8))
(assert
 (let (($x86 (= standard_metadata.ingress_port (_ bv7 9))))
 (let (($x81 (= standard_metadata.ingress_port (_ bv6 9))))
 (let (($x76 (= standard_metadata.ingress_port (_ bv5 9))))
 (let (($x71 (= standard_metadata.ingress_port (_ bv4 9))))
 (let (($x66 (= standard_metadata.ingress_port (_ bv3 9))))
 (let (($x62 (= standard_metadata.ingress_port (_ bv2 9))))
 (let (($x58 (= standard_metadata.ingress_port (_ bv1 9))))
 (let (($x63 (or (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x58) $x62)))
 (or (or (or (or (or $x63 $x66) $x71) $x76) $x81) $x86))))))))))
(assert
 (let (($x23 (= h1.f2 (_ bv255 8))))
 (let (($x11 (= h1.f1 (_ bv255 8))))
 (let (($x34 (and $x11 $x23)))
 (let (($x41 (= h1.f3 (_ bv255 8))))
 (let (($x31 (not $x11)))
 (let (($x44 (and $x31 $x41)))
 (let ((?x49 (ite $x44 (_ bv3 9) (ite $x34 (_ bv2 9) (ite $x11 (_ bv1 9) (_ bv0 9))))))
 (let (($x69 (or (or (or (or false (= ?x49 (_ bv0 9))) (= ?x49 (_ bv1 9))) (= ?x49 (_ bv2 9))) (= ?x49 (_ bv3 9)))))
 (let (($x89 (or (or (or (or $x69 (= ?x49 (_ bv4 9))) (= ?x49 (_ bv5 9))) (= ?x49 (_ bv6 9))) (= ?x49 (_ bv7 9)))))
 (let (($x53 (= ?x49 (_ bv511 9))))
 (or $x53 $x89))))))))))))
(check-sat)
