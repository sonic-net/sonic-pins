(ingress) $got_cloned$: false
(ingress) $got_recirculated$: false
(ingress) h1.$extracted$: false
(ingress) h1.$valid$: true
(ingress) h1.f1: h1.f1
(ingress) h1.f2: h1.f2
(ingress) h1.f3: h1.f3
(ingress) h1.f4: h1.f4
(ingress) h1.f5: h1.f5
(ingress) h1.f6: h1.f6
(ingress) h1.f7: h1.f7
(ingress) h1.f8: h1.f8
(ingress) h1.fr: h1.fr
(ingress) h1.fw: h1.fw
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
(parsed) h1.f5: h1.f5
(parsed) h1.f6: h1.f6
(parsed) h1.f7: h1.f7
(parsed) h1.f8: h1.f8
(parsed) h1.fr: h1.fr
(parsed) h1.fw: h1.fw
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
(egress) h1.f5: h1.f5
(egress) h1.f6: h1.f6
(egress) h1.f7: h1.f7
(egress) h1.f8: h1.f8
(egress) h1.fr: h1.fr
(egress) h1.fw: (let ((a!1 (ite (and true (= h1.fr #x14))
                #x0e
                (ite (and true (= h1.fr #x15)) #x0f h1.fw))))
(let ((a!2 (ite (and true (= h1.fr #x12))
                #x0c
                (ite (and true (= h1.fr #x13)) #x0d a!1))))
(let ((a!3 (ite (and true (= h1.fr #x10))
                #x0a
                (ite (and true (= h1.fr #x11)) #x0b a!2))))
(let ((a!4 (ite (and true (= h1.fr #x08))
                #x08
                (ite (and true (= h1.fr #x09)) #x09 a!3))))
(let ((a!5 (ite (and true (= h1.fr #x06))
                #x06
                (ite (and true (= h1.fr #x07)) #x07 a!4))))
(let ((a!6 (ite (and true (= h1.fr #x04))
                #x04
                (ite (and true (= h1.fr #x05)) #x05 a!5))))
(let ((a!7 (ite (and true (= h1.fr #x02))
                #x02
                (ite (and true (= h1.fr #x03)) #x03 a!6))))
  (ite (and true (= h1.fr #x01)) #x01 a!7))))))))
(egress) scalars.$extracted$: false
(egress) scalars.$valid$: false
(egress) standard_metadata.$extracted$: false
(egress) standard_metadata.$valid$: false
(egress) standard_metadata._padding: standard_metadata._padding
(egress) standard_metadata.checksum_error: #b0
(egress) standard_metadata.deq_qdepth: #b0000000000000000000
(egress) standard_metadata.deq_timedelta: #x00000000
(egress) standard_metadata.egress_global_timestamp: #x000000000000
(egress) standard_metadata.egress_port: (ite (not (= #b000000000 #b111111111))
     #b000000000
     standard_metadata.egress_port)
(egress) standard_metadata.egress_rid: #x0000
(egress) standard_metadata.egress_spec: #b000000000
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
(assert
 (let (($x151 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x151)))
(assert
 (let (($x154 (or (or false (= (_ bv0 9) (_ bv0 9))) (= (_ bv0 9) (_ bv1 9)))))
(let (($x143 (= (_ bv0 9) (_ bv511 9))))
(or $x143 $x154))))
(check-sat)
