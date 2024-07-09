(ingress) $got_cloned$: false
(ingress) $got_recirculated$: false
(ingress) scalars.$extracted$: false
(ingress) scalars.$valid$: false
(ingress) scalars._padding_0: scalars._padding_0
(ingress) scalars.metadata.string_field: scalars.metadata.string_field
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
(parsed) scalars.$extracted$: false
(parsed) scalars.$valid$: false
(parsed) scalars._padding_0: scalars._padding_0
(parsed) scalars.metadata.string_field: scalars.metadata.string_field
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
(egress) scalars.$extracted$: false
(egress) scalars.$valid$: false
(egress) scalars._padding_0: scalars._padding_0
(egress) scalars.metadata.string_field: (let ((a!1 (ite (and (not (= standard_metadata.ingress_port #b000000000))
                     (= standard_metadata.ingress_port #b000000001))
                #b000000001
                #b000000000)))
  (ite (= standard_metadata.ingress_port #b000000000) #b000000010 a!1))
(egress) standard_metadata.$extracted$: false
(egress) standard_metadata.$valid$: false
(egress) standard_metadata._padding: standard_metadata._padding
(egress) standard_metadata.checksum_error: #b0
(egress) standard_metadata.deq_qdepth: #b0000000000000000000
(egress) standard_metadata.deq_timedelta: #x00000000
(egress) standard_metadata.egress_global_timestamp: #x000000000000
(egress) standard_metadata.egress_port: (ite (= standard_metadata.ingress_port #b000000000) #b000000000 #b000000001)
(egress) standard_metadata.egress_rid: #x0000
(egress) standard_metadata.egress_spec: (ite (= standard_metadata.ingress_port #b000000000) #b000000000 #b000000001)
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
(assert
 (let (($x21 (= standard_metadata.ingress_port (_ bv2 9))))
 (let (($x27 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x27) $x21))))
(assert
 (let (($x54 (or false (= (ite (= standard_metadata.ingress_port (_ bv0 9)) (_ bv0 9) (_ bv1 9)) (_ bv0 9)))))
 (let (($x57 (or $x54 (= (ite (= standard_metadata.ingress_port (_ bv0 9)) (_ bv0 9) (_ bv1 9)) (_ bv1 9)))))
 (let (($x60 (or $x57 (= (ite (= standard_metadata.ingress_port (_ bv0 9)) (_ bv0 9) (_ bv1 9)) (_ bv2 9)))))
 (let (($x6 (= standard_metadata.ingress_port (_ bv0 9))))
 (let ((?x53 (ite $x6 (_ bv0 9) (_ bv1 9))))
 (let (($x38 (= ?x53 (_ bv511 9))))
 (or $x38 $x60))))))))
(check-sat)
