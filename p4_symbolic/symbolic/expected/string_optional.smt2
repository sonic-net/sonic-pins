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
(parsed) standard_metadata.parser_error: (ite (and true (not true)) #x00000002 #x00000000)
(parsed) standard_metadata.priority: #b000

(egress) $got_cloned$: false
(egress) $got_recirculated$: false
(egress) scalars.$extracted$: false
(egress) scalars.$valid$: false
(egress) scalars._padding_0: scalars._padding_0
(egress) scalars.metadata.string_field: (ite (and true (= standard_metadata.ingress_port #b000000000))
     (concat #b0000000 #b10)
     (ite (and true (= standard_metadata.ingress_port #b000000001))
          (concat #x00 #b1)
          (concat #x00 #b0)))
(egress) standard_metadata.$extracted$: false
(egress) standard_metadata.$valid$: false
(egress) standard_metadata._padding: standard_metadata._padding
(egress) standard_metadata.checksum_error: #b0
(egress) standard_metadata.deq_qdepth: #b0000000000000000000
(egress) standard_metadata.deq_timedelta: #x00000000
(egress) standard_metadata.egress_global_timestamp: #x000000000000
(egress) standard_metadata.egress_port: (let ((a!1 (ite (and true (= standard_metadata.ingress_port #b000000000))
                (concat #b0000000 #b10)
                (ite (and true (= standard_metadata.ingress_port #b000000001))
                     (concat #x00 #b1)
                     (concat #x00 #b0)))))
(let ((a!2 (ite (and true (= a!1 (concat #b0000000 #b10)))
                #b000000000
                (ite true #b000000001 #b000000000))))
  (ite (not (= a!2 #b111111111)) a!2 standard_metadata.egress_port)))
(egress) standard_metadata.egress_rid: #x0000
(egress) standard_metadata.egress_spec: (let ((a!1 (ite (and true (= standard_metadata.ingress_port #b000000000))
                (concat #b0000000 #b10)
                (ite (and true (= standard_metadata.ingress_port #b000000001))
                     (concat #x00 #b1)
                     (concat #x00 #b0)))))
  (ite (and true (= a!1 (concat #b0000000 #b10)))
       #b000000000
       (ite true #b000000001 #b000000000)))
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
 (let (($x31 (= standard_metadata.ingress_port (_ bv2 9))))
 (let (($x23 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x23) $x31))))
(assert
 (let ((?x46 (concat (_ bv0 7) (_ bv2 2))))
(let (($x23 (= standard_metadata.ingress_port (_ bv1 9))))
(let (($x29 (and true $x23)))
(let (($x21 (= standard_metadata.ingress_port (_ bv0 9))))
(let (($x14 (and true $x21)))
(let ((?x48 (ite $x14 ?x46 (ite $x29 (concat (_ bv0 8) (_ bv1 1)) (concat (_ bv0 8) (_ bv0 1))))))
(let (($x50 (and true (= ?x48 ?x46))))
(let ((?x56 (ite $x50 (_ bv0 9) (ite true (_ bv1 9) (_ bv0 9)))))
(let (($x69 (or (or (or false (= ?x56 (_ bv0 9))) (= ?x56 (_ bv1 9))) (= ?x56 (_ bv2 9)))))
(let (($x58 (= ?x56 (_ bv511 9))))
(or $x58 $x69))))))))))))
(check-sat)
