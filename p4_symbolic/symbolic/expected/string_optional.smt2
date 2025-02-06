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
(egress) scalars.metadata.string_field: (let ((a!1 (and true
                (not (and true (= standard_metadata.ingress_port #b000000000)))
                (and true (= standard_metadata.ingress_port #b000000001))))
      (a!2 (and true
                (not (and true (= standard_metadata.ingress_port #b000000000)))
                (not (and true (= standard_metadata.ingress_port #b000000001)))
                true
                (= standard_metadata.ingress_port #b000000010))))
(let ((a!3 (ite a!1
                (concat #x00 #b1)
                (ite a!2
                     (concat #x00 #b0)
                     (ite true (concat #x00 #b0) scalars.metadata.string_field)))))
  (ite (and true (and true (= standard_metadata.ingress_port #b000000000)))
       (concat #b0000000 #b10)
       a!3)))
(egress) standard_metadata.$extracted$: false
(egress) standard_metadata.$valid$: false
(egress) standard_metadata._padding: standard_metadata._padding
(egress) standard_metadata.checksum_error: #b0
(egress) standard_metadata.deq_qdepth: #b0000000000000000000
(egress) standard_metadata.deq_timedelta: #x00000000
(egress) standard_metadata.egress_global_timestamp: #x000000000000
(egress) standard_metadata.egress_port: (let ((a!1 (and true
                (not (and true (= standard_metadata.ingress_port #b000000000)))
                (and true (= standard_metadata.ingress_port #b000000001))))
      (a!2 (and true
                (not (and true (= standard_metadata.ingress_port #b000000000)))
                (not (and true (= standard_metadata.ingress_port #b000000001)))
                true
                (= standard_metadata.ingress_port #b000000010))))
(let ((a!3 (ite a!1
                (concat #x00 #b1)
                (ite a!2
                     (concat #x00 #b0)
                     (ite true (concat #x00 #b0) scalars.metadata.string_field)))))
(let ((a!4 (ite (and true
                     (and true (= standard_metadata.ingress_port #b000000000)))
                (concat #b0000000 #b10)
                a!3)))
(let ((a!5 (and true (and true (= a!4 (concat #b0000000 #b10)))))
      (a!6 (not (and true (= a!4 (concat #b0000000 #b10))))))
(let ((a!7 (ite a!5
                #b000000000
                (ite (and true a!6 true) #b000000001 #b000000000))))
  (ite (not (= a!7 #b111111111)) a!7 standard_metadata.egress_port))))))
(egress) standard_metadata.egress_rid: #x0000
(egress) standard_metadata.egress_spec: (let ((a!1 (and true
                (not (and true (= standard_metadata.ingress_port #b000000000)))
                (and true (= standard_metadata.ingress_port #b000000001))))
      (a!2 (and true
                (not (and true (= standard_metadata.ingress_port #b000000000)))
                (not (and true (= standard_metadata.ingress_port #b000000001)))
                true
                (= standard_metadata.ingress_port #b000000010))))
(let ((a!3 (ite a!1
                (concat #x00 #b1)
                (ite a!2
                     (concat #x00 #b0)
                     (ite true (concat #x00 #b0) scalars.metadata.string_field)))))
(let ((a!4 (ite (and true
                     (and true (= standard_metadata.ingress_port #b000000000)))
                (concat #b0000000 #b10)
                a!3)))
(let ((a!5 (and true (and true (= a!4 (concat #b0000000 #b10)))))
      (a!6 (not (and true (= a!4 (concat #b0000000 #b10))))))
  (ite a!5 #b000000000 (ite (and true a!6 true) #b000000001 #b000000000))))))
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
(declare-fun scalars.metadata.string_field () (_ BitVec 9))
(assert
 (let (($x32 (= standard_metadata.ingress_port (_ bv2 9))))
 (let (($x29 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x29) $x32))))
(assert
 (let ((?x59 (concat (_ bv0 7) (_ bv2 2))))
 (let ((?x24 (concat (_ bv0 8) (_ bv0 1))))
 (let (($x32 (= standard_metadata.ingress_port (_ bv2 9))))
 (let (($x33 (and true $x32)))
 (let (($x14 (= standard_metadata.ingress_port (_ bv0 9))))
 (let (($x19 (and true $x14)))
 (let (($x35 (not $x19)))
 (let (($x40 (and true (and $x35 (not (and true (= standard_metadata.ingress_port (_ bv1 9))))))))
 (let ((?x48 (ite (and $x40 $x33) ?x24 (ite true ?x24 scalars.metadata.string_field))))
 (let (($x29 (= standard_metadata.ingress_port (_ bv1 9))))
 (let (($x30 (and true $x29)))
 (let (($x34 (and true $x19)))
 (let ((?x60 (ite $x34 ?x59 (ite (and (and true $x35) $x30) (concat (_ bv0 8) (_ bv1 1)) ?x48))))
 (let (($x62 (and true (= ?x60 ?x59))))
 (let (($x63 (and true $x62)))
 (let ((?x73 (ite $x63 (_ bv0 9) (ite (and (and true (not $x62)) true) (_ bv1 9) (_ bv0 9)))))
 (let (($x81 (or (or (or false (= ?x73 (_ bv0 9))) (= ?x73 (_ bv1 9))) (= ?x73 (_ bv2 9)))))
 (let (($x43 (= ?x73 (_ bv511 9))))
 (or $x43 $x81))))))))))))))))))))
(check-sat)
