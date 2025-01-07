(ingress) $got_cloned$: false
(ingress) scalars.$extracted$: false
(ingress) scalars.$valid$: false
(ingress) scalars._padding_0: scalars._padding_0
(ingress) scalars.metadata.string_field: scalars.metadata.string_field
(ingress) standard_metadata.$extracted$: false
(ingress) standard_metadata.$valid$: false
(ingress) standard_metadata._padding: standard_metadata._padding
(ingress) standard_metadata.checksum_error: standard_metadata.checksum_error
(ingress) standard_metadata.deq_qdepth: standard_metadata.deq_qdepth
(ingress) standard_metadata.deq_timedelta: standard_metadata.deq_timedelta
(ingress) standard_metadata.egress_global_timestamp: standard_metadata.egress_global_timestamp
(ingress) standard_metadata.egress_port: standard_metadata.egress_port
(ingress) standard_metadata.egress_rid: standard_metadata.egress_rid
(ingress) standard_metadata.egress_spec: standard_metadata.egress_spec
(ingress) standard_metadata.enq_qdepth: standard_metadata.enq_qdepth
(ingress) standard_metadata.enq_timestamp: standard_metadata.enq_timestamp
(ingress) standard_metadata.ingress_global_timestamp: standard_metadata.ingress_global_timestamp
(ingress) standard_metadata.ingress_port: standard_metadata.ingress_port
(ingress) standard_metadata.instance_type: standard_metadata.instance_type
(ingress) standard_metadata.mcast_grp: standard_metadata.mcast_grp
(ingress) standard_metadata.packet_length: standard_metadata.packet_length
(ingress) standard_metadata.parser_error: #x00000000
(ingress) standard_metadata.priority: standard_metadata.priority

(parsed) $got_cloned$: false
(parsed) scalars.$extracted$: false
(parsed) scalars.$valid$: false
(parsed) scalars._padding_0: scalars._padding_0
(parsed) scalars.metadata.string_field: scalars.metadata.string_field
(parsed) standard_metadata.$extracted$: false
(parsed) standard_metadata.$valid$: false
(parsed) standard_metadata._padding: standard_metadata._padding
(parsed) standard_metadata.checksum_error: standard_metadata.checksum_error
(parsed) standard_metadata.deq_qdepth: standard_metadata.deq_qdepth
(parsed) standard_metadata.deq_timedelta: standard_metadata.deq_timedelta
(parsed) standard_metadata.egress_global_timestamp: standard_metadata.egress_global_timestamp
(parsed) standard_metadata.egress_port: standard_metadata.egress_port
(parsed) standard_metadata.egress_rid: standard_metadata.egress_rid
(parsed) standard_metadata.egress_spec: standard_metadata.egress_spec
(parsed) standard_metadata.enq_qdepth: standard_metadata.enq_qdepth
(parsed) standard_metadata.enq_timestamp: standard_metadata.enq_timestamp
(parsed) standard_metadata.ingress_global_timestamp: standard_metadata.ingress_global_timestamp
(parsed) standard_metadata.ingress_port: standard_metadata.ingress_port
(parsed) standard_metadata.instance_type: standard_metadata.instance_type
(parsed) standard_metadata.mcast_grp: standard_metadata.mcast_grp
(parsed) standard_metadata.packet_length: standard_metadata.packet_length
(parsed) standard_metadata.parser_error: (ite (and true (not true)) #x00000002 #x00000000)
(parsed) standard_metadata.priority: standard_metadata.priority

(egress) $got_cloned$: false
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
(egress) standard_metadata.checksum_error: standard_metadata.checksum_error
(egress) standard_metadata.deq_qdepth: standard_metadata.deq_qdepth
(egress) standard_metadata.deq_timedelta: standard_metadata.deq_timedelta
(egress) standard_metadata.egress_global_timestamp: standard_metadata.egress_global_timestamp
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
                (ite (and true a!6 true)
                     #b000000001
                     standard_metadata.egress_spec))))
  (ite (not (= a!7 #b111111111)) a!7 standard_metadata.egress_port))))))
(egress) standard_metadata.egress_rid: standard_metadata.egress_rid
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
  (ite a!5
       #b000000000
       (ite (and true a!6 true) #b000000001 standard_metadata.egress_spec))))))
(egress) standard_metadata.enq_qdepth: standard_metadata.enq_qdepth
(egress) standard_metadata.enq_timestamp: standard_metadata.enq_timestamp
(egress) standard_metadata.ingress_global_timestamp: standard_metadata.ingress_global_timestamp
(egress) standard_metadata.ingress_port: standard_metadata.ingress_port
(egress) standard_metadata.instance_type: standard_metadata.instance_type
(egress) standard_metadata.mcast_grp: standard_metadata.mcast_grp
(egress) standard_metadata.packet_length: standard_metadata.packet_length
(egress) standard_metadata.parser_error: (ite (and true (not true)) #x00000002 #x00000000)
(egress) standard_metadata.priority: standard_metadata.priority

(solver constraints)
; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(declare-fun standard_metadata.egress_spec () (_ BitVec 9))
(declare-fun scalars.metadata.string_field () (_ BitVec 9))
(assert
 (let (($x40 (= standard_metadata.ingress_port (_ bv2 9))))
 (let (($x37 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x37) $x40))))
(assert
 (let ((?x67 (concat (_ bv0 7) (_ bv2 2))))
 (let ((?x31 (concat (_ bv0 8) (_ bv0 1))))
 (let (($x40 (= standard_metadata.ingress_port (_ bv2 9))))
 (let (($x41 (and true $x40)))
 (let (($x34 (= standard_metadata.ingress_port (_ bv0 9))))
 (let (($x35 (and true $x34)))
 (let (($x43 (not $x35)))
 (let (($x48 (and true (and $x43 (not (and true (= standard_metadata.ingress_port (_ bv1 9))))))))
 (let ((?x56 (ite (and $x48 $x41) ?x31 (ite true ?x31 scalars.metadata.string_field))))
 (let (($x37 (= standard_metadata.ingress_port (_ bv1 9))))
 (let (($x38 (and true $x37)))
 (let (($x42 (and true $x35)))
 (let ((?x68 (ite $x42 ?x67 (ite (and (and true $x43) $x38) (concat (_ bv0 8) (_ bv1 1)) ?x56))))
 (let (($x70 (and true (= ?x68 ?x67))))
 (let ((?x79 (ite (and (and true (not $x70)) true) (_ bv1 9) standard_metadata.egress_spec)))
 (let (($x71 (and true $x70)))
 (let ((?x81 (ite $x71 (_ bv0 9) ?x79)))
 (let (($x89 (or (or (or false (= ?x81 (_ bv0 9))) (= ?x81 (_ bv1 9))) (= ?x81 (_ bv2 9)))))
 (let (($x51 (= ?x81 (_ bv511 9))))
 (or $x51 $x89)))))))))))))))))))))
(check-sat)
