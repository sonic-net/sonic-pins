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
(egress) standard_metadata.checksum_error: standard_metadata.checksum_error
(egress) standard_metadata.deq_qdepth: standard_metadata.deq_qdepth
(egress) standard_metadata.deq_timedelta: standard_metadata.deq_timedelta
(egress) standard_metadata.egress_global_timestamp: standard_metadata.egress_global_timestamp
(egress) standard_metadata.egress_port: (let ((a!1 (= (ite (and true true (= h1.f1 #xff)) 0 (- 1)) (- 1)))
      (a!2 (distinct (ite (and true true (= h1.f1 #xff)) 0 (- 1)) (- 1))))
(let ((a!3 (ite (and true a!2 true (= h1.f2 #xff))
                #b000000010
                (ite (and true true (= h1.f1 #xff))
                     #b000000001
                     (ite true (concat #x00 #b0) standard_metadata.egress_spec)))))
(let ((a!4 (ite (and true a!1 true (= h1.f3 #xff)) #b000000011 a!3)))
  (ite (not (= a!4 #b111111111)) a!4 standard_metadata.egress_port))))
(egress) standard_metadata.egress_rid: standard_metadata.egress_rid
(egress) standard_metadata.egress_spec: (let ((a!1 (= (ite (and true true (= h1.f1 #xff)) 0 (- 1)) (- 1)))
      (a!2 (distinct (ite (and true true (= h1.f1 #xff)) 0 (- 1)) (- 1))))
(let ((a!3 (ite (and true a!2 true (= h1.f2 #xff))
                #b000000010
                (ite (and true true (= h1.f1 #xff))
                     #b000000001
                     (ite true (concat #x00 #b0) standard_metadata.egress_spec)))))
  (ite (and true a!1 true (= h1.f3 #xff)) #b000000011 a!3)))
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
(declare-fun h1.f1 () (_ BitVec 8))
(declare-fun h1.f2 () (_ BitVec 8))
(declare-fun h1.f3 () (_ BitVec 8))
(assert
 (let (($x103 (= standard_metadata.ingress_port (_ bv7 9))))
 (let (($x98 (= standard_metadata.ingress_port (_ bv6 9))))
 (let (($x93 (= standard_metadata.ingress_port (_ bv5 9))))
 (let (($x88 (= standard_metadata.ingress_port (_ bv4 9))))
 (let (($x83 (= standard_metadata.ingress_port (_ bv3 9))))
 (let (($x79 (= standard_metadata.ingress_port (_ bv2 9))))
 (let (($x75 (= standard_metadata.ingress_port (_ bv1 9))))
 (let (($x80 (or (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x75) $x79)))
 (or (or (or (or (or $x80 $x83) $x88) $x93) $x98) $x103))))))))))
(assert
 (let (($x37 (= h1.f1 (_ bv255 8))))
 (let (($x38 (and true $x37)))
 (let (($x39 (and true $x38)))
 (let ((?x45 (ite $x39 (_ bv1 9) (ite true (concat (_ bv0 8) (_ bv0 1)) standard_metadata.egress_spec))))
 (let ((?x43 (ite $x39 0 (- 1))))
 (let (($x46 (and (distinct ?x43 (- 1)) true)))
 (let (($x47 (and true $x46)))
 (let (($x50 (and $x47 (and true (= h1.f2 (_ bv255 8))))))
 (let (($x56 (= ?x43 (- 1))))
 (let (($x57 (and true $x56)))
 (let (($x60 (and $x57 (and true (= h1.f3 (_ bv255 8))))))
 (let ((?x65 (ite $x60 (_ bv3 9) (ite $x50 (_ bv2 9) ?x45))))
 (let (($x86 (or (or (or (or false (= ?x65 (_ bv0 9))) (= ?x65 (_ bv1 9))) (= ?x65 (_ bv2 9))) (= ?x65 (_ bv3 9)))))
 (let (($x106 (or (or (or (or $x86 (= ?x65 (_ bv4 9))) (= ?x65 (_ bv5 9))) (= ?x65 (_ bv6 9))) (= ?x65 (_ bv7 9)))))
 (let (($x41 (= ?x65 (_ bv511 9))))
 (or $x41 $x106)))))))))))))))))
(check-sat)
