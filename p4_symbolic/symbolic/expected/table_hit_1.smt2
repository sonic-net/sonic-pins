(ingress) $got_cloned$: false
(ingress) ethernet.$extracted$: false
(ingress) ethernet.$valid$: (ite true true false)
(ingress) ethernet.dst_addr: ethernet.dst_addr
(ingress) ethernet.ether_type: ethernet.ether_type
(ingress) ethernet.src_addr: ethernet.src_addr
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
(parsed) ethernet.$extracted$: (ite true true false)
(parsed) ethernet.$valid$: (ite true true false)
(parsed) ethernet.dst_addr: ethernet.dst_addr
(parsed) ethernet.ether_type: ethernet.ether_type
(parsed) ethernet.src_addr: ethernet.src_addr
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
(egress) ethernet.$extracted$: (ite true true false)
(egress) ethernet.$valid$: (ite true true false)
(egress) ethernet.dst_addr: (let ((a!1 (distinct (ite (and true true (= ethernet.ether_type #x0010))
                          0
                          (- 1))
                     (- 1))))
  (ite (and true a!1 true (= ethernet.src_addr #x000000000100))
       #x000000000003
       (ite (and true true (= ethernet.ether_type #x0010))
            #x000000000002
            ethernet.dst_addr)))
(egress) ethernet.ether_type: ethernet.ether_type
(egress) ethernet.src_addr: ethernet.src_addr
(egress) scalars.$extracted$: false
(egress) scalars.$valid$: false
(egress) standard_metadata.$extracted$: false
(egress) standard_metadata.$valid$: false
(egress) standard_metadata._padding: standard_metadata._padding
(egress) standard_metadata.checksum_error: standard_metadata.checksum_error
(egress) standard_metadata.deq_qdepth: standard_metadata.deq_qdepth
(egress) standard_metadata.deq_timedelta: standard_metadata.deq_timedelta
(egress) standard_metadata.egress_global_timestamp: standard_metadata.egress_global_timestamp
(egress) standard_metadata.egress_port: (let ((a!1 (ite (and true (and true (= ethernet.ether_type #x0010))) 0 (- 1)))
      (a!2 (and true (not (and true (= ethernet.ether_type #x0010))))))
(let ((a!3 (ite (and true (and true (= ethernet.ether_type #x0010)))
                #b000000010
                (ite a!2 #b111111111 standard_metadata.egress_spec))))
(let ((a!4 (ite (and true
                     (distinct a!1 (- 1))
                     true
                     (= ethernet.src_addr #x000000000100))
                #b000000011
                a!3)))
  (ite (not (= a!4 #b111111111)) a!4 standard_metadata.egress_port))))
(egress) standard_metadata.egress_rid: standard_metadata.egress_rid
(egress) standard_metadata.egress_spec: (let ((a!1 (ite (and true (and true (= ethernet.ether_type #x0010))) 0 (- 1)))
      (a!2 (and true (not (and true (= ethernet.ether_type #x0010))))))
(let ((a!3 (ite (and true (and true (= ethernet.ether_type #x0010)))
                #b000000010
                (ite a!2 #b111111111 standard_metadata.egress_spec))))
  (ite (and true (distinct a!1 (- 1)) true (= ethernet.src_addr #x000000000100))
       #b000000011
       a!3)))
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
(declare-fun ethernet.ether_type () (_ BitVec 16))
(declare-fun ethernet.src_addr () (_ BitVec 48))
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
 (let ((?x38 (ite (and true (not (and true (= ethernet.ether_type (_ bv16 16))))) (_ bv511 9) standard_metadata.egress_spec)))
 (let (($x31 (= ethernet.ether_type (_ bv16 16))))
 (let (($x32 (and true $x31)))
 (let (($x33 (and true $x32)))
 (let ((?x40 (ite $x33 0 (- 1))))
 (let (($x45 (and (distinct ?x40 (- 1)) true)))
 (let (($x46 (and true $x45)))
 (let (($x50 (and $x46 (and true (= ethernet.src_addr (_ bv256 48))))))
 (let ((?x56 (ite $x50 (_ bv3 9) (ite $x33 (_ bv2 9) ?x38))))
 (let (($x78 (or (or (or (or false (= ?x56 (_ bv0 9))) (= ?x56 (_ bv1 9))) (= ?x56 (_ bv2 9))) (= ?x56 (_ bv3 9)))))
 (let (($x98 (or (or (or (or $x78 (= ?x56 (_ bv4 9))) (= ?x56 (_ bv5 9))) (= ?x56 (_ bv6 9))) (= ?x56 (_ bv7 9)))))
 (let (($x58 (= ?x56 (_ bv511 9))))
 (or $x58 $x98))))))))))))))
(check-sat)
