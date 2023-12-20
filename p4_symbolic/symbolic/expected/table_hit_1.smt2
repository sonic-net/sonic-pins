(ingress) $got_cloned$: false
(ingress) $got_recirculated$: false
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
(egress) standard_metadata.checksum_error: #b0
(egress) standard_metadata.deq_qdepth: #b0000000000000000000
(egress) standard_metadata.deq_timedelta: #x00000000
(egress) standard_metadata.egress_global_timestamp: #x000000000000
(egress) standard_metadata.egress_port: (let ((a!1 (ite (and true (and true (= ethernet.ether_type #x0010))) 0 (- 1)))
      (a!2 (and true (not (and true (= ethernet.ether_type #x0010))))))
(let ((a!3 (ite (and true (and true (= ethernet.ether_type #x0010)))
                #b000000010
                (ite a!2 #b111111111 #b000000000))))
(let ((a!4 (ite (and true
                     (distinct a!1 (- 1))
                     true
                     (= ethernet.src_addr #x000000000100))
                #b000000011
                a!3)))
  (ite (not (= a!4 #b111111111)) a!4 standard_metadata.egress_port))))
(egress) standard_metadata.egress_rid: #x0000
(egress) standard_metadata.egress_spec: (let ((a!1 (ite (and true (and true (= ethernet.ether_type #x0010))) 0 (- 1)))
      (a!2 (and true (not (and true (= ethernet.ether_type #x0010))))))
(let ((a!3 (ite (and true (and true (= ethernet.ether_type #x0010)))
                #b000000010
                (ite a!2 #b111111111 #b000000000))))
  (ite (and true (distinct a!1 (- 1)) true (= ethernet.src_addr #x000000000100))
       #b000000011
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
(declare-fun ethernet.ether_type () (_ BitVec 16))
(declare-fun ethernet.src_addr () (_ BitVec 48))
(assert
 (let (($x88 (= standard_metadata.ingress_port (_ bv7 9))))
 (let (($x83 (= standard_metadata.ingress_port (_ bv6 9))))
 (let (($x78 (= standard_metadata.ingress_port (_ bv5 9))))
 (let (($x73 (= standard_metadata.ingress_port (_ bv4 9))))
 (let (($x68 (= standard_metadata.ingress_port (_ bv3 9))))
 (let (($x64 (= standard_metadata.ingress_port (_ bv2 9))))
 (let (($x60 (= standard_metadata.ingress_port (_ bv1 9))))
 (let (($x65 (or (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x60) $x64)))
 (or (or (or (or (or $x65 $x68) $x73) $x78) $x83) $x88))))))))))
(assert
 (let ((?x32 (ite (and true (not (and true (= ethernet.ether_type (_ bv16 16))))) (_ bv511 9) (_ bv0 9))))
 (let (($x30 (= ethernet.ether_type (_ bv16 16))))
 (let (($x15 (and true $x30)))
 (let (($x27 (and true $x15)))
 (let ((?x34 (ite $x27 0 (- 1))))
 (let (($x39 (and (distinct ?x34 (- 1)) true)))
 (let (($x40 (and true $x39)))
 (let (($x44 (and $x40 (and true (= ethernet.src_addr (_ bv256 48))))))
 (let ((?x50 (ite $x44 (_ bv3 9) (ite $x27 (_ bv2 9) ?x32))))
 (let (($x71 (or (or (or (or false (= ?x50 (_ bv0 9))) (= ?x50 (_ bv1 9))) (= ?x50 (_ bv2 9))) (= ?x50 (_ bv3 9)))))
 (let (($x91 (or (or (or (or $x71 (= ?x50 (_ bv4 9))) (= ?x50 (_ bv5 9))) (= ?x50 (_ bv6 9))) (= ?x50 (_ bv7 9)))))
 (let (($x52 (= ?x50 (_ bv511 9))))
 (or $x52 $x91))))))))))))))
(check-sat)
