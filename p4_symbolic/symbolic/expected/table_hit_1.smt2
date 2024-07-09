(ingress) $got_cloned$: false
(ingress) $got_recirculated$: false
(ingress) ethernet.$extracted$: false
(ingress) ethernet.$valid$: true
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
(parsed) ethernet.$extracted$: true
(parsed) ethernet.$valid$: true
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
(parsed) standard_metadata.parser_error: #x00000000
(parsed) standard_metadata.priority: #b000

(egress) $got_cloned$: false
(egress) $got_recirculated$: false
(egress) ethernet.$extracted$: true
(egress) ethernet.$valid$: true
(egress) ethernet.dst_addr: (ite (and (= ethernet.ether_type #x0010) (= ethernet.src_addr #x000000000100))
     #x000000000003
     (ite (= ethernet.ether_type #x0010) #x000000000002 ethernet.dst_addr))
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
(egress) standard_metadata.egress_port: (let ((a!1 (and (not (= ethernet.ether_type #x0010))
                (not (and (= ethernet.ether_type #x0010)
                          (= ethernet.src_addr #x000000000100))))))
  (ite a!1
       standard_metadata.egress_port
       (ite (and (= ethernet.ether_type #x0010)
                 (= ethernet.src_addr #x000000000100))
            #b000000011
            (ite (= ethernet.ether_type #x0010) #b000000010 #b111111111))))
(egress) standard_metadata.egress_rid: #x0000
(egress) standard_metadata.egress_spec: (ite (and (= ethernet.ether_type #x0010) (= ethernet.src_addr #x000000000100))
     #b000000011
     (ite (= ethernet.ether_type #x0010) #b000000010 #b111111111))
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
(declare-fun ethernet.ether_type () (_ BitVec 16))
(declare-fun ethernet.src_addr () (_ BitVec 48))
(assert
 (let (($x82 (= standard_metadata.ingress_port (_ bv7 9))))
 (let (($x77 (= standard_metadata.ingress_port (_ bv6 9))))
 (let (($x72 (= standard_metadata.ingress_port (_ bv5 9))))
 (let (($x67 (= standard_metadata.ingress_port (_ bv4 9))))
 (let (($x62 (= standard_metadata.ingress_port (_ bv3 9))))
 (let (($x58 (= standard_metadata.ingress_port (_ bv2 9))))
 (let (($x54 (= standard_metadata.ingress_port (_ bv1 9))))
 (let (($x59 (or (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x54) $x58)))
 (or (or (or (or (or $x59 $x62) $x67) $x72) $x77) $x82))))))))))
(assert
 (let (($x34 (= ethernet.src_addr (_ bv256 48))))
 (let (($x11 (= ethernet.ether_type (_ bv16 16))))
 (let (($x37 (and $x11 $x34)))
 (let ((?x43 (ite $x37 (_ bv3 9) (ite $x11 (_ bv2 9) (_ bv511 9)))))
 (let (($x65 (or (or (or (or false (= ?x43 (_ bv0 9))) (= ?x43 (_ bv1 9))) (= ?x43 (_ bv2 9))) (= ?x43 (_ bv3 9)))))
 (let (($x85 (or (or (or (or $x65 (= ?x43 (_ bv4 9))) (= ?x43 (_ bv5 9))) (= ?x43 (_ bv6 9))) (= ?x43 (_ bv7 9)))))
 (let (($x5 (= ?x43 (_ bv511 9))))
 (or $x5 $x85)))))))))
(check-sat)
