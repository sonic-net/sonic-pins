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
(parsed) standard_metadata.parser_error: (ite (and true (not true)) #x00000002 #x00000000)
(parsed) standard_metadata.priority: #b000

(egress) $got_cloned$: false
(egress) $got_recirculated$: false
(egress) ethernet.$extracted$: true
(egress) ethernet.$valid$: true
(egress) ethernet.dst_addr: (ite (and true (= ethernet.dst_addr #x000000000001))
     #x000000000002
     ethernet.dst_addr)
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
(egress) standard_metadata.egress_port: (let ((a!1 (= (ite (and true (= ethernet.dst_addr #x000000000001))
                   #b000000001
                   #b111111111)
              #b111111111)))
  (ite (not a!1)
       (ite (and true (= ethernet.dst_addr #x000000000001))
            #b000000001
            #b111111111)
       standard_metadata.egress_port))
(egress) standard_metadata.egress_rid: #x0000
(egress) standard_metadata.egress_spec: (ite (and true (= ethernet.dst_addr #x000000000001)) #b000000001 #b111111111)
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
(declare-fun ethernet.dst_addr () (_ BitVec 48))
(assert
 (let (($x149 (= standard_metadata.ingress_port (_ bv19 9))))
 (let (($x144 (= standard_metadata.ingress_port (_ bv18 9))))
 (let (($x139 (= standard_metadata.ingress_port (_ bv17 9))))
 (let (($x134 (= standard_metadata.ingress_port (_ bv16 9))))
 (let (($x129 (= standard_metadata.ingress_port (_ bv15 9))))
 (let (($x124 (= standard_metadata.ingress_port (_ bv14 9))))
 (let (($x119 (= standard_metadata.ingress_port (_ bv13 9))))
 (let (($x114 (= standard_metadata.ingress_port (_ bv12 9))))
 (let (($x109 (= standard_metadata.ingress_port (_ bv11 9))))
 (let (($x104 (= standard_metadata.ingress_port (_ bv10 9))))
 (let (($x99 (= standard_metadata.ingress_port (_ bv9 9))))
 (let (($x94 (= standard_metadata.ingress_port (_ bv8 9))))
 (let (($x89 (= standard_metadata.ingress_port (_ bv7 9))))
 (let (($x84 (= standard_metadata.ingress_port (_ bv6 9))))
 (let (($x79 (= standard_metadata.ingress_port (_ bv5 9))))
 (let (($x74 (= standard_metadata.ingress_port (_ bv4 9))))
 (let (($x69 (= standard_metadata.ingress_port (_ bv3 9))))
 (let (($x64 (= standard_metadata.ingress_port (_ bv2 9))))
 (let (($x59 (= standard_metadata.ingress_port (_ bv1 9))))
 (let (($x65 (or (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x59) $x64)))
 (let (($x100 (or (or (or (or (or (or (or $x65 $x69) $x74) $x79) $x84) $x89) $x94) $x99)))
 (let (($x135 (or (or (or (or (or (or (or $x100 $x104) $x109) $x114) $x119) $x124) $x129) $x134)))
 (or (or (or $x135 $x139) $x144) $x149))))))))))))))))))))))))
(assert
 (let (($x58 (or false (= (ite (and true (= ethernet.dst_addr (_ bv1 48))) (_ bv1 9) (_ bv511 9)) (_ bv0 9)))))
(let (($x62 (or $x58 (= (ite (and true (= ethernet.dst_addr (_ bv1 48))) (_ bv1 9) (_ bv511 9)) (_ bv1 9)))))
(let (($x67 (or $x62 (= (ite (and true (= ethernet.dst_addr (_ bv1 48))) (_ bv1 9) (_ bv511 9)) (_ bv2 9)))))
(let (($x72 (or $x67 (= (ite (and true (= ethernet.dst_addr (_ bv1 48))) (_ bv1 9) (_ bv511 9)) (_ bv3 9)))))
(let (($x77 (or $x72 (= (ite (and true (= ethernet.dst_addr (_ bv1 48))) (_ bv1 9) (_ bv511 9)) (_ bv4 9)))))
(let (($x82 (or $x77 (= (ite (and true (= ethernet.dst_addr (_ bv1 48))) (_ bv1 9) (_ bv511 9)) (_ bv5 9)))))
(let (($x87 (or $x82 (= (ite (and true (= ethernet.dst_addr (_ bv1 48))) (_ bv1 9) (_ bv511 9)) (_ bv6 9)))))
(let (($x92 (or $x87 (= (ite (and true (= ethernet.dst_addr (_ bv1 48))) (_ bv1 9) (_ bv511 9)) (_ bv7 9)))))
(let (($x97 (or $x92 (= (ite (and true (= ethernet.dst_addr (_ bv1 48))) (_ bv1 9) (_ bv511 9)) (_ bv8 9)))))
(let (($x102 (or $x97 (= (ite (and true (= ethernet.dst_addr (_ bv1 48))) (_ bv1 9) (_ bv511 9)) (_ bv9 9)))))
(let (($x107 (or $x102 (= (ite (and true (= ethernet.dst_addr (_ bv1 48))) (_ bv1 9) (_ bv511 9)) (_ bv10 9)))))
(let (($x112 (or $x107 (= (ite (and true (= ethernet.dst_addr (_ bv1 48))) (_ bv1 9) (_ bv511 9)) (_ bv11 9)))))
(let (($x117 (or $x112 (= (ite (and true (= ethernet.dst_addr (_ bv1 48))) (_ bv1 9) (_ bv511 9)) (_ bv12 9)))))
(let (($x122 (or $x117 (= (ite (and true (= ethernet.dst_addr (_ bv1 48))) (_ bv1 9) (_ bv511 9)) (_ bv13 9)))))
(let (($x127 (or $x122 (= (ite (and true (= ethernet.dst_addr (_ bv1 48))) (_ bv1 9) (_ bv511 9)) (_ bv14 9)))))
(let (($x132 (or $x127 (= (ite (and true (= ethernet.dst_addr (_ bv1 48))) (_ bv1 9) (_ bv511 9)) (_ bv15 9)))))
(let (($x137 (or $x132 (= (ite (and true (= ethernet.dst_addr (_ bv1 48))) (_ bv1 9) (_ bv511 9)) (_ bv16 9)))))
(let (($x142 (or $x137 (= (ite (and true (= ethernet.dst_addr (_ bv1 48))) (_ bv1 9) (_ bv511 9)) (_ bv17 9)))))
(let (($x147 (or $x142 (= (ite (and true (= ethernet.dst_addr (_ bv1 48))) (_ bv1 9) (_ bv511 9)) (_ bv18 9)))))
(let (($x152 (or $x147 (= (ite (and true (= ethernet.dst_addr (_ bv1 48))) (_ bv1 9) (_ bv511 9)) (_ bv19 9)))))
(let (($x43 (= ethernet.dst_addr (_ bv1 48))))
(let (($x44 (and true $x43)))
(let ((?x51 (ite $x44 (_ bv1 9) (_ bv511 9))))
(let (($x52 (= ?x51 (_ bv511 9))))
(or $x52 $x152))))))))))))))))))))))))))
(check-sat)
