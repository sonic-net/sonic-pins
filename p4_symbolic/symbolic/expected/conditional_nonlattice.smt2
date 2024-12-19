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
(egress) ethernet.dst_addr: (ite (and true true (= ethernet.dst_addr #x000000000001))
     #x000000000002
     ethernet.dst_addr)
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
(egress) standard_metadata.egress_port: (let ((a!1 (and true (not (and true (= ethernet.dst_addr #x000000000001)))))
      (a!2 (and true
                (not (bvugt standard_metadata.ingress_port (concat #b00000 #xa)))))
      (a!4 (and (and true
                     (bvugt standard_metadata.ingress_port (concat #b00000 #xa)))
                (not (bvugt standard_metadata.ingress_port (concat #b00000 #xf)))))
      (a!5 (and (and true
                     (bvugt standard_metadata.ingress_port (concat #b00000 #xa)))
                (bvugt standard_metadata.ingress_port (concat #b00000 #xf)))))
(let ((a!3 (and a!2
                (not (bvugt standard_metadata.ingress_port
                            (concat #b000000 #b101)))))
      (a!6 (ite (and a!2
                     (bvugt standard_metadata.ingress_port
                            (concat #b000000 #b101)))
                #b111111111
                (ite a!4
                     #b111111111
                     (ite a!5 #b111111111 standard_metadata.egress_spec)))))
(let ((a!7 (ite (and true (and true (= ethernet.dst_addr #x000000000001)))
                #b000000001
                (ite a!1 #b111111111 (ite a!3 #b111111111 a!6)))))
  (ite true a!7 standard_metadata.egress_port))))
(egress) standard_metadata.egress_rid: standard_metadata.egress_rid
(egress) standard_metadata.egress_spec: (let ((a!1 (and true (not (and true (= ethernet.dst_addr #x000000000001)))))
      (a!2 (and true
                (not (bvugt standard_metadata.ingress_port (concat #b00000 #xa)))))
      (a!4 (and (and true
                     (bvugt standard_metadata.ingress_port (concat #b00000 #xa)))
                (not (bvugt standard_metadata.ingress_port (concat #b00000 #xf)))))
      (a!5 (and (and true
                     (bvugt standard_metadata.ingress_port (concat #b00000 #xa)))
                (bvugt standard_metadata.ingress_port (concat #b00000 #xf)))))
(let ((a!3 (and a!2
                (not (bvugt standard_metadata.ingress_port
                            (concat #b000000 #b101)))))
      (a!6 (ite (and a!2
                     (bvugt standard_metadata.ingress_port
                            (concat #b000000 #b101)))
                #b111111111
                (ite a!4
                     #b111111111
                     (ite a!5 #b111111111 standard_metadata.egress_spec)))))
  (ite (and true (and true (= ethernet.dst_addr #x000000000001)))
       #b000000001
       (ite a!1 #b111111111 (ite a!3 #b111111111 a!6)))))
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
(declare-fun ethernet.dst_addr () (_ BitVec 48))
(assert
 (let (($x172 (= standard_metadata.ingress_port (_ bv19 9))))
 (let (($x167 (= standard_metadata.ingress_port (_ bv18 9))))
 (let (($x162 (= standard_metadata.ingress_port (_ bv17 9))))
 (let (($x157 (= standard_metadata.ingress_port (_ bv16 9))))
 (let (($x152 (= standard_metadata.ingress_port (_ bv15 9))))
 (let (($x147 (= standard_metadata.ingress_port (_ bv14 9))))
 (let (($x142 (= standard_metadata.ingress_port (_ bv13 9))))
 (let (($x137 (= standard_metadata.ingress_port (_ bv12 9))))
 (let (($x132 (= standard_metadata.ingress_port (_ bv11 9))))
 (let (($x127 (= standard_metadata.ingress_port (_ bv10 9))))
 (let (($x122 (= standard_metadata.ingress_port (_ bv9 9))))
 (let (($x117 (= standard_metadata.ingress_port (_ bv8 9))))
 (let (($x112 (= standard_metadata.ingress_port (_ bv7 9))))
 (let (($x107 (= standard_metadata.ingress_port (_ bv6 9))))
 (let (($x102 (= standard_metadata.ingress_port (_ bv5 9))))
 (let (($x97 (= standard_metadata.ingress_port (_ bv4 9))))
 (let (($x92 (= standard_metadata.ingress_port (_ bv3 9))))
 (let (($x87 (= standard_metadata.ingress_port (_ bv2 9))))
 (let (($x82 (= standard_metadata.ingress_port (_ bv1 9))))
 (let (($x88 (or (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x82) $x87)))
 (let (($x123 (or (or (or (or (or (or (or $x88 $x92) $x97) $x102) $x107) $x112) $x117) $x122)))
 (let (($x158 (or (or (or (or (or (or (or $x123 $x127) $x132) $x137) $x142) $x147) $x152) $x157)))
 (or (or (or $x158 $x162) $x167) $x172))))))))))))))))))))))))
(assert
 (let (($x39 (bvugt standard_metadata.ingress_port (concat (_ bv0 5) (_ bv15 4)))))
 (let (($x33 (bvugt standard_metadata.ingress_port (concat (_ bv0 5) (_ bv10 4)))))
 (let (($x35 (and true $x33)))
 (let (($x41 (and $x35 $x39)))
 (let (($x42 (and $x35 (not $x39))))
 (let (($x52 (bvugt standard_metadata.ingress_port (concat (_ bv0 6) (_ bv5 3)))))
 (let (($x36 (and true (not $x33))))
 (let (($x54 (and $x36 $x52)))
 (let ((?x56 (ite $x54 (_ bv511 9) (ite $x42 (_ bv511 9) (ite $x41 (_ bv511 9) standard_metadata.egress_spec)))))
 (let (($x55 (and $x36 (not $x52))))
 (let ((?x68 (ite (and true (not (and true (= ethernet.dst_addr (_ bv1 48))))) (_ bv511 9) (ite $x55 (_ bv511 9) ?x56))))
 (let (($x63 (= ethernet.dst_addr (_ bv1 48))))
 (let (($x64 (and true $x63)))
 (let (($x65 (and true $x64)))
 (let ((?x73 (ite $x65 (_ bv1 9) ?x68)))
 (let (($x95 (or (or (or (or false (= ?x73 (_ bv0 9))) (= ?x73 (_ bv1 9))) (= ?x73 (_ bv2 9))) (= ?x73 (_ bv3 9)))))
 (let (($x115 (or (or (or (or $x95 (= ?x73 (_ bv4 9))) (= ?x73 (_ bv5 9))) (= ?x73 (_ bv6 9))) (= ?x73 (_ bv7 9)))))
 (let (($x135 (or (or (or (or $x115 (= ?x73 (_ bv8 9))) (= ?x73 (_ bv9 9))) (= ?x73 (_ bv10 9))) (= ?x73 (_ bv11 9)))))
 (let (($x155 (or (or (or (or $x135 (= ?x73 (_ bv12 9))) (= ?x73 (_ bv13 9))) (= ?x73 (_ bv14 9))) (= ?x73 (_ bv15 9)))))
 (let (($x175 (or (or (or (or $x155 (= ?x73 (_ bv16 9))) (= ?x73 (_ bv17 9))) (= ?x73 (_ bv18 9))) (= ?x73 (_ bv19 9)))))
 (let (($x75 (= ?x73 (_ bv511 9))))
 (or $x75 $x175)))))))))))))))))))))))
(check-sat)
