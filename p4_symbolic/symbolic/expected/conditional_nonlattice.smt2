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
(egress) standard_metadata.checksum_error: #b0
(egress) standard_metadata.deq_qdepth: #b0000000000000000000
(egress) standard_metadata.deq_timedelta: #x00000000
(egress) standard_metadata.egress_global_timestamp: #x000000000000
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
                (ite a!4 #b111111111 (ite a!5 #b111111111 #b000000000)))))
(let ((a!7 (ite (and true (and true (= ethernet.dst_addr #x000000000001)))
                #b000000001
                (ite a!1 #b111111111 (ite a!3 #b111111111 a!6)))))
  (ite (not (= a!7 #b111111111)) a!7 standard_metadata.egress_port))))
(egress) standard_metadata.egress_rid: #x0000
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
                (ite a!4 #b111111111 (ite a!5 #b111111111 #b000000000)))))
  (ite (and true (and true (= ethernet.dst_addr #x000000000001)))
       #b000000001
       (ite a!1 #b111111111 (ite a!3 #b111111111 a!6)))))
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
 (let (($x166 (= standard_metadata.ingress_port (_ bv19 9))))
 (let (($x161 (= standard_metadata.ingress_port (_ bv18 9))))
 (let (($x156 (= standard_metadata.ingress_port (_ bv17 9))))
 (let (($x151 (= standard_metadata.ingress_port (_ bv16 9))))
 (let (($x146 (= standard_metadata.ingress_port (_ bv15 9))))
 (let (($x141 (= standard_metadata.ingress_port (_ bv14 9))))
 (let (($x136 (= standard_metadata.ingress_port (_ bv13 9))))
 (let (($x131 (= standard_metadata.ingress_port (_ bv12 9))))
 (let (($x126 (= standard_metadata.ingress_port (_ bv11 9))))
 (let (($x121 (= standard_metadata.ingress_port (_ bv10 9))))
 (let (($x116 (= standard_metadata.ingress_port (_ bv9 9))))
 (let (($x111 (= standard_metadata.ingress_port (_ bv8 9))))
 (let (($x106 (= standard_metadata.ingress_port (_ bv7 9))))
 (let (($x101 (= standard_metadata.ingress_port (_ bv6 9))))
 (let (($x96 (= standard_metadata.ingress_port (_ bv5 9))))
 (let (($x91 (= standard_metadata.ingress_port (_ bv4 9))))
 (let (($x86 (= standard_metadata.ingress_port (_ bv3 9))))
 (let (($x81 (= standard_metadata.ingress_port (_ bv2 9))))
 (let (($x76 (= standard_metadata.ingress_port (_ bv1 9))))
 (let (($x82 (or (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x76) $x81)))
 (let (($x117 (or (or (or (or (or (or (or $x82 $x86) $x91) $x96) $x101) $x106) $x111) $x116)))
 (let (($x152 (or (or (or (or (or (or (or $x117 $x121) $x126) $x131) $x136) $x141) $x146) $x151)))
 (or (or (or $x152 $x156) $x161) $x166))))))))))))))))))))))))
(assert
 (let (($x33 (bvugt standard_metadata.ingress_port (concat (_ bv0 5) (_ bv15 4)))))
 (let (($x27 (bvugt standard_metadata.ingress_port (concat (_ bv0 5) (_ bv10 4)))))
 (let (($x17 (and true $x27)))
 (let (($x35 (and $x17 $x33)))
 (let (($x36 (and $x17 (not $x33))))
 (let (($x46 (bvugt standard_metadata.ingress_port (concat (_ bv0 6) (_ bv5 3)))))
 (let (($x22 (and true (not $x27))))
 (let (($x48 (and $x22 $x46)))
 (let (($x49 (and $x22 (not $x46))))
 (let ((?x62 (ite (and true (not (and true (= ethernet.dst_addr (_ bv1 48))))) (_ bv511 9) (ite $x49 (_ bv511 9) (ite $x48 (_ bv511 9) (ite $x36 (_ bv511 9) (ite $x35 (_ bv511 9) (_ bv0 9))))))))
 (let (($x57 (= ethernet.dst_addr (_ bv1 48))))
 (let (($x58 (and true $x57)))
 (let (($x59 (and true $x58)))
 (let ((?x67 (ite $x59 (_ bv1 9) ?x62)))
 (let (($x89 (or (or (or (or false (= ?x67 (_ bv0 9))) (= ?x67 (_ bv1 9))) (= ?x67 (_ bv2 9))) (= ?x67 (_ bv3 9)))))
 (let (($x109 (or (or (or (or $x89 (= ?x67 (_ bv4 9))) (= ?x67 (_ bv5 9))) (= ?x67 (_ bv6 9))) (= ?x67 (_ bv7 9)))))
 (let (($x129 (or (or (or (or $x109 (= ?x67 (_ bv8 9))) (= ?x67 (_ bv9 9))) (= ?x67 (_ bv10 9))) (= ?x67 (_ bv11 9)))))
 (let (($x149 (or (or (or (or $x129 (= ?x67 (_ bv12 9))) (= ?x67 (_ bv13 9))) (= ?x67 (_ bv14 9))) (= ?x67 (_ bv15 9)))))
 (let (($x169 (or (or (or (or $x149 (= ?x67 (_ bv16 9))) (= ?x67 (_ bv17 9))) (= ?x67 (_ bv18 9))) (= ?x67 (_ bv19 9)))))
 (let (($x69 (= ?x67 (_ bv511 9))))
 (or $x69 $x169))))))))))))))))))))))
(check-sat)
