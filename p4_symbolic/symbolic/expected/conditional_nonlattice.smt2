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
(egress) ethernet.dst_addr: (ite (= ethernet.dst_addr #x000000000001) #x000000000002 ethernet.dst_addr)
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
(egress) standard_metadata.egress_port: (let ((a!1 (not (and (= ((_ extract 8 4) standard_metadata.ingress_port)
                        #b00000)
                     (bvule ((_ extract 3 0) standard_metadata.ingress_port)
                            #xa))))
      (a!2 (not (and (= ((_ extract 8 3) standard_metadata.ingress_port)
                        #b000000)
                     (bvule ((_ extract 2 0) standard_metadata.ingress_port)
                            #b101)))))
(let ((a!3 (or a!1
               (and (= ((_ extract 8 4) standard_metadata.ingress_port) #b00000)
                    (bvule ((_ extract 3 0) standard_metadata.ingress_port) #xa)
                    a!2)
               (and (= ((_ extract 8 4) standard_metadata.ingress_port) #b00000)
                    (bvule ((_ extract 3 0) standard_metadata.ingress_port) #xa)
                    (= ((_ extract 8 3) standard_metadata.ingress_port)
                       #b000000)
                    (bvule ((_ extract 2 0) standard_metadata.ingress_port)
                           #b101)))))
(let ((a!4 (and (not (and (= ethernet.dst_addr #x000000000001) (not a!3)))
                (not (= ethernet.dst_addr #x000000000001))))
      (a!5 (ite (= ethernet.dst_addr #x000000000001)
                #b000000001
                (ite (and (= ethernet.dst_addr #x000000000001) (not a!3))
                     #b000000000
                     #b111111111))))
  (ite a!4 standard_metadata.egress_port a!5))))
(egress) standard_metadata.egress_rid: #x0000
(egress) standard_metadata.egress_spec: (let ((a!1 (not (and (= ((_ extract 8 4) standard_metadata.ingress_port)
                        #b00000)
                     (bvule ((_ extract 3 0) standard_metadata.ingress_port)
                            #xa))))
      (a!2 (not (and (= ((_ extract 8 3) standard_metadata.ingress_port)
                        #b000000)
                     (bvule ((_ extract 2 0) standard_metadata.ingress_port)
                            #b101)))))
(let ((a!3 (or a!1
               (and (= ((_ extract 8 4) standard_metadata.ingress_port) #b00000)
                    (bvule ((_ extract 3 0) standard_metadata.ingress_port) #xa)
                    a!2)
               (and (= ((_ extract 8 4) standard_metadata.ingress_port) #b00000)
                    (bvule ((_ extract 3 0) standard_metadata.ingress_port) #xa)
                    (= ((_ extract 8 3) standard_metadata.ingress_port)
                       #b000000)
                    (bvule ((_ extract 2 0) standard_metadata.ingress_port)
                           #b101)))))
  (ite (= ethernet.dst_addr #x000000000001)
       #b000000001
       (ite (and (= ethernet.dst_addr #x000000000001) (not a!3))
            #b000000000
            #b111111111))))
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
(declare-fun ethernet.dst_addr () (_ BitVec 48))
(assert
 (let (($x168 (= standard_metadata.ingress_port (_ bv19 9))))
 (let (($x163 (= standard_metadata.ingress_port (_ bv18 9))))
 (let (($x158 (= standard_metadata.ingress_port (_ bv17 9))))
 (let (($x153 (= standard_metadata.ingress_port (_ bv16 9))))
 (let (($x148 (= standard_metadata.ingress_port (_ bv15 9))))
 (let (($x143 (= standard_metadata.ingress_port (_ bv14 9))))
 (let (($x138 (= standard_metadata.ingress_port (_ bv13 9))))
 (let (($x133 (= standard_metadata.ingress_port (_ bv12 9))))
 (let (($x128 (= standard_metadata.ingress_port (_ bv11 9))))
 (let (($x123 (= standard_metadata.ingress_port (_ bv10 9))))
 (let (($x118 (= standard_metadata.ingress_port (_ bv9 9))))
 (let (($x113 (= standard_metadata.ingress_port (_ bv8 9))))
 (let (($x108 (= standard_metadata.ingress_port (_ bv7 9))))
 (let (($x103 (= standard_metadata.ingress_port (_ bv6 9))))
 (let (($x98 (= standard_metadata.ingress_port (_ bv5 9))))
 (let (($x93 (= standard_metadata.ingress_port (_ bv4 9))))
 (let (($x88 (= standard_metadata.ingress_port (_ bv3 9))))
 (let (($x83 (= standard_metadata.ingress_port (_ bv2 9))))
 (let (($x77 (= standard_metadata.ingress_port (_ bv1 9))))
 (let (($x84 (or (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x77) $x83)))
 (let (($x119 (or (or (or (or (or (or (or $x84 $x88) $x93) $x98) $x103) $x108) $x113) $x118)))
 (let (($x154 (or (or (or (or (or (or (or $x119 $x123) $x128) $x133) $x138) $x143) $x148) $x153)))
 (or (or (or $x154 $x158) $x163) $x168))))))))))))))))))))))))
(assert
 (let (($x61 (bvule ((_ extract 2 0) standard_metadata.ingress_port) (_ bv5 3))))
 (let (($x56 (= ((_ extract 8 3) standard_metadata.ingress_port) (_ bv0 6))))
 (let (($x35 (bvule ((_ extract 3 0) standard_metadata.ingress_port) (_ bv10 4))))
 (let (($x22 (= ((_ extract 8 4) standard_metadata.ingress_port) (_ bv0 5))))
 (let (($x65 (and $x22 $x35 $x56 $x61)))
 (let (($x64 (and $x22 $x35 (not (and $x56 $x61)))))
 (let (($x37 (not (and $x22 $x35))))
 (let (($x47 (= ethernet.dst_addr (_ bv1 48))))
 (let (($x67 (and $x47 (not (or $x37 $x64 $x65)))))
 (let ((?x71 (ite $x47 (_ bv1 9) (ite $x67 (_ bv0 9) (_ bv511 9)))))
 (let (($x91 (or (or (or (or false (= ?x71 (_ bv0 9))) (= ?x71 (_ bv1 9))) (= ?x71 (_ bv2 9))) (= ?x71 (_ bv3 9)))))
 (let (($x111 (or (or (or (or $x91 (= ?x71 (_ bv4 9))) (= ?x71 (_ bv5 9))) (= ?x71 (_ bv6 9))) (= ?x71 (_ bv7 9)))))
 (let (($x131 (or (or (or (or $x111 (= ?x71 (_ bv8 9))) (= ?x71 (_ bv9 9))) (= ?x71 (_ bv10 9))) (= ?x71 (_ bv11 9)))))
 (let (($x151 (or (or (or (or $x131 (= ?x71 (_ bv12 9))) (= ?x71 (_ bv13 9))) (= ?x71 (_ bv14 9))) (= ?x71 (_ bv15 9)))))
 (let (($x171 (or (or (or (or $x151 (= ?x71 (_ bv16 9))) (= ?x71 (_ bv17 9))) (= ?x71 (_ bv18 9))) (= ?x71 (_ bv19 9)))))
 (let (($x6 (= ?x71 (_ bv511 9))))
 (or $x6 $x171))))))))))))))))))
(check-sat)
