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
(egress) ethernet.dst_addr: (let ((a!1 (ite (and true (and true (= ethernet.ether_type #x0010))) 0 (- 1)))
      (a!2 (ite (and true (= ethernet.src_addr #x000000000100))
                #x000000000003
                (ite (and true (= ethernet.ether_type #x0010))
                     #x000000000002
                     ethernet.dst_addr))))
  (ite (and true (distinct a!1 (- 1)))
       a!2
       (ite (and true (= ethernet.ether_type #x0010))
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
      (a!2 (ite (and true (= ethernet.src_addr #x000000000100))
                #b000000011
                (ite (and true (= ethernet.ether_type #x0010))
                     #b000000010
                     #b111111111))))
(let ((a!3 (ite (and true (distinct a!1 (- 1)))
                a!2
                (ite (and true (= ethernet.ether_type #x0010))
                     #b000000010
                     #b111111111))))
  (ite (not (= a!3 #b111111111)) a!3 standard_metadata.egress_port)))
(egress) standard_metadata.egress_rid: #x0000
(egress) standard_metadata.egress_spec: (let ((a!1 (ite (and true (and true (= ethernet.ether_type #x0010))) 0 (- 1)))
      (a!2 (ite (and true (= ethernet.src_addr #x000000000100))
                #b000000011
                (ite (and true (= ethernet.ether_type #x0010))
                     #b000000010
                     #b111111111))))
  (ite (and true (distinct a!1 (- 1)))
       a!2
       (ite (and true (= ethernet.ether_type #x0010)) #b000000010 #b111111111)))
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
 (let (($x86 (= standard_metadata.ingress_port (_ bv7 9))))
 (let (($x81 (= standard_metadata.ingress_port (_ bv6 9))))
 (let (($x76 (= standard_metadata.ingress_port (_ bv5 9))))
 (let (($x71 (= standard_metadata.ingress_port (_ bv4 9))))
 (let (($x66 (= standard_metadata.ingress_port (_ bv3 9))))
 (let (($x62 (= standard_metadata.ingress_port (_ bv2 9))))
 (let (($x58 (= standard_metadata.ingress_port (_ bv1 9))))
 (let (($x63 (or (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x58) $x62)))
 (or (or (or (or (or $x63 $x66) $x71) $x76) $x81) $x86))))))))))
(assert
 (let (($x6 (= ethernet.ether_type (_ bv16 16))))
(let (($x5 (and true $x6)))
(let ((?x34 (ite $x5 (_ bv2 9) (_ bv511 9))))
(let ((?x22 (ite (and true $x5) 0 (- 1))))
(let (($x35 (and (distinct ?x22 (- 1)) true)))
(let (($x36 (and true $x35)))
(let ((?x47 (ite $x36 (ite (and true (= ethernet.src_addr (_ bv256 48))) (_ bv3 9) ?x34) ?x34)))
(let (($x69 (or (or (or (or false (= ?x47 (_ bv0 9))) (= ?x47 (_ bv1 9))) (= ?x47 (_ bv2 9))) (= ?x47 (_ bv3 9)))))
(let (($x89 (or (or (or (or $x69 (= ?x47 (_ bv4 9))) (= ?x47 (_ bv5 9))) (= ?x47 (_ bv6 9))) (= ?x47 (_ bv7 9)))))
(let (($x50 (= ?x47 (_ bv511 9))))
(or $x50 $x89))))))))))))
(check-sat)
