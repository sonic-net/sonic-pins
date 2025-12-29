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
 (let (($x47 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x47)))
(assert
 (let (($x46 (or false (= (ite (and true (= ethernet.dst_addr (_ bv1 48))) (_ bv1 9) (_ bv511 9)) (_ bv0 9)))))
(let (($x50 (or $x46 (= (ite (and true (= ethernet.dst_addr (_ bv1 48))) (_ bv1 9) (_ bv511 9)) (_ bv1 9)))))
(let (($x26 (= ethernet.dst_addr (_ bv1 48))))
(let (($x32 (and true $x26)))
(let ((?x39 (ite $x32 (_ bv1 9) (_ bv511 9))))
(let (($x40 (= ?x39 (_ bv511 9))))
(or $x40 $x50))))))))
(check-sat)
