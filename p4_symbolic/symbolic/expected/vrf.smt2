(ingress) $got_cloned$: false
(ingress) $got_recirculated$: false
(ingress) ethernet.$extracted$: false
(ingress) ethernet.$valid$: true
(ingress) ethernet.dstAddr: ethernet.dstAddr
(ingress) ethernet.eth_type: ethernet.eth_type
(ingress) ethernet.srcAddr: ethernet.srcAddr
(ingress) ipv4.$extracted$: false
(ingress) ipv4.$valid$: (ite (= (concat #x0 #x800) ethernet.eth_type) true false)
(ingress) ipv4.diffserv: ipv4.diffserv
(ingress) ipv4.dstAddr: ipv4.dstAddr
(ingress) ipv4.flags: ipv4.flags
(ingress) ipv4.fragOffset: ipv4.fragOffset
(ingress) ipv4.hdrChecksum: ipv4.hdrChecksum
(ingress) ipv4.identification: ipv4.identification
(ingress) ipv4.ihl: ipv4.ihl
(ingress) ipv4.protocol: ipv4.protocol
(ingress) ipv4.srcAddr: ipv4.srcAddr
(ingress) ipv4.totalLen: ipv4.totalLen
(ingress) ipv4.ttl: ipv4.ttl
(ingress) ipv4.version: ipv4.version
(ingress) scalars.$extracted$: false
(ingress) scalars.$valid$: false
(ingress) scalars._padding_0: scalars._padding_0
(ingress) scalars.local_metadata_t.vrf: scalars.local_metadata_t.vrf
(ingress) scalars.local_metadata_t.vrf_is_valid: scalars.local_metadata_t.vrf_is_valid
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
(parsed) ethernet.dstAddr: ethernet.dstAddr
(parsed) ethernet.eth_type: ethernet.eth_type
(parsed) ethernet.srcAddr: ethernet.srcAddr
(parsed) ipv4.$extracted$: (ite (= (concat #x0 #x800) ethernet.eth_type) true false)
(parsed) ipv4.$valid$: (ite (= (concat #x0 #x800) ethernet.eth_type) true false)
(parsed) ipv4.diffserv: ipv4.diffserv
(parsed) ipv4.dstAddr: ipv4.dstAddr
(parsed) ipv4.flags: ipv4.flags
(parsed) ipv4.fragOffset: ipv4.fragOffset
(parsed) ipv4.hdrChecksum: ipv4.hdrChecksum
(parsed) ipv4.identification: ipv4.identification
(parsed) ipv4.ihl: ipv4.ihl
(parsed) ipv4.protocol: ipv4.protocol
(parsed) ipv4.srcAddr: ipv4.srcAddr
(parsed) ipv4.totalLen: ipv4.totalLen
(parsed) ipv4.ttl: ipv4.ttl
(parsed) ipv4.version: ipv4.version
(parsed) scalars.$extracted$: false
(parsed) scalars.$valid$: false
(parsed) scalars._padding_0: scalars._padding_0
(parsed) scalars.local_metadata_t.vrf: scalars.local_metadata_t.vrf
(parsed) scalars.local_metadata_t.vrf_is_valid: scalars.local_metadata_t.vrf_is_valid
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
(parsed) standard_metadata.parser_error: (let ((a!1 (and true (not (= (concat #x0 #x800) ethernet.eth_type)) (not true)))
      (a!2 (ite (= (concat #x0 #x800) ethernet.eth_type)
                (ite (and true (not true)) #x00000002 #x00000000)
                #x00000000)))
  (ite a!1 #x00000002 a!2))
(parsed) standard_metadata.priority: #b000

(egress) $got_cloned$: false
(egress) $got_recirculated$: false
(egress) ethernet.$extracted$: true
(egress) ethernet.$valid$: true
(egress) ethernet.dstAddr: (let ((a!1 (ite (and true (= (bvand ipv4.srcAddr #x21210909) #x21210000))
                (ite true #b1 #b0)
                (ite false #b1 #b0)))
      (a!3 (ite (and true (= (bvand ipv4.srcAddr #x09210909) #x00210100))
                (concat #b000000000 #b1)
                (concat #b000000000 #b0))))
(let ((a!2 (ite (and true (= (bvand ipv4.srcAddr #x09210909) #x00210100))
                (ite true #b1 #b0)
                a!1))
      (a!4 (ite (and true
                     (= ((_ extract 31 24) ipv4.dstAddr)
                        ((_ extract 31 24) #x0a000000))
                     (= a!3 (concat #b000000000 #b0)))
                #x00000000000a
                ethernet.dstAddr)))
(let ((a!5 (ite (and true
                     (= ((_ extract 31 16) ipv4.dstAddr)
                        ((_ extract 31 16) #x14140000))
                     (= a!3 (concat #b000000000 #b1)))
                #x160000000016
                a!4)))
(let ((a!6 (ite (and true
                     (= ((_ extract 31 16) ipv4.dstAddr)
                        ((_ extract 31 16) #x0a0a0000))
                     (= a!3 (concat #b000000000 #b0)))
                #x000000000000
                a!5)))
(let ((a!7 (ite (and true
                     (= ipv4.dstAddr #x0a0a0000)
                     (= a!3 (concat #b000000000 #b0)))
                #x000000000000
                a!6)))
  (ite (ite (= (concat #x0 #x800) ethernet.eth_type) true false)
       (ite (bvuge a!2 #b1) a!7 ethernet.dstAddr)
       ethernet.dstAddr))))))
(egress) ethernet.eth_type: ethernet.eth_type
(egress) ethernet.srcAddr: (let ((a!1 (ite (and true (= (bvand ipv4.srcAddr #x21210909) #x21210000))
                (ite true #b1 #b0)
                (ite false #b1 #b0)))
      (a!3 (ite (and true (= (bvand ipv4.srcAddr #x09210909) #x00210100))
                (concat #b000000000 #b1)
                (concat #b000000000 #b0))))
(let ((a!2 (ite (and true (= (bvand ipv4.srcAddr #x09210909) #x00210100))
                (ite true #b1 #b0)
                a!1))
      (a!4 (ite (and true
                     (= ((_ extract 31 24) ipv4.dstAddr)
                        ((_ extract 31 24) #x0a000000))
                     (= a!3 (concat #b000000000 #b0)))
                ethernet.dstAddr
                ethernet.srcAddr)))
(let ((a!5 (ite (and true
                     (= ((_ extract 31 16) ipv4.dstAddr)
                        ((_ extract 31 16) #x14140000))
                     (= a!3 (concat #b000000000 #b1)))
                ethernet.dstAddr
                a!4)))
(let ((a!6 (ite (and true
                     (= ((_ extract 31 16) ipv4.dstAddr)
                        ((_ extract 31 16) #x0a0a0000))
                     (= a!3 (concat #b000000000 #b0)))
                ethernet.dstAddr
                a!5)))
(let ((a!7 (ite (and true
                     (= ipv4.dstAddr #x0a0a0000)
                     (= a!3 (concat #b000000000 #b0)))
                ethernet.dstAddr
                a!6)))
  (ite (ite (= (concat #x0 #x800) ethernet.eth_type) true false)
       (ite (bvuge a!2 #b1) a!7 ethernet.srcAddr)
       ethernet.srcAddr))))))
(egress) ipv4.$extracted$: (ite (= (concat #x0 #x800) ethernet.eth_type) true false)
(egress) ipv4.$valid$: (ite (= (concat #x0 #x800) ethernet.eth_type) true false)
(egress) ipv4.diffserv: ipv4.diffserv
(egress) ipv4.dstAddr: ipv4.dstAddr
(egress) ipv4.flags: ipv4.flags
(egress) ipv4.fragOffset: ipv4.fragOffset
(egress) ipv4.hdrChecksum: ipv4.hdrChecksum
(egress) ipv4.identification: ipv4.identification
(egress) ipv4.ihl: ipv4.ihl
(egress) ipv4.protocol: ipv4.protocol
(egress) ipv4.srcAddr: ipv4.srcAddr
(egress) ipv4.totalLen: ipv4.totalLen
(egress) ipv4.ttl: (let ((a!1 (ite (and true (= (bvand ipv4.srcAddr #x21210909) #x21210000))
                (ite true #b1 #b0)
                (ite false #b1 #b0)))
      (a!3 (ite (and true (= (bvand ipv4.srcAddr #x09210909) #x00210100))
                (concat #b000000000 #b1)
                (concat #b000000000 #b0))))
(let ((a!2 (ite (and true (= (bvand ipv4.srcAddr #x09210909) #x00210100))
                (ite true #b1 #b0)
                a!1))
      (a!4 (ite (and true
                     (= ((_ extract 31 24) ipv4.dstAddr)
                        ((_ extract 31 24) #x0a000000))
                     (= a!3 (concat #b000000000 #b0)))
                (bvand (bvadd ipv4.ttl #xff) #xff)
                ipv4.ttl)))
(let ((a!5 (ite (and true
                     (= ((_ extract 31 16) ipv4.dstAddr)
                        ((_ extract 31 16) #x14140000))
                     (= a!3 (concat #b000000000 #b1)))
                (bvand (bvadd ipv4.ttl #xff) #xff)
                a!4)))
(let ((a!6 (ite (and true
                     (= ((_ extract 31 16) ipv4.dstAddr)
                        ((_ extract 31 16) #x0a0a0000))
                     (= a!3 (concat #b000000000 #b0)))
                (bvand (bvadd ipv4.ttl #xff) #xff)
                a!5)))
(let ((a!7 (ite (and true
                     (= ipv4.dstAddr #x0a0a0000)
                     (= a!3 (concat #b000000000 #b0)))
                (bvand (bvadd ipv4.ttl #xff) #xff)
                a!6)))
  (ite (ite (= (concat #x0 #x800) ethernet.eth_type) true false)
       (ite (bvuge a!2 #b1) a!7 ipv4.ttl)
       ipv4.ttl))))))
(egress) ipv4.version: ipv4.version
(egress) scalars.$extracted$: false
(egress) scalars.$valid$: false
(egress) scalars._padding_0: scalars._padding_0
(egress) scalars.local_metadata_t.vrf: (let ((a!1 (ite (and true (= (bvand ipv4.srcAddr #x09210909) #x00210100))
                (concat #b000000000 #b1)
                (concat #b000000000 #b0))))
  (ite (ite (= (concat #x0 #x800) ethernet.eth_type) true false)
       a!1
       (concat #b000000000 #b0)))
(egress) scalars.local_metadata_t.vrf_is_valid: (let ((a!1 (ite (and true (= (bvand ipv4.srcAddr #x21210909) #x21210000))
                (ite true #b1 #b0)
                (ite false #b1 #b0))))
(let ((a!2 (ite (and true (= (bvand ipv4.srcAddr #x09210909) #x00210100))
                (ite true #b1 #b0)
                a!1)))
  (ite (ite (= (concat #x0 #x800) ethernet.eth_type) true false)
       a!2
       (ite false #b1 #b0))))
(egress) standard_metadata.$extracted$: false
(egress) standard_metadata.$valid$: false
(egress) standard_metadata._padding: standard_metadata._padding
(egress) standard_metadata.checksum_error: #b0
(egress) standard_metadata.deq_qdepth: #b0000000000000000000
(egress) standard_metadata.deq_timedelta: #x00000000
(egress) standard_metadata.egress_global_timestamp: #x000000000000
(egress) standard_metadata.egress_port: (let ((a!1 (ite (and true (= (bvand ipv4.srcAddr #x21210909) #x21210000))
                (ite true #b1 #b0)
                (ite false #b1 #b0)))
      (a!3 (ite (and true (= (bvand ipv4.srcAddr #x09210909) #x00210100))
                (concat #b000000000 #b1)
                (concat #b000000000 #b0))))
(let ((a!2 (ite (and true (= (bvand ipv4.srcAddr #x09210909) #x00210100))
                (ite true #b1 #b0)
                a!1))
      (a!4 (ite (and true
                     (= ((_ extract 31 24) ipv4.dstAddr)
                        ((_ extract 31 24) #x0a000000))
                     (= a!3 (concat #b000000000 #b0)))
                #b000000001
                #b111111111)))
(let ((a!5 (ite (and true
                     (= ((_ extract 31 16) ipv4.dstAddr)
                        ((_ extract 31 16) #x14140000))
                     (= a!3 (concat #b000000000 #b1)))
                #b000000001
                a!4)))
(let ((a!6 (ite (and true
                     (= ((_ extract 31 16) ipv4.dstAddr)
                        ((_ extract 31 16) #x0a0a0000))
                     (= a!3 (concat #b000000000 #b0)))
                #b000000000
                a!5)))
(let ((a!7 (ite (and true
                     (= ipv4.dstAddr #x0a0a0000)
                     (= a!3 (concat #b000000000 #b0)))
                #b000000001
                a!6)))
(let ((a!8 (ite (ite (= (concat #x0 #x800) ethernet.eth_type) true false)
                (ite (bvuge a!2 #b1) a!7 #b000000000)
                #b000000000)))
  (ite (not (= a!8 #b111111111)) a!8 standard_metadata.egress_port)))))))
(egress) standard_metadata.egress_rid: #x0000
(egress) standard_metadata.egress_spec: (let ((a!1 (ite (and true (= (bvand ipv4.srcAddr #x21210909) #x21210000))
                (ite true #b1 #b0)
                (ite false #b1 #b0)))
      (a!3 (ite (and true (= (bvand ipv4.srcAddr #x09210909) #x00210100))
                (concat #b000000000 #b1)
                (concat #b000000000 #b0))))
(let ((a!2 (ite (and true (= (bvand ipv4.srcAddr #x09210909) #x00210100))
                (ite true #b1 #b0)
                a!1))
      (a!4 (ite (and true
                     (= ((_ extract 31 24) ipv4.dstAddr)
                        ((_ extract 31 24) #x0a000000))
                     (= a!3 (concat #b000000000 #b0)))
                #b000000001
                #b111111111)))
(let ((a!5 (ite (and true
                     (= ((_ extract 31 16) ipv4.dstAddr)
                        ((_ extract 31 16) #x14140000))
                     (= a!3 (concat #b000000000 #b1)))
                #b000000001
                a!4)))
(let ((a!6 (ite (and true
                     (= ((_ extract 31 16) ipv4.dstAddr)
                        ((_ extract 31 16) #x0a0a0000))
                     (= a!3 (concat #b000000000 #b0)))
                #b000000000
                a!5)))
(let ((a!7 (ite (and true
                     (= ipv4.dstAddr #x0a0a0000)
                     (= a!3 (concat #b000000000 #b0)))
                #b000000001
                a!6)))
  (ite (ite (= (concat #x0 #x800) ethernet.eth_type) true false)
       (ite (bvuge a!2 #b1) a!7 #b000000000)
       #b000000000))))))
(egress) standard_metadata.enq_qdepth: #b0000000000000000000
(egress) standard_metadata.enq_timestamp: #x00000000
(egress) standard_metadata.ingress_global_timestamp: #x000000000000
(egress) standard_metadata.ingress_port: standard_metadata.ingress_port
(egress) standard_metadata.instance_type: #x00000000
(egress) standard_metadata.mcast_grp: #x0000
(egress) standard_metadata.packet_length: standard_metadata.packet_length
(egress) standard_metadata.parser_error: (let ((a!1 (and true (not (= (concat #x0 #x800) ethernet.eth_type)) (not true)))
      (a!2 (ite (= (concat #x0 #x800) ethernet.eth_type)
                (ite (and true (not true)) #x00000002 #x00000000)
                #x00000000)))
  (ite a!1 #x00000002 a!2))
(egress) standard_metadata.priority: #b000

(solver constraints)
; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(declare-fun ipv4.srcAddr () (_ BitVec 32))
(declare-fun ipv4.dstAddr () (_ BitVec 32))
(declare-fun ethernet.eth_type () (_ BitVec 16))
(assert
 (let (($x152 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x152)))
(assert
 (let ((?x51 (concat (_ bv0 9) (_ bv0 1))))
(let ((?x69 (concat (_ bv0 9) (_ bv1 1))))
(let (($x56 (and true (= (bvand ipv4.srcAddr (_ bv153159945 32)) (_ bv2162944 32)))))
(let ((?x70 (ite $x56 ?x69 ?x51)))
(let (($x77 (= ?x70 ?x51)))
(let (($x95 (and (and true (= ((_ extract 31 24) ipv4.dstAddr) ((_ extract 31 24) (_ bv167772160 32)))) $x77)))
(let (($x89 (and (and true (= ((_ extract 31 16) ipv4.dstAddr) ((_ extract 31 16) (_ bv336855040 32)))) (= ?x70 ?x69))))
(let (($x83 (and (and true (= ((_ extract 31 16) ipv4.dstAddr) ((_ extract 31 16) (_ bv168427520 32)))) $x77)))
(let (($x78 (and (and true (= ipv4.dstAddr (_ bv168427520 32))) $x77)))
(let ((?x49 (ite false (_ bv1 1) (_ bv0 1))))
(let ((?x65 (ite true (_ bv1 1) (_ bv0 1))))
(let (($x61 (and true (= (bvand ipv4.srcAddr (_ bv555813129 32)) (_ bv555810816 32)))))
(let ((?x72 (ite $x56 ?x65 (ite $x61 ?x65 ?x49))))
(let (($x73 (bvuge ?x72 (_ bv1 1))))
(let ((?x132 (ite $x73 (ite $x78 (_ bv1 9) (ite $x83 (_ bv0 9) (ite $x89 (_ bv1 9) (ite $x95 (_ bv1 9) (_ bv511 9))))) (_ bv0 9))))
(let (($x24 (= (concat (_ bv0 4) (_ bv2048 12)) ethernet.eth_type)))
(let (($x44 (ite $x24 true false)))
(let ((?x140 (ite $x44 ?x132 (_ bv0 9))))
(let (($x155 (or (or false (= ?x140 (_ bv0 9))) (= ?x140 (_ bv1 9)))))
(let (($x145 (= ?x140 (_ bv511 9))))
(or $x145 $x155))))))))))))))))))))))
(check-sat)
