(ingress) $got_cloned$: false
(ingress) $got_recirculated$: false
(ingress) ethernet.$extracted$: false
(ingress) ethernet.$valid$: true
(ingress) ethernet.dstAddr: ethernet.dstAddr
(ingress) ethernet.etherType: ethernet.etherType
(ingress) ethernet.srcAddr: ethernet.srcAddr
(ingress) ipv4.$extracted$: false
(ingress) ipv4.$valid$: (ite (= (concat #x0 #x800) ethernet.etherType) true false)
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
(parsed) ethernet.etherType: ethernet.etherType
(parsed) ethernet.srcAddr: ethernet.srcAddr
(parsed) ipv4.$extracted$: (ite (= (concat #x0 #x800) ethernet.etherType) true false)
(parsed) ipv4.$valid$: (ite (= (concat #x0 #x800) ethernet.etherType) true false)
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
(parsed) standard_metadata.parser_error: (let ((a!1 (and true (not (= (concat #x0 #x800) ethernet.etherType)) (not true)))
      (a!2 (ite (= (concat #x0 #x800) ethernet.etherType)
                (ite (and true (not true)) #x00000002 #x00000000)
                #x00000000)))
  (ite a!1 #x00000002 a!2))
(parsed) standard_metadata.priority: #b000

(egress) $got_cloned$: false
(egress) $got_recirculated$: false
(egress) ethernet.$extracted$: true
(egress) ethernet.$valid$: true
(egress) ethernet.dstAddr: (let ((a!1 (ite (and true
                     (= ((_ extract 31 24) ipv4.dstAddr)
                        ((_ extract 31 24) #x0a000000)))
                #x00000000000a
                ethernet.dstAddr)))
(let ((a!2 (ite (and true
                     (= ((_ extract 31 16) ipv4.dstAddr)
                        ((_ extract 31 16) #x14140000)))
                #x160000000016
                a!1)))
(let ((a!3 (ite (and true
                     (= ((_ extract 31 16) ipv4.dstAddr)
                        ((_ extract 31 16) #x0a0a0000)))
                #x000000000000
                a!2)))
  (ite (ite (= (concat #x0 #x800) ethernet.etherType) true false)
       (ite (and true (= ipv4.dstAddr #x0a0a0000)) #x000000000000 a!3)
       ethernet.dstAddr))))
(egress) ethernet.etherType: ethernet.etherType
(egress) ethernet.srcAddr: (let ((a!1 (ite (and true
                     (= ((_ extract 31 24) ipv4.dstAddr)
                        ((_ extract 31 24) #x0a000000)))
                ethernet.dstAddr
                ethernet.srcAddr)))
(let ((a!2 (ite (and true
                     (= ((_ extract 31 16) ipv4.dstAddr)
                        ((_ extract 31 16) #x14140000)))
                ethernet.dstAddr
                a!1)))
(let ((a!3 (ite (and true
                     (= ((_ extract 31 16) ipv4.dstAddr)
                        ((_ extract 31 16) #x0a0a0000)))
                ethernet.dstAddr
                a!2)))
  (ite (ite (= (concat #x0 #x800) ethernet.etherType) true false)
       (ite (and true (= ipv4.dstAddr #x0a0a0000)) ethernet.dstAddr a!3)
       ethernet.srcAddr))))
(egress) ipv4.$extracted$: (ite (= (concat #x0 #x800) ethernet.etherType) true false)
(egress) ipv4.$valid$: (ite (= (concat #x0 #x800) ethernet.etherType) true false)
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
(egress) ipv4.ttl: (let ((a!1 (ite (and true
                     (= ((_ extract 31 24) ipv4.dstAddr)
                        ((_ extract 31 24) #x0a000000)))
                (bvand (bvadd ipv4.ttl #xff) #xff)
                ipv4.ttl)))
(let ((a!2 (ite (and true
                     (= ((_ extract 31 16) ipv4.dstAddr)
                        ((_ extract 31 16) #x14140000)))
                (bvand (bvadd ipv4.ttl #xff) #xff)
                a!1)))
(let ((a!3 (ite (and true
                     (= ((_ extract 31 16) ipv4.dstAddr)
                        ((_ extract 31 16) #x0a0a0000)))
                (bvand (bvadd ipv4.ttl #xff) #xff)
                a!2)))
  (ite (ite (= (concat #x0 #x800) ethernet.etherType) true false)
       (ite (and true (= ipv4.dstAddr #x0a0a0000))
            (bvand (bvadd ipv4.ttl #xff) #xff)
            a!3)
       ipv4.ttl))))
(egress) ipv4.version: ipv4.version
(egress) scalars.$extracted$: false
(egress) scalars.$valid$: false
(egress) standard_metadata.$extracted$: false
(egress) standard_metadata.$valid$: false
(egress) standard_metadata._padding: standard_metadata._padding
(egress) standard_metadata.checksum_error: #b0
(egress) standard_metadata.deq_qdepth: #b0000000000000000000
(egress) standard_metadata.deq_timedelta: #x00000000
(egress) standard_metadata.egress_global_timestamp: #x000000000000
(egress) standard_metadata.egress_port: (let ((a!1 (ite (and true
                     (= ((_ extract 31 24) ipv4.dstAddr)
                        ((_ extract 31 24) #x0a000000)))
                #b000000001
                #b111111111)))
(let ((a!2 (ite (and true
                     (= ((_ extract 31 16) ipv4.dstAddr)
                        ((_ extract 31 16) #x14140000)))
                #b000000001
                a!1)))
(let ((a!3 (ite (and true
                     (= ((_ extract 31 16) ipv4.dstAddr)
                        ((_ extract 31 16) #x0a0a0000)))
                #b000000000
                a!2)))
(let ((a!4 (ite (ite (= (concat #x0 #x800) ethernet.etherType) true false)
                (ite (and true (= ipv4.dstAddr #x0a0a0000)) #b000000001 a!3)
                #b000000000)))
  (ite (not (= a!4 #b111111111)) a!4 standard_metadata.egress_port)))))
(egress) standard_metadata.egress_rid: #x0000
(egress) standard_metadata.egress_spec: (let ((a!1 (ite (and true
                     (= ((_ extract 31 24) ipv4.dstAddr)
                        ((_ extract 31 24) #x0a000000)))
                #b000000001
                #b111111111)))
(let ((a!2 (ite (and true
                     (= ((_ extract 31 16) ipv4.dstAddr)
                        ((_ extract 31 16) #x14140000)))
                #b000000001
                a!1)))
(let ((a!3 (ite (and true
                     (= ((_ extract 31 16) ipv4.dstAddr)
                        ((_ extract 31 16) #x0a0a0000)))
                #b000000000
                a!2)))
  (ite (ite (= (concat #x0 #x800) ethernet.etherType) true false)
       (ite (and true (= ipv4.dstAddr #x0a0a0000)) #b000000001 a!3)
       #b000000000))))
(egress) standard_metadata.enq_qdepth: #b0000000000000000000
(egress) standard_metadata.enq_timestamp: #x00000000
(egress) standard_metadata.ingress_global_timestamp: #x000000000000
(egress) standard_metadata.ingress_port: standard_metadata.ingress_port
(egress) standard_metadata.instance_type: #x00000000
(egress) standard_metadata.mcast_grp: #x0000
(egress) standard_metadata.packet_length: standard_metadata.packet_length
(egress) standard_metadata.parser_error: (let ((a!1 (and true (not (= (concat #x0 #x800) ethernet.etherType)) (not true)))
      (a!2 (ite (= (concat #x0 #x800) ethernet.etherType)
                (ite (and true (not true)) #x00000002 #x00000000)
                #x00000000)))
  (ite a!1 #x00000002 a!2))
(egress) standard_metadata.priority: #b000

(solver constraints)
; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(declare-fun ipv4.dstAddr () (_ BitVec 32))
(declare-fun ethernet.etherType () (_ BitVec 16))
(assert
 (let (($x110 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x110)))
(assert
 (let (($x60 (and true (= ((_ extract 31 24) ipv4.dstAddr) ((_ extract 31 24) (_ bv167772160 32))))))
(let (($x55 (and true (= ((_ extract 31 16) ipv4.dstAddr) ((_ extract 31 16) (_ bv336855040 32))))))
(let (($x51 (and true (= ((_ extract 31 16) ipv4.dstAddr) ((_ extract 31 16) (_ bv168427520 32))))))
(let (($x40 (= ipv4.dstAddr (_ bv168427520 32))))
(let (($x46 (and true $x40)))
(let (($x24 (= (concat (_ bv0 4) (_ bv2048 12)) ethernet.etherType)))
(let (($x41 (ite $x24 true false)))
(let ((?x100 (ite $x41 (ite $x46 (_ bv1 9) (ite $x51 (_ bv0 9) (ite $x55 (_ bv1 9) (ite $x60 (_ bv1 9) (_ bv511 9))))) (_ bv0 9))))
(let (($x113 (or (or false (= ?x100 (_ bv0 9))) (= ?x100 (_ bv1 9)))))
(let (($x103 (= ?x100 (_ bv511 9))))
(or $x103 $x113))))))))))))
(check-sat)
