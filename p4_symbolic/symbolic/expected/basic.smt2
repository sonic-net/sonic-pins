(ingress) $got_cloned$: false
(ingress) $got_recirculated$: false
(ingress) ethernet.$extracted$: false
(ingress) ethernet.$valid$: (ite true true false)
(ingress) ethernet.dstAddr: ethernet.dstAddr
(ingress) ethernet.etherType: ethernet.etherType
(ingress) ethernet.srcAddr: ethernet.srcAddr
(ingress) ipv4.$extracted$: false
(ingress) ipv4.$valid$: (ite (and true (= (concat #x0 #x800) ethernet.etherType)) true false)
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
(parsed) ethernet.$extracted$: (ite true true false)
(parsed) ethernet.$valid$: (ite true true false)
(parsed) ethernet.dstAddr: ethernet.dstAddr
(parsed) ethernet.etherType: ethernet.etherType
(parsed) ethernet.srcAddr: ethernet.srcAddr
(parsed) ipv4.$extracted$: (ite (and true (= (concat #x0 #x800) ethernet.etherType)) true false)
(parsed) ipv4.$valid$: (ite (and true (= (concat #x0 #x800) ethernet.etherType)) true false)
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
      (a!2 (ite (and true (= (concat #x0 #x800) ethernet.etherType) (not true))
                #x00000002
                #x00000000)))
  (ite a!1 #x00000002 a!2))
(parsed) standard_metadata.priority: #b000

(egress) $got_cloned$: false
(egress) $got_recirculated$: false
(egress) ethernet.$extracted$: (ite true true false)
(egress) ethernet.$valid$: (ite true true false)
(egress) ethernet.dstAddr: (let ((a!1 (ite (and true (= (concat #x0 #x800) ethernet.etherType)) true false))
      (a!3 (not (and true
                     (= ((_ extract 31 16) ipv4.dstAddr)
                        ((_ extract 31 16) #x0a0a0000)))))
      (a!6 (not (and true
                     (= ((_ extract 31 16) ipv4.dstAddr)
                        ((_ extract 31 16) #x14140000))))))
(let ((a!2 (and (and true a!1)
                (not (and true (= ipv4.dstAddr #x0a0a0000)))
                (and true
                     (= ((_ extract 31 16) ipv4.dstAddr)
                        ((_ extract 31 16) #x0a0a0000)))))
      (a!4 (and (not (and true (= ipv4.dstAddr #x0a0a0000))) a!3)))
(let ((a!5 (and (and true a!1)
                a!4
                (and true
                     (= ((_ extract 31 16) ipv4.dstAddr)
                        ((_ extract 31 16) #x14140000)))))
      (a!7 (ite (and (and true a!1)
                     a!4
                     a!6
                     true
                     (= ((_ extract 31 24) ipv4.dstAddr)
                        ((_ extract 31 24) #x0a000000)))
                #x00000000000a
                ethernet.dstAddr)))
  (ite (and (and true a!1) (and true (= ipv4.dstAddr #x0a0a0000)))
       #x000000000000
       (ite a!2 #x000000000000 (ite a!5 #x160000000016 a!7))))))
(egress) ethernet.etherType: ethernet.etherType
(egress) ethernet.srcAddr: (let ((a!1 (ite (and true (= (concat #x0 #x800) ethernet.etherType)) true false))
      (a!3 (not (and true
                     (= ((_ extract 31 16) ipv4.dstAddr)
                        ((_ extract 31 16) #x0a0a0000)))))
      (a!6 (not (and true
                     (= ((_ extract 31 16) ipv4.dstAddr)
                        ((_ extract 31 16) #x14140000))))))
(let ((a!2 (and (and true a!1)
                (not (and true (= ipv4.dstAddr #x0a0a0000)))
                (and true
                     (= ((_ extract 31 16) ipv4.dstAddr)
                        ((_ extract 31 16) #x0a0a0000)))))
      (a!4 (and (not (and true (= ipv4.dstAddr #x0a0a0000))) a!3)))
(let ((a!5 (and (and true a!1)
                a!4
                (and true
                     (= ((_ extract 31 16) ipv4.dstAddr)
                        ((_ extract 31 16) #x14140000)))))
      (a!7 (and (and true a!1)
                a!4
                a!6
                true
                (= ((_ extract 31 24) ipv4.dstAddr)
                   ((_ extract 31 24) #x0a000000)))))
  (ite (and (and true a!1) (and true (= ipv4.dstAddr #x0a0a0000)))
       (ite a!2
            #x000000000000
            (ite a!5 #x160000000016 (ite a!7 #x00000000000a ethernet.dstAddr)))
       (ite a!2
            (ite a!5 #x160000000016 (ite a!7 #x00000000000a ethernet.dstAddr))
            (ite a!5
                 (ite a!7 #x00000000000a ethernet.dstAddr)
                 (ite a!7 ethernet.dstAddr ethernet.srcAddr)))))))
(egress) ipv4.$extracted$: (ite (and true (= (concat #x0 #x800) ethernet.etherType)) true false)
(egress) ipv4.$valid$: (ite (and true (= (concat #x0 #x800) ethernet.etherType)) true false)
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
(egress) ipv4.ttl: (let ((a!1 (ite (and true (= (concat #x0 #x800) ethernet.etherType)) true false))
      (a!3 (not (and true
                     (= ((_ extract 31 16) ipv4.dstAddr)
                        ((_ extract 31 16) #x0a0a0000)))))
      (a!6 (not (and true
                     (= ((_ extract 31 16) ipv4.dstAddr)
                        ((_ extract 31 16) #x14140000))))))
(let ((a!2 (and (and true a!1)
                (not (and true (= ipv4.dstAddr #x0a0a0000)))
                (and true
                     (= ((_ extract 31 16) ipv4.dstAddr)
                        ((_ extract 31 16) #x0a0a0000)))))
      (a!4 (and (not (and true (= ipv4.dstAddr #x0a0a0000))) a!3)))
(let ((a!5 (and (and true a!1)
                a!4
                (and true
                     (= ((_ extract 31 16) ipv4.dstAddr)
                        ((_ extract 31 16) #x14140000)))))
      (a!7 (ite (and (and true a!1)
                     a!4
                     a!6
                     true
                     (= ((_ extract 31 24) ipv4.dstAddr)
                        ((_ extract 31 24) #x0a000000)))
                (bvand (bvadd ipv4.ttl #xff) #xff)
                ipv4.ttl)))
(let ((a!8 (bvadd (ite a!5 (bvand (bvadd a!7 #xff) #xff) a!7) #xff)))
(let ((a!9 (ite a!2
                (bvand a!8 #xff)
                (ite a!5 (bvand (bvadd a!7 #xff) #xff) a!7))))
  (ite (and (and true a!1) (and true (= ipv4.dstAddr #x0a0a0000)))
       (bvand (bvadd a!9 #xff) #xff)
       a!9))))))
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
(egress) standard_metadata.egress_port: (let ((a!1 (ite (and true (= (concat #x0 #x800) ethernet.etherType)) true false))
      (a!3 (not (and true
                     (= ((_ extract 31 16) ipv4.dstAddr)
                        ((_ extract 31 16) #x0a0a0000)))))
      (a!6 (not (and true
                     (= ((_ extract 31 16) ipv4.dstAddr)
                        ((_ extract 31 16) #x14140000)))))
      (a!8 (not (and true
                     (= ((_ extract 31 24) ipv4.dstAddr)
                        ((_ extract 31 24) #x0a000000))))))
(let ((a!2 (and (and true a!1)
                (not (and true (= ipv4.dstAddr #x0a0a0000)))
                (and true
                     (= ((_ extract 31 16) ipv4.dstAddr)
                        ((_ extract 31 16) #x0a0a0000)))))
      (a!4 (and (not (and true (= ipv4.dstAddr #x0a0a0000))) a!3)))
(let ((a!5 (and (and true a!1)
                a!4
                (and true
                     (= ((_ extract 31 16) ipv4.dstAddr)
                        ((_ extract 31 16) #x14140000)))))
      (a!7 (and (and true a!1)
                (and a!4 a!6)
                (and true
                     (= ((_ extract 31 24) ipv4.dstAddr)
                        ((_ extract 31 24) #x0a000000))))))
(let ((a!9 (ite a!7
                #b000000001
                (ite (and (and true a!1) (and a!4 a!6) a!8)
                     #b111111111
                     #b000000000))))
(let ((a!10 (ite (and (and true a!1) (and true (= ipv4.dstAddr #x0a0a0000)))
                 #b000000001
                 (ite a!2 #b000000000 (ite a!5 #b000000001 a!9)))))
  (ite (not (= a!10 #b111111111)) a!10 standard_metadata.egress_port))))))
(egress) standard_metadata.egress_rid: #x0000
(egress) standard_metadata.egress_spec: (let ((a!1 (ite (and true (= (concat #x0 #x800) ethernet.etherType)) true false))
      (a!3 (not (and true
                     (= ((_ extract 31 16) ipv4.dstAddr)
                        ((_ extract 31 16) #x0a0a0000)))))
      (a!6 (not (and true
                     (= ((_ extract 31 16) ipv4.dstAddr)
                        ((_ extract 31 16) #x14140000)))))
      (a!8 (not (and true
                     (= ((_ extract 31 24) ipv4.dstAddr)
                        ((_ extract 31 24) #x0a000000))))))
(let ((a!2 (and (and true a!1)
                (not (and true (= ipv4.dstAddr #x0a0a0000)))
                (and true
                     (= ((_ extract 31 16) ipv4.dstAddr)
                        ((_ extract 31 16) #x0a0a0000)))))
      (a!4 (and (not (and true (= ipv4.dstAddr #x0a0a0000))) a!3)))
(let ((a!5 (and (and true a!1)
                a!4
                (and true
                     (= ((_ extract 31 16) ipv4.dstAddr)
                        ((_ extract 31 16) #x14140000)))))
      (a!7 (and (and true a!1)
                (and a!4 a!6)
                (and true
                     (= ((_ extract 31 24) ipv4.dstAddr)
                        ((_ extract 31 24) #x0a000000))))))
(let ((a!9 (ite a!7
                #b000000001
                (ite (and (and true a!1) (and a!4 a!6) a!8)
                     #b111111111
                     #b000000000))))
  (ite (and (and true a!1) (and true (= ipv4.dstAddr #x0a0a0000)))
       #b000000001
       (ite a!2 #b000000000 (ite a!5 #b000000001 a!9)))))))
(egress) standard_metadata.enq_qdepth: #b0000000000000000000
(egress) standard_metadata.enq_timestamp: #x00000000
(egress) standard_metadata.ingress_global_timestamp: #x000000000000
(egress) standard_metadata.ingress_port: standard_metadata.ingress_port
(egress) standard_metadata.instance_type: #x00000000
(egress) standard_metadata.mcast_grp: #x0000
(egress) standard_metadata.packet_length: standard_metadata.packet_length
(egress) standard_metadata.parser_error: (let ((a!1 (and true (not (= (concat #x0 #x800) ethernet.etherType)) (not true)))
      (a!2 (ite (and true (= (concat #x0 #x800) ethernet.etherType) (not true))
                #x00000002
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
 (let (($x129 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x129)))
(assert
 (let (($x50 (= ipv4.dstAddr (_ bv168427520 32))))
 (let (($x51 (and true $x50)))
 (let (($x66 (not $x51)))
 (let (($x70 (and $x66 (not (and true (= ((_ extract 31 16) ipv4.dstAddr) ((_ extract 31 16) (_ bv168427520 32))))))))
 (let (($x74 (and $x70 (not (and true (= ((_ extract 31 16) ipv4.dstAddr) ((_ extract 31 16) (_ bv336855040 32))))))))
 (let (($x78 (and $x74 (not (and true (= ((_ extract 31 24) ipv4.dstAddr) ((_ extract 31 24) (_ bv167772160 32))))))))
 (let (($x11 (= (concat (_ bv0 4) (_ bv2048 12)) ethernet.etherType)))
 (let (($x10 (and true $x11)))
 (let (($x38 (ite $x10 true false)))
 (let (($x47 (and true $x38)))
 (let (($x64 (and true (= ((_ extract 31 24) ipv4.dstAddr) ((_ extract 31 24) (_ bv167772160 32))))))
 (let (($x76 (and (and $x47 $x74) $x64)))
 (let (($x59 (and true (= ((_ extract 31 16) ipv4.dstAddr) ((_ extract 31 16) (_ bv336855040 32))))))
 (let (($x72 (and (and $x47 $x70) $x59)))
 (let (($x55 (and true (= ((_ extract 31 16) ipv4.dstAddr) ((_ extract 31 16) (_ bv168427520 32))))))
 (let (($x68 (and (and $x47 $x66) $x55)))
 (let ((?x108 (ite $x68 (_ bv0 9) (ite $x72 (_ bv1 9) (ite $x76 (_ bv1 9) (ite (and $x47 $x78) (_ bv511 9) (_ bv0 9)))))))
 (let (($x65 (and $x47 $x51)))
 (let ((?x116 (ite $x65 (_ bv1 9) ?x108)))
 (let (($x132 (or (or false (= ?x116 (_ bv0 9))) (= ?x116 (_ bv1 9)))))
 (let (($x44 (= ?x116 (_ bv511 9))))
 (or $x44 $x132)))))))))))))))))))))))
(check-sat)
