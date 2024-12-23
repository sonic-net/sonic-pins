(ingress) $got_cloned$: false
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
(parsed) standard_metadata.parser_error: (let ((a!1 (and true (not (= (concat #x0 #x800) ethernet.etherType)) (not true)))
      (a!2 (ite (and true (= (concat #x0 #x800) ethernet.etherType) (not true))
                #x00000002
                #x00000000)))
  (ite a!1 #x00000002 a!2))
(parsed) standard_metadata.priority: standard_metadata.priority

(egress) $got_cloned$: false
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
(egress) standard_metadata.checksum_error: standard_metadata.checksum_error
(egress) standard_metadata.deq_qdepth: standard_metadata.deq_qdepth
(egress) standard_metadata.deq_timedelta: standard_metadata.deq_timedelta
(egress) standard_metadata.egress_global_timestamp: standard_metadata.egress_global_timestamp
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
                     standard_metadata.egress_spec))))
(let ((a!10 (ite (and (and true a!1) (and true (= ipv4.dstAddr #x0a0a0000)))
                 #b000000001
                 (ite a!2 #b000000000 (ite a!5 #b000000001 a!9)))))
  (ite true a!10 standard_metadata.egress_port))))))
(egress) standard_metadata.egress_rid: standard_metadata.egress_rid
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
                     standard_metadata.egress_spec))))
  (ite (and (and true a!1) (and true (= ipv4.dstAddr #x0a0a0000)))
       #b000000001
       (ite a!2 #b000000000 (ite a!5 #b000000001 a!9)))))))
(egress) standard_metadata.enq_qdepth: standard_metadata.enq_qdepth
(egress) standard_metadata.enq_timestamp: standard_metadata.enq_timestamp
(egress) standard_metadata.ingress_global_timestamp: standard_metadata.ingress_global_timestamp
(egress) standard_metadata.ingress_port: standard_metadata.ingress_port
(egress) standard_metadata.instance_type: standard_metadata.instance_type
(egress) standard_metadata.mcast_grp: standard_metadata.mcast_grp
(egress) standard_metadata.packet_length: standard_metadata.packet_length
(egress) standard_metadata.parser_error: (let ((a!1 (and true (not (= (concat #x0 #x800) ethernet.etherType)) (not true)))
      (a!2 (ite (and true (= (concat #x0 #x800) ethernet.etherType) (not true))
                #x00000002
                #x00000000)))
  (ite a!1 #x00000002 a!2))
(egress) standard_metadata.priority: standard_metadata.priority

(solver constraints)
; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(declare-fun standard_metadata.egress_spec () (_ BitVec 9))
(declare-fun ipv4.dstAddr () (_ BitVec 32))
(declare-fun ethernet.etherType () (_ BitVec 16))
(assert
 (let (($x136 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x136)))
(assert
 (let (($x56 (= ipv4.dstAddr (_ bv168427520 32))))
 (let (($x57 (and true $x56)))
 (let (($x72 (not $x57)))
 (let (($x76 (and $x72 (not (and true (= ((_ extract 31 16) ipv4.dstAddr) ((_ extract 31 16) (_ bv168427520 32))))))))
 (let (($x80 (and $x76 (not (and true (= ((_ extract 31 16) ipv4.dstAddr) ((_ extract 31 16) (_ bv336855040 32))))))))
 (let (($x84 (and $x80 (not (and true (= ((_ extract 31 24) ipv4.dstAddr) ((_ extract 31 24) (_ bv167772160 32))))))))
 (let (($x11 (= (concat (_ bv0 4) (_ bv2048 12)) ethernet.etherType)))
 (let (($x10 (and true $x11)))
 (let (($x48 (ite $x10 true false)))
 (let (($x53 (and true $x48)))
 (let (($x70 (and true (= ((_ extract 31 24) ipv4.dstAddr) ((_ extract 31 24) (_ bv167772160 32))))))
 (let (($x82 (and (and $x53 $x80) $x70)))
 (let ((?x94 (ite $x82 (_ bv1 9) (ite (and $x53 $x84) (_ bv511 9) standard_metadata.egress_spec))))
 (let (($x65 (and true (= ((_ extract 31 16) ipv4.dstAddr) ((_ extract 31 16) (_ bv336855040 32))))))
 (let (($x78 (and (and $x53 $x76) $x65)))
 (let (($x61 (and true (= ((_ extract 31 16) ipv4.dstAddr) ((_ extract 31 16) (_ bv168427520 32))))))
 (let (($x74 (and (and $x53 $x72) $x61)))
 (let (($x71 (and $x53 $x57)))
 (let ((?x124 (ite $x71 (_ bv1 9) (ite $x74 (_ bv0 9) (ite $x78 (_ bv1 9) ?x94)))))
 (let (($x139 (or (or false (= ?x124 (_ bv0 9))) (= ?x124 (_ bv1 9)))))
 (let (($x45 (= ?x124 (_ bv511 9))))
 (or $x45 $x139)))))))))))))))))))))))
(check-sat)
