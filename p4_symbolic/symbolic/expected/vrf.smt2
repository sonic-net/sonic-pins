(ingress) $got_cloned$: false
(ingress) $got_recirculated$: false
(ingress) ethernet.$extracted$: false
(ingress) ethernet.$valid$: (ite true true false)
(ingress) ethernet.dstAddr: ethernet.dstAddr
(ingress) ethernet.eth_type: ethernet.eth_type
(ingress) ethernet.srcAddr: ethernet.srcAddr
(ingress) ipv4.$extracted$: false
(ingress) ipv4.$valid$: (ite (and true (= (concat #x0 #x800) ethernet.eth_type)) true false)
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
(parsed) ethernet.$extracted$: (ite true true false)
(parsed) ethernet.$valid$: (ite true true false)
(parsed) ethernet.dstAddr: ethernet.dstAddr
(parsed) ethernet.eth_type: ethernet.eth_type
(parsed) ethernet.srcAddr: ethernet.srcAddr
(parsed) ipv4.$extracted$: (ite (and true (= (concat #x0 #x800) ethernet.eth_type)) true false)
(parsed) ipv4.$valid$: (ite (and true (= (concat #x0 #x800) ethernet.eth_type)) true false)
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
      (a!2 (ite (and true (= (concat #x0 #x800) ethernet.eth_type) (not true))
                #x00000002
                #x00000000)))
  (ite a!1 #x00000002 a!2))
(parsed) standard_metadata.priority: #b000

(egress) $got_cloned$: false
(egress) $got_recirculated$: false
(egress) ethernet.$extracted$: (ite true true false)
(egress) ethernet.$valid$: (ite true true false)
(egress) ethernet.dstAddr: (let ((a!1 (ite (and true (= (concat #x0 #x800) ethernet.eth_type)) true false))
      (a!3 (not (and true (= (bvand ipv4.srcAddr #x09210909) #x00210100)))))
(let ((a!2 (and (and true a!1)
                (and true (= (bvand ipv4.srcAddr #x09210909) #x00210100))))
      (a!4 (and (and true a!1)
                a!3
                true
                (= (bvand ipv4.srcAddr #x21210909) #x21210000))))
(let ((a!5 (ite a!2
                (ite true #b1 #b0)
                (ite a!4
                     (ite true #b1 #b0)
                     (ite true
                          (ite false #b1 #b0)
                          scalars.local_metadata_t.vrf_is_valid))))
      (a!6 (ite a!2
                (concat #b000000000 #b1)
                (ite a!4
                     (concat #b000000000 #b0)
                     (ite true
                          (concat #b000000000 #b0)
                          scalars.local_metadata_t.vrf)))))
(let ((a!7 (and true
                (= ipv4.dstAddr #x0a0a0000)
                (= a!6 (concat #b000000000 #b0))))
      (a!8 (and true
                (= ((_ extract 31 16) ipv4.dstAddr)
                   ((_ extract 31 16) #x0a0a0000))
                (= a!6 (concat #b000000000 #b0))))
      (a!9 (and true
                (= ((_ extract 31 16) ipv4.dstAddr)
                   ((_ extract 31 16) #x14140000))
                (= a!6 (concat #b000000000 #b1)))))
(let ((a!10 (ite (and (and (and true a!1) (bvuge a!5 #b1))
                      (and (not a!7) (not a!8))
                      (not a!9)
                      true
                      (= ((_ extract 31 24) ipv4.dstAddr)
                         ((_ extract 31 24) #x0a000000))
                      (= a!6 (concat #b000000000 #b0)))
                 #x00000000000a
                 ethernet.dstAddr)))
(let ((a!11 (ite (and (and (and true a!1) (bvuge a!5 #b1))
                      (and (not a!7) (not a!8))
                      a!9)
                 #x160000000016
                 a!10)))
(let ((a!12 (ite (and (and (and true a!1) (bvuge a!5 #b1)) (not a!7) a!8)
                 #x000000000000
                 a!11)))
  (ite (and (and (and true a!1) (bvuge a!5 #b1)) a!7) #x000000000000 a!12))))))))
(egress) ethernet.eth_type: ethernet.eth_type
(egress) ethernet.srcAddr: (let ((a!1 (ite (and true (= (concat #x0 #x800) ethernet.eth_type)) true false))
      (a!3 (not (and true (= (bvand ipv4.srcAddr #x09210909) #x00210100)))))
(let ((a!2 (and (and true a!1)
                (and true (= (bvand ipv4.srcAddr #x09210909) #x00210100))))
      (a!4 (and (and true a!1)
                a!3
                true
                (= (bvand ipv4.srcAddr #x21210909) #x21210000))))
(let ((a!5 (ite a!2
                (ite true #b1 #b0)
                (ite a!4
                     (ite true #b1 #b0)
                     (ite true
                          (ite false #b1 #b0)
                          scalars.local_metadata_t.vrf_is_valid))))
      (a!6 (ite a!2
                (concat #b000000000 #b1)
                (ite a!4
                     (concat #b000000000 #b0)
                     (ite true
                          (concat #b000000000 #b0)
                          scalars.local_metadata_t.vrf)))))
(let ((a!7 (and true
                (= ipv4.dstAddr #x0a0a0000)
                (= a!6 (concat #b000000000 #b0))))
      (a!8 (and true
                (= ((_ extract 31 16) ipv4.dstAddr)
                   ((_ extract 31 16) #x0a0a0000))
                (= a!6 (concat #b000000000 #b0))))
      (a!10 (and true
                 (= ((_ extract 31 16) ipv4.dstAddr)
                    ((_ extract 31 16) #x14140000))
                 (= a!6 (concat #b000000000 #b1)))))
(let ((a!9 (and (and (and true a!1) (bvuge a!5 #b1)) (not a!7) a!8))
      (a!11 (and (and (and true a!1) (bvuge a!5 #b1))
                 (and (not a!7) (not a!8))
                 a!10))
      (a!12 (and (and (and true a!1) (bvuge a!5 #b1))
                 (and (not a!7) (not a!8))
                 (not a!10)
                 true
                 (= ((_ extract 31 24) ipv4.dstAddr)
                    ((_ extract 31 24) #x0a000000))
                 (= a!6 (concat #b000000000 #b0)))))
  (ite (and (and (and true a!1) (bvuge a!5 #b1)) a!7)
       (ite a!9
            #x000000000000
            (ite a!11 #x160000000016 (ite a!12 #x00000000000a ethernet.dstAddr)))
       (ite a!9
            (ite a!11 #x160000000016 (ite a!12 #x00000000000a ethernet.dstAddr))
            (ite a!11
                 (ite a!12 #x00000000000a ethernet.dstAddr)
                 (ite a!12 ethernet.dstAddr ethernet.srcAddr)))))))))
(egress) ipv4.$extracted$: (ite (and true (= (concat #x0 #x800) ethernet.eth_type)) true false)
(egress) ipv4.$valid$: (ite (and true (= (concat #x0 #x800) ethernet.eth_type)) true false)
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
(egress) ipv4.ttl: (let ((a!1 (ite (and true (= (concat #x0 #x800) ethernet.eth_type)) true false))
      (a!3 (not (and true (= (bvand ipv4.srcAddr #x09210909) #x00210100)))))
(let ((a!2 (and (and true a!1)
                (and true (= (bvand ipv4.srcAddr #x09210909) #x00210100))))
      (a!4 (and (and true a!1)
                a!3
                true
                (= (bvand ipv4.srcAddr #x21210909) #x21210000))))
(let ((a!5 (ite a!2
                (ite true #b1 #b0)
                (ite a!4
                     (ite true #b1 #b0)
                     (ite true
                          (ite false #b1 #b0)
                          scalars.local_metadata_t.vrf_is_valid))))
      (a!6 (ite a!2
                (concat #b000000000 #b1)
                (ite a!4
                     (concat #b000000000 #b0)
                     (ite true
                          (concat #b000000000 #b0)
                          scalars.local_metadata_t.vrf)))))
(let ((a!7 (and true
                (= ipv4.dstAddr #x0a0a0000)
                (= a!6 (concat #b000000000 #b0))))
      (a!8 (and true
                (= ((_ extract 31 16) ipv4.dstAddr)
                   ((_ extract 31 16) #x0a0a0000))
                (= a!6 (concat #b000000000 #b0))))
      (a!9 (and true
                (= ((_ extract 31 16) ipv4.dstAddr)
                   ((_ extract 31 16) #x14140000))
                (= a!6 (concat #b000000000 #b1)))))
(let ((a!10 (ite (and (and (and true a!1) (bvuge a!5 #b1))
                      (and (not a!7) (not a!8))
                      (not a!9)
                      true
                      (= ((_ extract 31 24) ipv4.dstAddr)
                         ((_ extract 31 24) #x0a000000))
                      (= a!6 (concat #b000000000 #b0)))
                 (bvand (bvadd ipv4.ttl #xff) #xff)
                 ipv4.ttl)))
(let ((a!11 (ite (and (and (and true a!1) (bvuge a!5 #b1))
                      (and (not a!7) (not a!8))
                      a!9)
                 (bvand (bvadd a!10 #xff) #xff)
                 a!10)))
(let ((a!12 (ite (and (and (and true a!1) (bvuge a!5 #b1)) (not a!7) a!8)
                 (bvand (bvadd a!11 #xff) #xff)
                 a!11)))
  (ite (and (and (and true a!1) (bvuge a!5 #b1)) a!7)
       (bvand (bvadd a!12 #xff) #xff)
       a!12))))))))
(egress) ipv4.version: ipv4.version
(egress) scalars.$extracted$: false
(egress) scalars.$valid$: false
(egress) scalars._padding_0: scalars._padding_0
(egress) scalars.local_metadata_t.vrf: (let ((a!1 (ite (and true (= (concat #x0 #x800) ethernet.eth_type)) true false))
      (a!3 (not (and true (= (bvand ipv4.srcAddr #x09210909) #x00210100)))))
(let ((a!2 (and (and true a!1)
                (and true (= (bvand ipv4.srcAddr #x09210909) #x00210100))))
      (a!4 (ite (and (and true a!1)
                     a!3
                     true
                     (= (bvand ipv4.srcAddr #x21210909) #x21210000))
                (concat #b000000000 #b0)
                (ite true (concat #b000000000 #b0) scalars.local_metadata_t.vrf))))
  (ite a!2 (concat #b000000000 #b1) a!4)))
(egress) scalars.local_metadata_t.vrf_is_valid: (let ((a!1 (ite (and true (= (concat #x0 #x800) ethernet.eth_type)) true false))
      (a!3 (not (and true (= (bvand ipv4.srcAddr #x09210909) #x00210100)))))
(let ((a!2 (and (and true a!1)
                (and true (= (bvand ipv4.srcAddr #x09210909) #x00210100))))
      (a!4 (ite (and (and true a!1)
                     a!3
                     true
                     (= (bvand ipv4.srcAddr #x21210909) #x21210000))
                (ite true #b1 #b0)
                (ite true
                     (ite false #b1 #b0)
                     scalars.local_metadata_t.vrf_is_valid))))
  (ite a!2 (ite true #b1 #b0) a!4)))
(egress) standard_metadata.$extracted$: false
(egress) standard_metadata.$valid$: false
(egress) standard_metadata._padding: standard_metadata._padding
(egress) standard_metadata.checksum_error: #b0
(egress) standard_metadata.deq_qdepth: #b0000000000000000000
(egress) standard_metadata.deq_timedelta: #x00000000
(egress) standard_metadata.egress_global_timestamp: #x000000000000
(egress) standard_metadata.egress_port: (let ((a!1 (ite (and true (= (concat #x0 #x800) ethernet.eth_type)) true false))
      (a!3 (not (and true (= (bvand ipv4.srcAddr #x09210909) #x00210100)))))
(let ((a!2 (and (and true a!1)
                (and true (= (bvand ipv4.srcAddr #x09210909) #x00210100))))
      (a!4 (and (and true a!1)
                a!3
                true
                (= (bvand ipv4.srcAddr #x21210909) #x21210000))))
(let ((a!5 (ite a!2
                (ite true #b1 #b0)
                (ite a!4
                     (ite true #b1 #b0)
                     (ite true
                          (ite false #b1 #b0)
                          scalars.local_metadata_t.vrf_is_valid))))
      (a!6 (ite a!2
                (concat #b000000000 #b1)
                (ite a!4
                     (concat #b000000000 #b0)
                     (ite true
                          (concat #b000000000 #b0)
                          scalars.local_metadata_t.vrf)))))
(let ((a!7 (and true
                (= ipv4.dstAddr #x0a0a0000)
                (= a!6 (concat #b000000000 #b0))))
      (a!8 (and true
                (= ((_ extract 31 16) ipv4.dstAddr)
                   ((_ extract 31 16) #x0a0a0000))
                (= a!6 (concat #b000000000 #b0))))
      (a!9 (and true
                (= ((_ extract 31 16) ipv4.dstAddr)
                   ((_ extract 31 16) #x14140000))
                (= a!6 (concat #b000000000 #b1))))
      (a!10 (and true
                 (= ((_ extract 31 24) ipv4.dstAddr)
                    ((_ extract 31 24) #x0a000000))
                 (= a!6 (concat #b000000000 #b0)))))
(let ((a!11 (and (and (and true a!1) (bvuge a!5 #b1))
                 (and (and (not a!7) (not a!8)) (not a!9))
                 a!10))
      (a!12 (and (and (and true a!1) (bvuge a!5 #b1))
                 (and (and (not a!7) (not a!8)) (not a!9))
                 (not a!10))))
(let ((a!13 (ite (and (and (and true a!1) (bvuge a!5 #b1))
                      (and (not a!7) (not a!8))
                      a!9)
                 #b000000001
                 (ite a!11 #b000000001 (ite a!12 #b111111111 #b000000000)))))
(let ((a!14 (ite (and (and (and true a!1) (bvuge a!5 #b1)) (not a!7) a!8)
                 #b000000000
                 a!13)))
(let ((a!15 (ite (and (and (and true a!1) (bvuge a!5 #b1)) a!7)
                 #b000000001
                 a!14)))
  (ite (not (= a!15 #b111111111)) a!15 standard_metadata.egress_port)))))))))
(egress) standard_metadata.egress_rid: #x0000
(egress) standard_metadata.egress_spec: (let ((a!1 (ite (and true (= (concat #x0 #x800) ethernet.eth_type)) true false))
      (a!3 (not (and true (= (bvand ipv4.srcAddr #x09210909) #x00210100)))))
(let ((a!2 (and (and true a!1)
                (and true (= (bvand ipv4.srcAddr #x09210909) #x00210100))))
      (a!4 (and (and true a!1)
                a!3
                true
                (= (bvand ipv4.srcAddr #x21210909) #x21210000))))
(let ((a!5 (ite a!2
                (ite true #b1 #b0)
                (ite a!4
                     (ite true #b1 #b0)
                     (ite true
                          (ite false #b1 #b0)
                          scalars.local_metadata_t.vrf_is_valid))))
      (a!6 (ite a!2
                (concat #b000000000 #b1)
                (ite a!4
                     (concat #b000000000 #b0)
                     (ite true
                          (concat #b000000000 #b0)
                          scalars.local_metadata_t.vrf)))))
(let ((a!7 (and true
                (= ipv4.dstAddr #x0a0a0000)
                (= a!6 (concat #b000000000 #b0))))
      (a!8 (and true
                (= ((_ extract 31 16) ipv4.dstAddr)
                   ((_ extract 31 16) #x0a0a0000))
                (= a!6 (concat #b000000000 #b0))))
      (a!9 (and true
                (= ((_ extract 31 16) ipv4.dstAddr)
                   ((_ extract 31 16) #x14140000))
                (= a!6 (concat #b000000000 #b1))))
      (a!10 (and true
                 (= ((_ extract 31 24) ipv4.dstAddr)
                    ((_ extract 31 24) #x0a000000))
                 (= a!6 (concat #b000000000 #b0)))))
(let ((a!11 (and (and (and true a!1) (bvuge a!5 #b1))
                 (and (and (not a!7) (not a!8)) (not a!9))
                 a!10))
      (a!12 (and (and (and true a!1) (bvuge a!5 #b1))
                 (and (and (not a!7) (not a!8)) (not a!9))
                 (not a!10))))
(let ((a!13 (ite (and (and (and true a!1) (bvuge a!5 #b1))
                      (and (not a!7) (not a!8))
                      a!9)
                 #b000000001
                 (ite a!11 #b000000001 (ite a!12 #b111111111 #b000000000)))))
(let ((a!14 (ite (and (and (and true a!1) (bvuge a!5 #b1)) (not a!7) a!8)
                 #b000000000
                 a!13)))
  (ite (and (and (and true a!1) (bvuge a!5 #b1)) a!7) #b000000001 a!14))))))))
(egress) standard_metadata.enq_qdepth: #b0000000000000000000
(egress) standard_metadata.enq_timestamp: #x00000000
(egress) standard_metadata.ingress_global_timestamp: #x000000000000
(egress) standard_metadata.ingress_port: standard_metadata.ingress_port
(egress) standard_metadata.instance_type: #x00000000
(egress) standard_metadata.mcast_grp: #x0000
(egress) standard_metadata.packet_length: standard_metadata.packet_length
(egress) standard_metadata.parser_error: (let ((a!1 (and true (not (= (concat #x0 #x800) ethernet.eth_type)) (not true)))
      (a!2 (ite (and true (= (concat #x0 #x800) ethernet.eth_type) (not true))
                #x00000002
                #x00000000)))
  (ite a!1 #x00000002 a!2))
(egress) standard_metadata.priority: #b000

(solver constraints)
; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(declare-fun scalars.local_metadata_t.vrf () (_ BitVec 10))
(declare-fun ipv4.srcAddr () (_ BitVec 32))
(declare-fun ethernet.eth_type () (_ BitVec 16))
(declare-fun ipv4.dstAddr () (_ BitVec 32))
(declare-fun scalars.local_metadata_t.vrf_is_valid () (_ BitVec 1))
(assert
 (let (($x172 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x172)))
(assert
 (let ((?x53 (concat (_ bv0 9) (_ bv0 1))))
 (let (($x67 (and true (= (bvand ipv4.srcAddr (_ bv555813129 32)) (_ bv555810816 32)))))
 (let (($x11 (= (concat (_ bv0 4) (_ bv2048 12)) ethernet.eth_type)))
 (let (($x10 (and true $x11)))
 (let (($x41 (ite $x10 true false)))
 (let (($x56 (and true $x41)))
 (let (($x71 (and (and $x56 (not (and true (= (bvand ipv4.srcAddr (_ bv153159945 32)) (_ bv2162944 32))))) $x67)))
 (let ((?x83 (concat (_ bv0 9) (_ bv1 1))))
 (let (($x62 (and true (= (bvand ipv4.srcAddr (_ bv153159945 32)) (_ bv2162944 32)))))
 (let (($x68 (and $x56 $x62)))
 (let ((?x84 (ite $x68 ?x83 (ite $x71 ?x53 (ite true ?x53 scalars.local_metadata_t.vrf)))))
 (let (($x93 (= ?x84 ?x53)))
 (let (($x111 (and (and true (= ((_ extract 31 24) ipv4.dstAddr) ((_ extract 31 24) (_ bv167772160 32)))) $x93)))
 (let (($x105 (and (and true (= ((_ extract 31 16) ipv4.dstAddr) ((_ extract 31 16) (_ bv336855040 32)))) (= ?x84 ?x83))))
 (let (($x99 (and (and true (= ((_ extract 31 16) ipv4.dstAddr) ((_ extract 31 16) (_ bv168427520 32)))) $x93)))
 (let (($x94 (and (and true (= ipv4.dstAddr (_ bv168427520 32))) $x93)))
 (let (($x113 (not $x94)))
 (let (($x117 (and $x113 (not $x99))))
 (let (($x121 (and $x117 (not $x105))))
 (let ((?x51 (ite false (_ bv1 1) (_ bv0 1))))
 (let ((?x79 (ite true (_ bv1 1) (_ bv0 1))))
 (let ((?x85 (ite $x68 ?x79 (ite $x71 ?x79 (ite true ?x51 scalars.local_metadata_t.vrf_is_valid)))))
 (let (($x86 (bvuge ?x85 (_ bv1 1))))
 (let (($x88 (and $x56 $x86)))
 (let (($x123 (and (and $x88 $x121) $x111)))
 (let (($x119 (and (and $x88 $x117) $x105)))
 (let ((?x145 (ite $x119 (_ bv1 9) (ite $x123 (_ bv1 9) (ite (and $x88 (and $x121 (not $x111))) (_ bv511 9) (_ bv0 9))))))
 (let (($x115 (and (and $x88 $x113) $x99)))
 (let (($x112 (and $x88 $x94)))
 (let ((?x160 (ite $x112 (_ bv1 9) (ite $x115 (_ bv0 9) ?x145))))
 (let (($x175 (or (or false (= ?x160 (_ bv0 9))) (= ?x160 (_ bv1 9)))))
 (let (($x55 (= ?x160 (_ bv511 9))))
 (or $x55 $x175))))))))))))))))))))))))))))))))))
(check-sat)
