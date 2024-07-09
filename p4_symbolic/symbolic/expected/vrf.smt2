(ingress) $got_cloned$: false
(ingress) $got_recirculated$: false
(ingress) ethernet.$extracted$: false
(ingress) ethernet.$valid$: true
(ingress) ethernet.dstAddr: ethernet.dstAddr
(ingress) ethernet.eth_type: ethernet.eth_type
(ingress) ethernet.srcAddr: ethernet.srcAddr
(ingress) ipv4.$extracted$: false
(ingress) ipv4.$valid$: (= ethernet.eth_type #x0800)
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
(parsed) ipv4.$extracted$: (= ethernet.eth_type #x0800)
(parsed) ipv4.$valid$: (= ethernet.eth_type #x0800)
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
(parsed) standard_metadata.parser_error: #x00000000
(parsed) standard_metadata.priority: #b000

(egress) $got_cloned$: false
(egress) $got_recirculated$: false
(egress) ethernet.$extracted$: true
(egress) ethernet.$valid$: true
(egress) ethernet.dstAddr: (let ((a!1 (not (and (= ethernet.eth_type #x0800)
                     (= ((_ extract 0 0) ipv4.srcAddr) #b0)
                     (= ((_ extract 3 3) ipv4.srcAddr) #b0)
                     (= ((_ extract 8 8) ipv4.srcAddr) #b1)
                     (= ((_ extract 11 11) ipv4.srcAddr) #b0)
                     (= ((_ extract 16 16) ipv4.srcAddr) #b1)
                     (= ((_ extract 21 21) ipv4.srcAddr) #b1)
                     (= ((_ extract 24 24) ipv4.srcAddr) #b0)
                     (= ((_ extract 27 27) ipv4.srcAddr) #b0))))
      (a!2 (and (= ((_ extract 8 8) ipv4.srcAddr) #b1)
                (= ((_ extract 24 24) ipv4.srcAddr) #b0)
                (= ((_ extract 27 27) ipv4.srcAddr) #b0)))
      (a!4 (and (= #x0800 #x0800)
                (= #b0 #b0)
                (= ((_ extract 0 0) ipv4.srcAddr) #b0)
                (= ((_ extract 0 0) ipv4.srcAddr) #b0)
                (= #b1 #b1)
                (= ((_ extract 16 16) ipv4.srcAddr) #b1)
                true
                (not (and (= ipv4.dstAddr #x0a0a0000) (not false)))
                (= ((_ extract 31 16) ipv4.dstAddr) #x0a0a)
                (not false)))
      (a!8 (not (and (= ((_ extract 31 16) ipv4.dstAddr) #x1414)
                     (= ethernet.eth_type #x0800)
                     (= ((_ extract 0 0) ipv4.srcAddr) #b0)
                     (= ((_ extract 3 3) ipv4.srcAddr) #b0)
                     (= ((_ extract 8 8) ipv4.srcAddr) #b1)
                     (= ((_ extract 11 11) ipv4.srcAddr) #b0)
                     (= ((_ extract 16 16) ipv4.srcAddr) #b1)
                     (= ((_ extract 21 21) ipv4.srcAddr) #b1)
                     (= ((_ extract 24 24) ipv4.srcAddr) #b0)
                     (= ((_ extract 27 27) ipv4.srcAddr) #b0)))))
(let ((a!3 (or a!2
               (and (not a!2)
                    (= ((_ extract 8 8) ipv4.srcAddr) #b0)
                    (= ((_ extract 24 24) ipv4.srcAddr) #b1)
                    (= ((_ extract 29 29) ipv4.srcAddr) #b1))))
      (a!5 (or (and (= #x0800 #x0800)
                    (= #b0 #b0)
                    (= ((_ extract 0 0) ipv4.srcAddr) #b0)
                    (= ((_ extract 0 0) ipv4.srcAddr) #b0)
                    (= #b1 #b1)
                    (= ((_ extract 16 16) ipv4.srcAddr) #b1)
                    true
                    (= ipv4.dstAddr #x0a0a0000)
                    (not false))
               a!4))
      (a!6 (not (and (= ((_ extract 31 16) ipv4.dstAddr) #x0a0a) a!1))))
(let ((a!7 (and (= ethernet.eth_type #x0800)
                (= ((_ extract 0 0) ipv4.srcAddr) #b0)
                (= ((_ extract 11 11) ipv4.srcAddr)
                   ((_ extract 0 0) ipv4.srcAddr))
                (= ((_ extract 3 3) ipv4.srcAddr)
                   ((_ extract 0 0) ipv4.srcAddr))
                (= ((_ extract 16 16) ipv4.srcAddr) #b1)
                (= ((_ extract 21 21) ipv4.srcAddr)
                   ((_ extract 16 16) ipv4.srcAddr))
                a!3
                (not (and (= ipv4.dstAddr #x0a0a0000) a!1))
                a!6
                (= ((_ extract 31 16) ipv4.dstAddr) #x1414)
                (= ((_ extract 3 3) ipv4.srcAddr) #b0)
                (= ((_ extract 8 8) ipv4.srcAddr) #b1)
                (= ((_ extract 11 11) ipv4.srcAddr) #b0)
                (= ((_ extract 21 21) ipv4.srcAddr) #b1)
                (= ((_ extract 24 24) ipv4.srcAddr) #b0)
                (= ((_ extract 27 27) ipv4.srcAddr) #b0)))
      (a!9 (and (= ethernet.eth_type #x0800)
                (= ((_ extract 0 0) ipv4.srcAddr) #b0)
                (= ((_ extract 11 11) ipv4.srcAddr)
                   ((_ extract 0 0) ipv4.srcAddr))
                (= ((_ extract 3 3) ipv4.srcAddr)
                   ((_ extract 0 0) ipv4.srcAddr))
                (= ((_ extract 16 16) ipv4.srcAddr) #b1)
                (= ((_ extract 21 21) ipv4.srcAddr)
                   ((_ extract 16 16) ipv4.srcAddr))
                a!3
                (not (and (= ipv4.dstAddr #x0a0a0000) a!1))
                a!6
                a!8
                (= ((_ extract 31 24) ipv4.dstAddr) #x0a)
                a!1)))
  (ite (and a!1
            a!3
            (= ethernet.eth_type #x0800)
            (= ((_ extract 0 0) ipv4.srcAddr) #b0)
            (= ((_ extract 3 3) ipv4.srcAddr) ((_ extract 0 0) ipv4.srcAddr))
            (= ((_ extract 11 11) ipv4.srcAddr) ((_ extract 0 0) ipv4.srcAddr))
            (= ((_ extract 16 16) ipv4.srcAddr) #b1)
            (= ((_ extract 21 21) ipv4.srcAddr)
               ((_ extract 16 16) ipv4.srcAddr))
            a!5)
       #x000000000000
       (ite a!7 #x160000000016 (ite a!9 #x00000000000a ethernet.dstAddr))))))
(egress) ethernet.eth_type: ethernet.eth_type
(egress) ethernet.srcAddr: (let ((a!1 (and (= ((_ extract 8 8) ipv4.srcAddr) #b1)
                (= ((_ extract 24 24) ipv4.srcAddr) #b0)
                (= ((_ extract 27 27) ipv4.srcAddr) #b0)))
      (a!3 (not (and (= ethernet.eth_type #x0800)
                     (= ((_ extract 0 0) ipv4.srcAddr) #b0)
                     (= ((_ extract 3 3) ipv4.srcAddr) #b0)
                     (= ((_ extract 8 8) ipv4.srcAddr) #b1)
                     (= ((_ extract 11 11) ipv4.srcAddr) #b0)
                     (= ((_ extract 16 16) ipv4.srcAddr) #b1)
                     (= ((_ extract 21 21) ipv4.srcAddr) #b1)
                     (= ((_ extract 24 24) ipv4.srcAddr) #b0)
                     (= ((_ extract 27 27) ipv4.srcAddr) #b0))))
      (a!7 (not (and (= ((_ extract 31 16) ipv4.dstAddr) #x1414)
                     (= ethernet.eth_type #x0800)
                     (= ((_ extract 0 0) ipv4.srcAddr) #b0)
                     (= ((_ extract 3 3) ipv4.srcAddr) #b0)
                     (= ((_ extract 8 8) ipv4.srcAddr) #b1)
                     (= ((_ extract 11 11) ipv4.srcAddr) #b0)
                     (= ((_ extract 16 16) ipv4.srcAddr) #b1)
                     (= ((_ extract 21 21) ipv4.srcAddr) #b1)
                     (= ((_ extract 24 24) ipv4.srcAddr) #b0)
                     (= ((_ extract 27 27) ipv4.srcAddr) #b0)))))
(let ((a!2 (or a!1
               (and (not a!1)
                    (= ((_ extract 8 8) ipv4.srcAddr) #b0)
                    (= ((_ extract 24 24) ipv4.srcAddr) #b1)
                    (= ((_ extract 29 29) ipv4.srcAddr) #b1))))
      (a!5 (not (and (= ((_ extract 31 16) ipv4.dstAddr) #x0a0a) a!3))))
(let ((a!4 (and (= ethernet.eth_type #x0800)
                (= ((_ extract 0 0) ipv4.srcAddr) #b0)
                (= ((_ extract 11 11) ipv4.srcAddr)
                   ((_ extract 0 0) ipv4.srcAddr))
                (= ((_ extract 3 3) ipv4.srcAddr)
                   ((_ extract 0 0) ipv4.srcAddr))
                (= ((_ extract 16 16) ipv4.srcAddr) #b1)
                (= ((_ extract 21 21) ipv4.srcAddr)
                   ((_ extract 16 16) ipv4.srcAddr))
                a!2
                (not (and (= ipv4.dstAddr #x0a0a0000) a!3))
                (= ((_ extract 31 16) ipv4.dstAddr) #x0a0a)
                a!3))
      (a!6 (and (= ethernet.eth_type #x0800)
                (= ((_ extract 0 0) ipv4.srcAddr) #b0)
                (= ((_ extract 11 11) ipv4.srcAddr)
                   ((_ extract 0 0) ipv4.srcAddr))
                (= ((_ extract 3 3) ipv4.srcAddr)
                   ((_ extract 0 0) ipv4.srcAddr))
                (= ((_ extract 16 16) ipv4.srcAddr) #b1)
                (= ((_ extract 21 21) ipv4.srcAddr)
                   ((_ extract 16 16) ipv4.srcAddr))
                a!2
                (not (and (= ipv4.dstAddr #x0a0a0000) a!3))
                a!5
                (= ((_ extract 31 16) ipv4.dstAddr) #x1414)
                (= ((_ extract 3 3) ipv4.srcAddr) #b0)
                (= ((_ extract 8 8) ipv4.srcAddr) #b1)
                (= ((_ extract 11 11) ipv4.srcAddr) #b0)
                (= ((_ extract 21 21) ipv4.srcAddr) #b1)
                (= ((_ extract 24 24) ipv4.srcAddr) #b0)
                (= ((_ extract 27 27) ipv4.srcAddr) #b0)))
      (a!8 (and (= ethernet.eth_type #x0800)
                (= ((_ extract 0 0) ipv4.srcAddr) #b0)
                (= ((_ extract 11 11) ipv4.srcAddr)
                   ((_ extract 0 0) ipv4.srcAddr))
                (= ((_ extract 3 3) ipv4.srcAddr)
                   ((_ extract 0 0) ipv4.srcAddr))
                (= ((_ extract 16 16) ipv4.srcAddr) #b1)
                (= ((_ extract 21 21) ipv4.srcAddr)
                   ((_ extract 16 16) ipv4.srcAddr))
                a!2
                (not (and (= ipv4.dstAddr #x0a0a0000) a!3))
                a!5
                a!7
                (= ((_ extract 31 24) ipv4.dstAddr) #x0a)
                a!3)))
  (ite (and (= ethernet.eth_type #x0800)
            (= ((_ extract 0 0) ipv4.srcAddr) #b0)
            (= ((_ extract 11 11) ipv4.srcAddr) ((_ extract 0 0) ipv4.srcAddr))
            (= ((_ extract 3 3) ipv4.srcAddr) ((_ extract 0 0) ipv4.srcAddr))
            (= ((_ extract 16 16) ipv4.srcAddr) #b1)
            (= ((_ extract 21 21) ipv4.srcAddr)
               ((_ extract 16 16) ipv4.srcAddr))
            a!2
            (= ipv4.dstAddr #x0a0a0000)
            a!3)
       (ite a!4
            #x000000000000
            (ite a!6 #x160000000016 (ite a!8 #x00000000000a ethernet.dstAddr)))
       (ite a!4
            (ite a!6 #x160000000016 (ite a!8 #x00000000000a ethernet.dstAddr))
            (ite a!6
                 (ite a!8 #x00000000000a ethernet.dstAddr)
                 (ite a!8 ethernet.dstAddr ethernet.srcAddr)))))))
(egress) ipv4.$extracted$: (= ethernet.eth_type #x0800)
(egress) ipv4.$valid$: (= ethernet.eth_type #x0800)
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
(egress) ipv4.ttl: (let ((a!1 (and (= ((_ extract 8 8) ipv4.srcAddr) #b1)
                (= ((_ extract 24 24) ipv4.srcAddr) #b0)
                (= ((_ extract 27 27) ipv4.srcAddr) #b0)))
      (a!3 (not (and (= ethernet.eth_type #x0800)
                     (= ((_ extract 0 0) ipv4.srcAddr) #b0)
                     (= ((_ extract 3 3) ipv4.srcAddr) #b0)
                     (= ((_ extract 8 8) ipv4.srcAddr) #b1)
                     (= ((_ extract 11 11) ipv4.srcAddr) #b0)
                     (= ((_ extract 16 16) ipv4.srcAddr) #b1)
                     (= ((_ extract 21 21) ipv4.srcAddr) #b1)
                     (= ((_ extract 24 24) ipv4.srcAddr) #b0)
                     (= ((_ extract 27 27) ipv4.srcAddr) #b0))))
      (a!7 (not (and (= ((_ extract 31 16) ipv4.dstAddr) #x1414)
                     (= ethernet.eth_type #x0800)
                     (= ((_ extract 0 0) ipv4.srcAddr) #b0)
                     (= ((_ extract 3 3) ipv4.srcAddr) #b0)
                     (= ((_ extract 8 8) ipv4.srcAddr) #b1)
                     (= ((_ extract 11 11) ipv4.srcAddr) #b0)
                     (= ((_ extract 16 16) ipv4.srcAddr) #b1)
                     (= ((_ extract 21 21) ipv4.srcAddr) #b1)
                     (= ((_ extract 24 24) ipv4.srcAddr) #b0)
                     (= ((_ extract 27 27) ipv4.srcAddr) #b0)))))
(let ((a!2 (or a!1
               (and (not a!1)
                    (= ((_ extract 8 8) ipv4.srcAddr) #b0)
                    (= ((_ extract 24 24) ipv4.srcAddr) #b1)
                    (= ((_ extract 29 29) ipv4.srcAddr) #b1))))
      (a!5 (not (and (= ((_ extract 31 16) ipv4.dstAddr) #x0a0a) a!3))))
(let ((a!4 (and (= ethernet.eth_type #x0800)
                (= ((_ extract 0 0) ipv4.srcAddr) #b0)
                (= ((_ extract 11 11) ipv4.srcAddr)
                   ((_ extract 0 0) ipv4.srcAddr))
                (= ((_ extract 3 3) ipv4.srcAddr)
                   ((_ extract 0 0) ipv4.srcAddr))
                (= ((_ extract 16 16) ipv4.srcAddr) #b1)
                (= ((_ extract 21 21) ipv4.srcAddr)
                   ((_ extract 16 16) ipv4.srcAddr))
                a!2
                (not (and (= ipv4.dstAddr #x0a0a0000) a!3))
                (= ((_ extract 31 16) ipv4.dstAddr) #x0a0a)
                a!3))
      (a!6 (and (= ethernet.eth_type #x0800)
                (= ((_ extract 0 0) ipv4.srcAddr) #b0)
                (= ((_ extract 11 11) ipv4.srcAddr)
                   ((_ extract 0 0) ipv4.srcAddr))
                (= ((_ extract 3 3) ipv4.srcAddr)
                   ((_ extract 0 0) ipv4.srcAddr))
                (= ((_ extract 16 16) ipv4.srcAddr) #b1)
                (= ((_ extract 21 21) ipv4.srcAddr)
                   ((_ extract 16 16) ipv4.srcAddr))
                a!2
                (not (and (= ipv4.dstAddr #x0a0a0000) a!3))
                a!5
                (= ((_ extract 31 16) ipv4.dstAddr) #x1414)
                (= ((_ extract 3 3) ipv4.srcAddr) #b0)
                (= ((_ extract 8 8) ipv4.srcAddr) #b1)
                (= ((_ extract 11 11) ipv4.srcAddr) #b0)
                (= ((_ extract 21 21) ipv4.srcAddr) #b1)
                (= ((_ extract 24 24) ipv4.srcAddr) #b0)
                (= ((_ extract 27 27) ipv4.srcAddr) #b0)))
      (a!8 (and (= ethernet.eth_type #x0800)
                (= ((_ extract 0 0) ipv4.srcAddr) #b0)
                (= ((_ extract 11 11) ipv4.srcAddr)
                   ((_ extract 0 0) ipv4.srcAddr))
                (= ((_ extract 3 3) ipv4.srcAddr)
                   ((_ extract 0 0) ipv4.srcAddr))
                (= ((_ extract 16 16) ipv4.srcAddr) #b1)
                (= ((_ extract 21 21) ipv4.srcAddr)
                   ((_ extract 16 16) ipv4.srcAddr))
                a!2
                (not (and (= ipv4.dstAddr #x0a0a0000) a!3))
                a!5
                a!7
                (= ((_ extract 31 24) ipv4.dstAddr) #x0a)
                a!3)))
(let ((a!9 (ite a!6
                (bvadd #xff (ite a!8 (bvadd #xff ipv4.ttl) ipv4.ttl))
                (ite a!8 (bvadd #xff ipv4.ttl) ipv4.ttl))))
  (ite (and (= ethernet.eth_type #x0800)
            (= ((_ extract 0 0) ipv4.srcAddr) #b0)
            (= ((_ extract 11 11) ipv4.srcAddr) ((_ extract 0 0) ipv4.srcAddr))
            (= ((_ extract 3 3) ipv4.srcAddr) ((_ extract 0 0) ipv4.srcAddr))
            (= ((_ extract 16 16) ipv4.srcAddr) #b1)
            (= ((_ extract 21 21) ipv4.srcAddr)
               ((_ extract 16 16) ipv4.srcAddr))
            a!2
            (= ipv4.dstAddr #x0a0a0000)
            a!3)
       (bvadd #xff (ite a!4 (bvadd #xff a!9) a!9))
       (ite a!4 (bvadd #xff a!9) a!9))))))
(egress) ipv4.version: ipv4.version
(egress) scalars.$extracted$: false
(egress) scalars.$valid$: false
(egress) scalars._padding_0: scalars._padding_0
(egress) scalars.local_metadata_t.vrf: (ite (and (= ethernet.eth_type #x0800)
          (= ((_ extract 0 0) ipv4.srcAddr) #b0)
          (= ((_ extract 3 3) ipv4.srcAddr) #b0)
          (= ((_ extract 8 8) ipv4.srcAddr) #b1)
          (= ((_ extract 11 11) ipv4.srcAddr) #b0)
          (= ((_ extract 16 16) ipv4.srcAddr) #b1)
          (= ((_ extract 21 21) ipv4.srcAddr) #b1)
          (= ((_ extract 24 24) ipv4.srcAddr) #b0)
          (= ((_ extract 27 27) ipv4.srcAddr) #b0))
     #b0000000001
     #b0000000000)
(egress) scalars.local_metadata_t.vrf_is_valid: (let ((a!1 (not (and (= #b0 #b0)
                     (= ((_ extract 0 0) ipv4.srcAddr) #b0)
                     (= ((_ extract 8 8) ipv4.srcAddr) #b1)
                     (= ((_ extract 0 0) ipv4.srcAddr) #b0)
                     (= #b1 #b1)
                     (= ((_ extract 16 16) ipv4.srcAddr) #b1)
                     (= ((_ extract 24 24) ipv4.srcAddr) #b0)
                     (= ((_ extract 27 27) ipv4.srcAddr) #b0)))))
(let ((a!2 (or (and (= #x0800 #x0800)
                    (= #b0 #b0)
                    (= ((_ extract 0 0) ipv4.srcAddr) #b0)
                    (= ((_ extract 8 8) ipv4.srcAddr) #b1)
                    (= ((_ extract 0 0) ipv4.srcAddr) #b0)
                    (= #b1 #b1)
                    (= ((_ extract 16 16) ipv4.srcAddr) #b1)
                    (= ((_ extract 24 24) ipv4.srcAddr) #b0)
                    (= ((_ extract 27 27) ipv4.srcAddr) #b0))
               (and (= #x0800 #x0800)
                    a!1
                    (= #b0 #b0)
                    (= ((_ extract 0 0) ipv4.srcAddr) #b0)
                    (= ((_ extract 8 8) ipv4.srcAddr) #b0)
                    (= ((_ extract 0 0) ipv4.srcAddr) #b0)
                    (= #b1 #b1)
                    (= ((_ extract 16 16) ipv4.srcAddr) #b1)
                    (= ((_ extract 24 24) ipv4.srcAddr) #b1)
                    (= ((_ extract 29 29) ipv4.srcAddr) #b1)))))
  (ite (and (= ethernet.eth_type #x0800)
            (= ((_ extract 0 0) ipv4.srcAddr) #b0)
            (= ((_ extract 11 11) ipv4.srcAddr) ((_ extract 0 0) ipv4.srcAddr))
            (= ((_ extract 3 3) ipv4.srcAddr) ((_ extract 0 0) ipv4.srcAddr))
            (= ((_ extract 16 16) ipv4.srcAddr) #b1)
            (= ((_ extract 21 21) ipv4.srcAddr)
               ((_ extract 16 16) ipv4.srcAddr))
            a!2)
       #b1
       #b0)))
(egress) standard_metadata.$extracted$: false
(egress) standard_metadata.$valid$: false
(egress) standard_metadata._padding: standard_metadata._padding
(egress) standard_metadata.checksum_error: #b0
(egress) standard_metadata.deq_qdepth: #b0000000000000000000
(egress) standard_metadata.deq_timedelta: #x00000000
(egress) standard_metadata.egress_global_timestamp: #x000000000000
(egress) standard_metadata.egress_port: (let ((a!1 (and (= ((_ extract 8 8) ipv4.srcAddr) #b1)
                (= ((_ extract 24 24) ipv4.srcAddr) #b0)
                (= ((_ extract 27 27) ipv4.srcAddr) #b0)))
      (a!3 (not (and (= ethernet.eth_type #x0800)
                     (= ((_ extract 0 0) ipv4.srcAddr) #b0)
                     (= ((_ extract 3 3) ipv4.srcAddr) #b0)
                     (= ((_ extract 8 8) ipv4.srcAddr) #b1)
                     (= ((_ extract 11 11) ipv4.srcAddr) #b0)
                     (= ((_ extract 16 16) ipv4.srcAddr) #b1)
                     (= ((_ extract 21 21) ipv4.srcAddr) #b1)
                     (= ((_ extract 24 24) ipv4.srcAddr) #b0)
                     (= ((_ extract 27 27) ipv4.srcAddr) #b0))))
      (a!5 (not (and (= ((_ extract 31 16) ipv4.dstAddr) #x1414)
                     (= ethernet.eth_type #x0800)
                     (= ((_ extract 0 0) ipv4.srcAddr) #b0)
                     (= ((_ extract 3 3) ipv4.srcAddr) #b0)
                     (= ((_ extract 8 8) ipv4.srcAddr) #b1)
                     (= ((_ extract 11 11) ipv4.srcAddr) #b0)
                     (= ((_ extract 16 16) ipv4.srcAddr) #b1)
                     (= ((_ extract 21 21) ipv4.srcAddr) #b1)
                     (= ((_ extract 24 24) ipv4.srcAddr) #b0)
                     (= ((_ extract 27 27) ipv4.srcAddr) #b0))))
      (a!7 (and (= ((_ extract 31 16) ipv4.dstAddr) #x1414)
                (= ((_ extract 8 8) ipv4.srcAddr) #b1)
                (= ((_ extract 24 24) ipv4.srcAddr) #b0)
                (= ((_ extract 27 27) ipv4.srcAddr) #b0))))
(let ((a!2 (or a!1
               (and (not a!1)
                    (= ((_ extract 8 8) ipv4.srcAddr) #b0)
                    (= ((_ extract 24 24) ipv4.srcAddr) #b1)
                    (= ((_ extract 29 29) ipv4.srcAddr) #b1))))
      (a!4 (not (and (= ((_ extract 31 16) ipv4.dstAddr) #x0a0a) a!3)))
      (a!6 (not (and (= ((_ extract 31 24) ipv4.dstAddr) #x0a) a!3)))
      (a!8 (or a!7
               (and (not a!7)
                    (= ((_ extract 31 24) ipv4.dstAddr) #x0a)
                    (not a!1)))))
(let ((a!9 (and a!4
                a!2
                (not (and (= ipv4.dstAddr #x0a0a0000) a!3))
                (= ethernet.eth_type #x0800)
                (= ((_ extract 0 0) ipv4.srcAddr) #b0)
                (= ((_ extract 3 3) ipv4.srcAddr)
                   ((_ extract 0 0) ipv4.srcAddr))
                (= ((_ extract 11 11) ipv4.srcAddr)
                   ((_ extract 0 0) ipv4.srcAddr))
                (= ((_ extract 16 16) ipv4.srcAddr) #b1)
                (= ((_ extract 21 21) ipv4.srcAddr)
                   ((_ extract 16 16) ipv4.srcAddr))
                a!8))
      (a!10 (and (= ethernet.eth_type #x0800)
                 (= ((_ extract 0 0) ipv4.srcAddr) #b0)
                 (= ((_ extract 11 11) ipv4.srcAddr)
                    ((_ extract 0 0) ipv4.srcAddr))
                 (= ((_ extract 3 3) ipv4.srcAddr)
                    ((_ extract 0 0) ipv4.srcAddr))
                 (= ((_ extract 16 16) ipv4.srcAddr) #b1)
                 (= ((_ extract 21 21) ipv4.srcAddr)
                    ((_ extract 16 16) ipv4.srcAddr))
                 a!2
                 (not (and (= ipv4.dstAddr #x0a0a0000) a!3))
                 (= ((_ extract 31 16) ipv4.dstAddr) #x0a0a)
                 a!3))
      (a!11 (and (= ethernet.eth_type #x0800)
                 (= ((_ extract 0 0) ipv4.srcAddr) #b0)
                 (= ((_ extract 11 11) ipv4.srcAddr)
                    ((_ extract 0 0) ipv4.srcAddr))
                 (= ((_ extract 3 3) ipv4.srcAddr)
                    ((_ extract 0 0) ipv4.srcAddr))
                 (= ((_ extract 16 16) ipv4.srcAddr) #b1)
                 (= ((_ extract 21 21) ipv4.srcAddr)
                    ((_ extract 16 16) ipv4.srcAddr))
                 a!2
                 (= ipv4.dstAddr #x0a0a0000)
                 a!3))
      (a!13 (and (= ethernet.eth_type #x0800)
                 (= ((_ extract 0 0) ipv4.srcAddr) #b0)
                 (= ((_ extract 11 11) ipv4.srcAddr)
                    ((_ extract 0 0) ipv4.srcAddr))
                 (= ((_ extract 3 3) ipv4.srcAddr)
                    ((_ extract 0 0) ipv4.srcAddr))
                 (= ((_ extract 16 16) ipv4.srcAddr) #b1)
                 (= ((_ extract 21 21) ipv4.srcAddr)
                    ((_ extract 16 16) ipv4.srcAddr))
                 a!2
                 (not (and (= ipv4.dstAddr #x0a0a0000) a!3))
                 a!4
                 a!5
                 a!6)))
(let ((a!12 (and (= ethernet.eth_type #x0800)
                 (= ((_ extract 0 0) ipv4.srcAddr) #b0)
                 (= ((_ extract 11 11) ipv4.srcAddr)
                    ((_ extract 0 0) ipv4.srcAddr))
                 (= ((_ extract 3 3) ipv4.srcAddr)
                    ((_ extract 0 0) ipv4.srcAddr))
                 (= ((_ extract 16 16) ipv4.srcAddr) #b1)
                 (= ((_ extract 21 21) ipv4.srcAddr)
                    ((_ extract 16 16) ipv4.srcAddr))
                 a!2
                 (not (and (= ipv4.dstAddr #x0a0a0000) a!3))
                 a!4
                 a!5
                 a!6
                 (not a!9)
                 (not a!10)
                 (not a!11)))
      (a!14 (ite a!11
                 #b000000001
                 (ite a!10
                      #b000000000
                      (ite a!9 #b000000001 (ite a!13 #b111111111 #b000000000))))))
  (ite a!12 standard_metadata.egress_port a!14)))))
(egress) standard_metadata.egress_rid: #x0000
(egress) standard_metadata.egress_spec: (let ((a!1 (and (= ((_ extract 8 8) ipv4.srcAddr) #b1)
                (= ((_ extract 24 24) ipv4.srcAddr) #b0)
                (= ((_ extract 27 27) ipv4.srcAddr) #b0)))
      (a!3 (not (and (= ethernet.eth_type #x0800)
                     (= ((_ extract 0 0) ipv4.srcAddr) #b0)
                     (= ((_ extract 3 3) ipv4.srcAddr) #b0)
                     (= ((_ extract 8 8) ipv4.srcAddr) #b1)
                     (= ((_ extract 11 11) ipv4.srcAddr) #b0)
                     (= ((_ extract 16 16) ipv4.srcAddr) #b1)
                     (= ((_ extract 21 21) ipv4.srcAddr) #b1)
                     (= ((_ extract 24 24) ipv4.srcAddr) #b0)
                     (= ((_ extract 27 27) ipv4.srcAddr) #b0))))
      (a!6 (and (= ((_ extract 31 16) ipv4.dstAddr) #x1414)
                (= ((_ extract 8 8) ipv4.srcAddr) #b1)
                (= ((_ extract 24 24) ipv4.srcAddr) #b0)
                (= ((_ extract 27 27) ipv4.srcAddr) #b0)))
      (a!9 (not (and (= ((_ extract 31 16) ipv4.dstAddr) #x1414)
                     (= ethernet.eth_type #x0800)
                     (= ((_ extract 0 0) ipv4.srcAddr) #b0)
                     (= ((_ extract 3 3) ipv4.srcAddr) #b0)
                     (= ((_ extract 8 8) ipv4.srcAddr) #b1)
                     (= ((_ extract 11 11) ipv4.srcAddr) #b0)
                     (= ((_ extract 16 16) ipv4.srcAddr) #b1)
                     (= ((_ extract 21 21) ipv4.srcAddr) #b1)
                     (= ((_ extract 24 24) ipv4.srcAddr) #b0)
                     (= ((_ extract 27 27) ipv4.srcAddr) #b0)))))
(let ((a!2 (or a!1
               (and (not a!1)
                    (= ((_ extract 8 8) ipv4.srcAddr) #b0)
                    (= ((_ extract 24 24) ipv4.srcAddr) #b1)
                    (= ((_ extract 29 29) ipv4.srcAddr) #b1))))
      (a!5 (not (and (= ((_ extract 31 16) ipv4.dstAddr) #x0a0a) a!3)))
      (a!7 (or a!6
               (and (not a!6)
                    (= ((_ extract 31 24) ipv4.dstAddr) #x0a)
                    (not a!1))))
      (a!10 (not (and (= ((_ extract 31 24) ipv4.dstAddr) #x0a) a!3))))
(let ((a!4 (and (= ethernet.eth_type #x0800)
                (= ((_ extract 0 0) ipv4.srcAddr) #b0)
                (= ((_ extract 11 11) ipv4.srcAddr)
                   ((_ extract 0 0) ipv4.srcAddr))
                (= ((_ extract 3 3) ipv4.srcAddr)
                   ((_ extract 0 0) ipv4.srcAddr))
                (= ((_ extract 16 16) ipv4.srcAddr) #b1)
                (= ((_ extract 21 21) ipv4.srcAddr)
                   ((_ extract 16 16) ipv4.srcAddr))
                a!2
                (not (and (= ipv4.dstAddr #x0a0a0000) a!3))
                (= ((_ extract 31 16) ipv4.dstAddr) #x0a0a)
                a!3))
      (a!8 (and a!5
                a!2
                (not (and (= ipv4.dstAddr #x0a0a0000) a!3))
                (= ethernet.eth_type #x0800)
                (= ((_ extract 0 0) ipv4.srcAddr) #b0)
                (= ((_ extract 3 3) ipv4.srcAddr)
                   ((_ extract 0 0) ipv4.srcAddr))
                (= ((_ extract 11 11) ipv4.srcAddr)
                   ((_ extract 0 0) ipv4.srcAddr))
                (= ((_ extract 16 16) ipv4.srcAddr) #b1)
                (= ((_ extract 21 21) ipv4.srcAddr)
                   ((_ extract 16 16) ipv4.srcAddr))
                a!7))
      (a!11 (and (= ethernet.eth_type #x0800)
                 (= ((_ extract 0 0) ipv4.srcAddr) #b0)
                 (= ((_ extract 11 11) ipv4.srcAddr)
                    ((_ extract 0 0) ipv4.srcAddr))
                 (= ((_ extract 3 3) ipv4.srcAddr)
                    ((_ extract 0 0) ipv4.srcAddr))
                 (= ((_ extract 16 16) ipv4.srcAddr) #b1)
                 (= ((_ extract 21 21) ipv4.srcAddr)
                    ((_ extract 16 16) ipv4.srcAddr))
                 a!2
                 (not (and (= ipv4.dstAddr #x0a0a0000) a!3))
                 a!5
                 a!9
                 a!10)))
  (ite (and (= ethernet.eth_type #x0800)
            (= ((_ extract 0 0) ipv4.srcAddr) #b0)
            (= ((_ extract 11 11) ipv4.srcAddr) ((_ extract 0 0) ipv4.srcAddr))
            (= ((_ extract 3 3) ipv4.srcAddr) ((_ extract 0 0) ipv4.srcAddr))
            (= ((_ extract 16 16) ipv4.srcAddr) #b1)
            (= ((_ extract 21 21) ipv4.srcAddr)
               ((_ extract 16 16) ipv4.srcAddr))
            a!2
            (= ipv4.dstAddr #x0a0a0000)
            a!3)
       #b000000001
       (ite a!4
            #b000000000
            (ite a!8 #b000000001 (ite a!11 #b111111111 #b000000000)))))))
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
(declare-fun ipv4.srcAddr () (_ BitVec 32))
(declare-fun ethernet.eth_type () (_ BitVec 16))
(declare-fun ipv4.dstAddr () (_ BitVec 32))
(assert
 (let (($x110 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x110)))
(assert
 (let (($x139 (= ((_ extract 27 27) ipv4.srcAddr) (_ bv0 1))))
 (let ((?x69 ((_ extract 24 24) ipv4.srcAddr)))
 (let (($x138 (= ?x69 (_ bv0 1))))
 (let ((?x71 ((_ extract 21 21) ipv4.srcAddr)))
 (let (($x137 (= ?x71 (_ bv1 1))))
 (let ((?x73 ((_ extract 16 16) ipv4.srcAddr)))
 (let (($x136 (= ?x73 (_ bv1 1))))
 (let ((?x75 ((_ extract 11 11) ipv4.srcAddr)))
 (let (($x135 (= ?x75 (_ bv0 1))))
 (let ((?x77 ((_ extract 8 8) ipv4.srcAddr)))
 (let (($x134 (= ?x77 (_ bv1 1))))
 (let ((?x79 ((_ extract 3 3) ipv4.srcAddr)))
 (let (($x132 (= ?x79 (_ bv0 1))))
 (let ((?x81 ((_ extract 0 0) ipv4.srcAddr)))
 (let (($x131 (= ?x81 (_ bv0 1))))
 (let (($x32 (= ethernet.eth_type (_ bv2048 16))))
 (let (($x141 (and $x32 $x131 $x132 $x134 $x135 $x136 $x137 $x138 $x139)))
 (let (($x102 (not $x141)))
 (let ((?x124 ((_ extract 31 24) ipv4.dstAddr)))
 (let (($x158 (= ?x124 (_ bv10 8))))
 (let (($x165 (not (and $x158 $x102))))
 (let ((?x116 ((_ extract 31 16) ipv4.dstAddr)))
 (let (($x156 (= ?x116 (_ bv5140 16))))
 (let (($x160 (not (and $x156 $x32 $x131 $x132 $x134 $x135 $x136 $x137 $x138 $x139))))
 (let (($x68 (not (and (= ?x116 (_ bv2570 16)) $x102))))
 (let (($x106 (not (and (= ipv4.dstAddr (_ bv168427520 32)) $x102))))
 (let (($x149 (= ((_ extract 29 29) ipv4.srcAddr) (_ bv1 1))))
 (let (($x148 (= ?x69 (_ bv1 1))))
 (let (($x147 (= ?x77 (_ bv0 1))))
 (let (($x114 (and $x134 $x138 $x139)))
 (let (($x105 (not $x114)))
 (let (($x95 (or $x114 (and $x105 $x147 $x148 $x149))))
 (let (($x88 (= ?x71 ?x73)))
 (let (($x67 (= ?x79 ?x81)))
 (let (($x107 (= ?x75 ?x81)))
 (let (($x162 (and $x32 $x131 $x107 $x67 $x136 $x88 $x95 $x106 $x68 $x160 $x165)))
 (let (($x185 (and $x156 $x134 $x138 $x139)))
 (let (($x203 (and $x68 $x95 $x106 $x32 $x131 $x67 $x107 $x136 $x88 (or $x185 (and (not $x185) $x158 $x105)))))
 (let (($x98 (= ?x116 (_ bv2570 16))))
 (let (($x57 (and $x32 $x131 $x107 $x67 $x136 $x88 $x95 $x106 $x98 $x102)))
 (let (($x89 (= ipv4.dstAddr (_ bv168427520 32))))
 (let (($x140 (and $x32 $x131 $x107 $x67 $x136 $x88 $x95 $x89 $x102)))
 (let ((?x192 (ite $x140 (_ bv1 9) (ite $x57 (_ bv0 9) (ite $x203 (_ bv1 9) (ite $x162 (_ bv511 9) (_ bv0 9)))))))
 (let (($x210 (or (or false (= ?x192 (_ bv0 9))) (= ?x192 (_ bv1 9)))))
 (let (($x29 (= ?x192 (_ bv511 9))))
 (or $x29 $x210)))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
