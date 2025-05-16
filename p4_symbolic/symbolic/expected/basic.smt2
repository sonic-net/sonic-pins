(ingress) $got_cloned$: false
(ingress) $got_recirculated$: false
(ingress) ethernet.$extracted$: false
(ingress) ethernet.$valid$: true
(ingress) ethernet.dstAddr: ethernet.dstAddr
(ingress) ethernet.etherType: ethernet.etherType
(ingress) ethernet.srcAddr: ethernet.srcAddr
(ingress) ipv4.$extracted$: false
(ingress) ipv4.$valid$: (= ethernet.etherType #x0800)
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
(parsed) ipv4.$extracted$: (= ethernet.etherType #x0800)
(parsed) ipv4.$valid$: (= ethernet.etherType #x0800)
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
(parsed) standard_metadata.parser_error: #x00000000
(parsed) standard_metadata.priority: #b000

(egress) $got_cloned$: false
(egress) $got_recirculated$: false
(egress) ethernet.$extracted$: true
(egress) ethernet.$valid$: true
(egress) ethernet.dstAddr: (let ((a!1 (or (and (= #x0800 #x0800) (= ipv4.dstAddr #x0a0a0000))
               (and (= #x0800 #x0800)
                    (not (= ipv4.dstAddr #x0a0a0000))
                    (= ((_ extract 31 16) ipv4.dstAddr) #x0a0a))))
      (a!2 (and (= ethernet.etherType #x0800)
                (not (= ipv4.dstAddr #x0a0a0000))
                (not (= ((_ extract 31 16) ipv4.dstAddr) #x0a0a))
                (= ((_ extract 31 16) ipv4.dstAddr) #x1414)))
      (a!3 (and (= ethernet.etherType #x0800)
                (not (= ipv4.dstAddr #x0a0a0000))
                (not (= ((_ extract 31 16) ipv4.dstAddr) #x0a0a))
                (not (= ((_ extract 31 16) ipv4.dstAddr) #x1414))
                (= ((_ extract 31 24) ipv4.dstAddr) #x0a))))
  (ite (and (= ethernet.etherType #x0800) a!1)
       #x000000000000
       (ite a!2 #x160000000016 (ite a!3 #x00000000000a ethernet.dstAddr))))
(egress) ethernet.etherType: ethernet.etherType
(egress) ethernet.srcAddr: (let ((a!1 (and (= ethernet.etherType #x0800)
                (not (= ipv4.dstAddr #x0a0a0000))
                (= ((_ extract 31 16) ipv4.dstAddr) #x0a0a)))
      (a!2 (and (= ethernet.etherType #x0800)
                (not (= ipv4.dstAddr #x0a0a0000))
                (not (= ((_ extract 31 16) ipv4.dstAddr) #x0a0a))
                (= ((_ extract 31 16) ipv4.dstAddr) #x1414)))
      (a!3 (and (= ethernet.etherType #x0800)
                (not (= ipv4.dstAddr #x0a0a0000))
                (not (= ((_ extract 31 16) ipv4.dstAddr) #x0a0a))
                (not (= ((_ extract 31 16) ipv4.dstAddr) #x1414))
                (= ((_ extract 31 24) ipv4.dstAddr) #x0a))))
  (ite (and (= ethernet.etherType #x0800) (= ipv4.dstAddr #x0a0a0000))
       (ite a!1
            #x000000000000
            (ite a!2 #x160000000016 (ite a!3 #x00000000000a ethernet.dstAddr)))
       (ite a!1
            (ite a!2 #x160000000016 (ite a!3 #x00000000000a ethernet.dstAddr))
            (ite a!2
                 (ite a!3 #x00000000000a ethernet.dstAddr)
                 (ite a!3 ethernet.dstAddr ethernet.srcAddr)))))
(egress) ipv4.$extracted$: (= ethernet.etherType #x0800)
(egress) ipv4.$valid$: (= ethernet.etherType #x0800)
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
(egress) ipv4.ttl: (let ((a!1 (and (= ethernet.etherType #x0800)
                (not (= ipv4.dstAddr #x0a0a0000))
                (not (= ((_ extract 31 16) ipv4.dstAddr) #x0a0a))
                (= ((_ extract 31 16) ipv4.dstAddr) #x1414)))
      (a!2 (and (= ethernet.etherType #x0800)
                (not (= ipv4.dstAddr #x0a0a0000))
                (not (= ((_ extract 31 16) ipv4.dstAddr) #x0a0a))
                (not (= ((_ extract 31 16) ipv4.dstAddr) #x1414))
                (= ((_ extract 31 24) ipv4.dstAddr) #x0a))))
(let ((a!3 (ite a!1
                (bvadd #xff (ite a!2 (bvadd #xff ipv4.ttl) ipv4.ttl))
                (ite a!2 (bvadd #xff ipv4.ttl) ipv4.ttl))))
(let ((a!4 (ite (and (= ethernet.etherType #x0800)
                     (not (= ipv4.dstAddr #x0a0a0000))
                     (= ((_ extract 31 16) ipv4.dstAddr) #x0a0a))
                (bvadd #xff a!3)
                a!3)))
  (ite (and (= ethernet.etherType #x0800) (= ipv4.dstAddr #x0a0a0000))
       (bvadd #xff a!4)
       a!4))))
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
(egress) standard_metadata.egress_port: (let ((a!1 (and (not (= ((_ extract 31 16) ipv4.dstAddr) #x1414))
                (= ((_ extract 31 24) ipv4.dstAddr) #x0a)))
      (a!3 (and (= ethernet.etherType #x0800)
                (not (= ipv4.dstAddr #x0a0a0000))
                (= ((_ extract 31 16) ipv4.dstAddr) #x0a0a)))
      (a!5 (and (= ethernet.etherType #x0800)
                (not (= ipv4.dstAddr #x0a0a0000))
                (not (= ((_ extract 31 16) ipv4.dstAddr) #x0a0a))
                (not (= ((_ extract 31 16) ipv4.dstAddr) #x1414))
                (not (= ((_ extract 31 24) ipv4.dstAddr) #x0a)))))
(let ((a!2 (and (not (= ((_ extract 31 16) ipv4.dstAddr) #x0a0a))
                (not (= ipv4.dstAddr #x0a0a0000))
                (= ethernet.etherType #x0800)
                (or (= ((_ extract 31 16) ipv4.dstAddr) #x1414) a!1))))
(let ((a!4 (and (= ethernet.etherType #x0800)
                (not (= ipv4.dstAddr #x0a0a0000))
                (not (= ((_ extract 31 16) ipv4.dstAddr) #x0a0a))
                (not (= ((_ extract 31 16) ipv4.dstAddr) #x1414))
                (not (= ((_ extract 31 24) ipv4.dstAddr) #x0a))
                (not a!2)
                (not a!3)
                (not (and (= ethernet.etherType #x0800)
                          (= ipv4.dstAddr #x0a0a0000)))))
      (a!6 (ite (and (= ethernet.etherType #x0800) (= ipv4.dstAddr #x0a0a0000))
                #b000000001
                (ite a!3
                     #b000000000
                     (ite a!2 #b000000001 (ite a!5 #b111111111 #b000000000))))))
  (ite a!4 standard_metadata.egress_port a!6))))
(egress) standard_metadata.egress_rid: #x0000
(egress) standard_metadata.egress_spec: (let ((a!1 (and (not (= ((_ extract 31 16) ipv4.dstAddr) #x1414))
                (= ((_ extract 31 24) ipv4.dstAddr) #x0a)))
      (a!3 (and (= ethernet.etherType #x0800)
                (not (= ipv4.dstAddr #x0a0a0000))
                (not (= ((_ extract 31 16) ipv4.dstAddr) #x0a0a))
                (not (= ((_ extract 31 16) ipv4.dstAddr) #x1414))
                (not (= ((_ extract 31 24) ipv4.dstAddr) #x0a)))))
(let ((a!2 (and (not (= ((_ extract 31 16) ipv4.dstAddr) #x0a0a))
                (not (= ipv4.dstAddr #x0a0a0000))
                (= ethernet.etherType #x0800)
                (or (= ((_ extract 31 16) ipv4.dstAddr) #x1414) a!1))))
(let ((a!4 (ite (and (= ethernet.etherType #x0800)
                     (not (= ipv4.dstAddr #x0a0a0000))
                     (= ((_ extract 31 16) ipv4.dstAddr) #x0a0a))
                #b000000000
                (ite a!2 #b000000001 (ite a!3 #b111111111 #b000000000)))))
  (ite (and (= ethernet.etherType #x0800) (= ipv4.dstAddr #x0a0a0000))
       #b000000001
       a!4))))
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
(declare-fun ipv4.dstAddr () (_ BitVec 32))
(declare-fun ethernet.etherType () (_ BitVec 16))
(assert
 (let (($x107 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x107)))
(assert
 (let ((?x48 ((_ extract 31 24) ipv4.dstAddr)))
 (let (($x67 (= ?x48 (_ bv10 8))))
 (let (($x72 (not $x67)))
 (let ((?x6 ((_ extract 31 16) ipv4.dstAddr)))
 (let (($x65 (= ?x6 (_ bv5140 16))))
 (let (($x68 (not $x65)))
 (let (($x59 (= ?x6 (_ bv2570 16))))
 (let (($x63 (not $x59)))
 (let (($x24 (= ipv4.dstAddr (_ bv168427520 32))))
 (let (($x55 (not $x24)))
 (let (($x29 (= ethernet.etherType (_ bv2048 16))))
 (let (($x64 (and $x29 $x55 $x63 $x68 $x72)))
 (let (($x100 (and $x63 $x55 $x29 (or $x65 (and $x68 $x67)))))
 (let (($x60 (and $x29 $x55 $x59)))
 (let (($x53 (and $x29 $x24)))
 (let ((?x94 (ite $x53 (_ bv1 9) (ite $x60 (_ bv0 9) (ite $x100 (_ bv1 9) (ite $x64 (_ bv511 9) (_ bv0 9)))))))
 (let (($x121 (or (or false (= ?x94 (_ bv0 9))) (= ?x94 (_ bv1 9)))))
 (let (($x11 (= ?x94 (_ bv511 9))))
 (or $x11 $x121))))))))))))))))))))
(check-sat)
