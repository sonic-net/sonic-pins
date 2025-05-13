(ingress) $got_cloned$: false
(ingress) $got_recirculated$: false
(ingress) h1.$extracted$: false
(ingress) h1.$valid$: true
(ingress) h1.f1: h1.f1
(ingress) h1.f2: h1.f2
(ingress) h1.f3: h1.f3
(ingress) h1.f4: h1.f4
(ingress) h1.f5: h1.f5
(ingress) h1.f6: h1.f6
(ingress) h1.f7: h1.f7
(ingress) h1.f8: h1.f8
(ingress) h1.fr: h1.fr
(ingress) h1.fw: h1.fw
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
(parsed) h1.$extracted$: true
(parsed) h1.$valid$: true
(parsed) h1.f1: h1.f1
(parsed) h1.f2: h1.f2
(parsed) h1.f3: h1.f3
(parsed) h1.f4: h1.f4
(parsed) h1.f5: h1.f5
(parsed) h1.f6: h1.f6
(parsed) h1.f7: h1.f7
(parsed) h1.f8: h1.f8
(parsed) h1.fr: h1.fr
(parsed) h1.fw: h1.fw
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
(egress) h1.$extracted$: true
(egress) h1.$valid$: true
(egress) h1.f1: h1.f1
(egress) h1.f2: h1.f2
(egress) h1.f3: h1.f3
(egress) h1.f4: h1.f4
(egress) h1.f5: h1.f5
(egress) h1.f6: h1.f6
(egress) h1.f7: h1.f7
(egress) h1.f8: h1.f8
(egress) h1.fr: h1.fr
(egress) h1.fw: (let ((a!1 (and (not (= h1.f2 #x00)) (= h1.f3 #x00) (= h1.f4 #x00)))
      (a!2 (or (and (not (= h1.f3 #x00)) (not (= h1.f4 #x00)))
               (and (= h1.f3 #x00) (= h1.f4 #x00))))
      (a!5 (or (and (not (= h1.f3 #x00)) (= h1.f4 #x00))
               (and (= h1.f3 #x00) (not (= h1.f4 #x00))))))
(let ((a!3 (and (not false) (= #xff #xff) (or a!1 (and (= h1.f2 #x00) a!2))))
      (a!6 (or a!1
               (and (= h1.f2 #x00) (not (= h1.f3 #x00)) (not (= h1.f4 #x00)))))
      (a!7 (ite (and (= h1.f1 #x00) (= h1.f2 h1.f1) (= h1.fr #xff) a!5)
                #x02
                (ite (and (= h1.f1 #x00)
                          (= h1.f2 #x00)
                          (= h1.f3 #x00)
                          (= h1.f4 #x00)
                          (= h1.fr #xff))
                     #x01
                     h1.fw))))
(let ((a!4 (or (and (not false)
                    (not (= h1.f2 #x00))
                    (not (= h1.f3 #x00))
                    (not (= h1.f4 #x00))
                    (= #xff #xff))
               a!3))
      (a!8 (ite (and (not (= h1.f2 #x00)) (= h1.f1 #x00) (= h1.fr #xff) a!5)
                #x02
                (ite (and (= h1.f1 #x00) (= h1.fr #xff) a!6) #x01 a!7))))
(let ((a!9 (ite (and (= h1.f1 #x00)
                     (not (= h1.f2 #x00))
                     (not (= h1.f3 #x00))
                     (not (= h1.f4 #x00))
                     (= h1.fr #xff))
                #x01
                a!8)))
  (ite (and (not (= h1.f1 #x00)) (= h1.fr #xff) a!4) #x03 a!9)))))
(egress) scalars.$extracted$: false
(egress) scalars.$valid$: false
(egress) standard_metadata.$extracted$: false
(egress) standard_metadata.$valid$: false
(egress) standard_metadata._padding: standard_metadata._padding
(egress) standard_metadata.checksum_error: #b0
(egress) standard_metadata.deq_qdepth: #b0000000000000000000
(egress) standard_metadata.deq_timedelta: #x00000000
(egress) standard_metadata.egress_global_timestamp: #x000000000000
(egress) standard_metadata.egress_port: #b000000000
(egress) standard_metadata.egress_rid: #x0000
(egress) standard_metadata.egress_spec: #b000000000
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
(assert
 (let (($x133 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x133)))
(assert
 (let (($x134 (or (or false (= (_ bv0 9) (_ bv0 9))) (= (_ bv0 9) (_ bv1 9)))))
 (let (($x20 (= (_ bv0 9) (_ bv511 9))))
 (or $x20 $x134))))
(check-sat)
