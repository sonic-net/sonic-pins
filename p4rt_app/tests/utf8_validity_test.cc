// Copyright 2025 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include <string>
#include <vector>

#include "absl/status/status.h"
#include "gmock/gmock.h"
#include "grpcpp/support/status.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status_matchers.h"
#include "p4_infra/p4_pdpi/pd.h"
#include "p4_infra/p4_runtime/p4_runtime_session.h"
#include "p4_infra/string_encodings/hex_string.h"
#include "p4rt_app/tests/lib/p4runtime_component_test_fixture.h"
#include "p4rt_app/tests/lib/p4runtime_request_helpers.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"

namespace p4rt_app {
namespace {

using ::gutil::StatusIs;
using ::testing::HasSubstr;

class Utf8ValidityTest : public test_lib::P4RuntimeComponentTestFixture {
 protected:
  Utf8ValidityTest()
      : test_lib::P4RuntimeComponentTestFixture(sai::Instantiation::kTor) {}
};

TEST_F(Utf8ValidityTest, NonUtf8StringFailsInRouterInterfaceTable) {
  ASSERT_OK(p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet0", "1"));
  ASSERT_OK_AND_ASSIGN(
      p4::v1::WriteRequest request,
      test_lib::PdWriteRequestToPi(
          R"pb(
            updates {
              type: INSERT
              table_entry {
                router_interface_table_entry {
                  match { router_interface_id: "\x01\x33\x00\x80" }
                  action {
                    set_port_and_src_mac {
                      port: "1"
                      src_mac: "02:2a:10:00:00:03"
                    }
                  }
                }
              }
            }
          )pb",
          ir_p4_info_));
  EXPECT_THAT(
      p4_runtime::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                   request),
      StatusIs(absl::StatusCode::kUnknown, AllOf(HasSubstr("INVALID_ARGUMENT"),
                                                 HasSubstr("Invalid UTF-8"))));
}
TEST_F(Utf8ValidityTest, NonUtf8StringFailsInNextHopTable) {
  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest request,
                       test_lib::PdWriteRequestToPi(
                           R"pb(
                             updates {
                               type: INSERT
                               table_entry {
                                 nexthop_table_entry {
                                   match { nexthop_id: "\x01\x33\x00\xF2" }
                                   action {
                                     set_ip_nexthop {
                                       router_interface_id: "8"
                                       neighbor_id: "fe80::21a:11ff:fe17:5f80"
                                     }
                                   }
                                 }
                               }
                             }
                           )pb",
                           ir_p4_info_));
  EXPECT_THAT(
      p4_runtime::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                   request),
      StatusIs(absl::StatusCode::kUnknown, AllOf(HasSubstr("INVALID_ARGUMENT"),
                                                 HasSubstr("Invalid UTF-8"))));
}

TEST_F(Utf8ValidityTest, NonUtf8StringFailsInTunnelTable) {
  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest request,
                       test_lib::PdWriteRequestToPi(
                           R"pb(
                             updates {
                               type: INSERT
                               table_entry {
                                 tunnel_table_entry {
                                   match { tunnel_id: "\x01\x33\x00\xFF" }
                                   action {
                                     mark_for_p2p_tunnel_encap {
                                       encap_src_ip: "2002:a17:506:c114::1"
                                       encap_dst_ip: "2002:a17:506:c114::2"
                                       router_interface_id: "1"
                                     }
                                   }
                                 }
                               }
                             }
                           )pb",
                           ir_p4_info_));
  EXPECT_THAT(
      p4_runtime::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                   request),
      StatusIs(absl::StatusCode::kUnknown, AllOf(HasSubstr("INVALID_ARGUMENT"),
                                                 HasSubstr("Invalid UTF-8"))));
}

TEST_F(Utf8ValidityTest, NonUtf8StringFailsInMirrorTable) {
  ASSERT_OK_AND_ASSIGN(
      p4::v1::WriteRequest request,
      test_lib::PdWriteRequestToPi(
          R"pb(
            updates {
              type: INSERT
              table_entry {
                mirror_session_table_entry {
                  match { mirror_session_id: "\x01\x33\x00\xFF" }
                  action {
                    mirror_with_vlan_tag_and_ipfix_encapsulation {
                      monitor_port: "1"
                      monitor_failover_port: "2"
                      mirror_encap_dst_ip: "2002:a17:506:c114::2"
                      mirror_encap_src_ip: "2002:a17:506:d114::3"
                      mirror_encap_src_mac: "00:01:02:03:04:05"
                      mirror_encap_vlan_id: "0x001"
                      mirror_encap_dst_mac: "01:02:03:04:05:06"
                      mirror_encap_udp_dst_port: "0x1234"
                      mirror_encap_udp_src_port: "0x2472"
                    }
                  }
                }
              }
            }
          )pb",
          ir_p4_info_));

  EXPECT_THAT(
      p4_runtime::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                   request),
      StatusIs(absl::StatusCode::kUnknown, AllOf(HasSubstr("INVALID_ARGUMENT"),
                                                 HasSubstr("Invalid UTF-8"))));
}

TEST_F(Utf8ValidityTest, NonUtf8StringFailsInWcmpGroupTable) {
  ASSERT_OK_AND_ASSIGN(
      p4::v1::WriteRequest request,
      test_lib::PdWriteRequestToPi(
          R"pb(
            updates {
              type: INSERT
              table_entry {
                wcmp_group_table_entry {
                  match { wcmp_group_id: "\x01\x33\x00\xF0" }
                  wcmp_actions {
                    action { set_nexthop_id { nexthop_id: "nexthop-1" } }
                    weight: 1
                    watch_port: "2"
                  }
                }
              }
            }
          )pb",
          ir_p4_info_));
  EXPECT_THAT(
      p4_runtime::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                   request),
      StatusIs(absl::StatusCode::kUnknown, AllOf(HasSubstr("INVALID_ARGUMENT"),
                                                 HasSubstr("Invalid UTF-8"))));
}

TEST_F(Utf8ValidityTest, NonUtf8StringFailsInWatchPort) {
  ASSERT_OK_AND_ASSIGN(
      p4::v1::WriteRequest request,
      test_lib::PdWriteRequestToPi(
          R"pb(
            updates {
              type: INSERT
              table_entry {
                wcmp_group_table_entry {
                  match { wcmp_group_id: "group-1" }
                  wcmp_actions {
                    action { set_nexthop_id { nexthop_id: "nexthop-1" } }
                    weight: 1
                    watch_port: "\x01\x33\x00\xF5"
                  }
                }
              }
            }
          )pb",
          ir_p4_info_));
  EXPECT_THAT(
      p4_runtime::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                   request),
      StatusIs(absl::StatusCode::kUnknown, AllOf(HasSubstr("INVALID_ARGUMENT"),
                                                 HasSubstr("Invalid UTF-8"))));
}

TEST_F(Utf8ValidityTest, NonUtf8StringFailsInVrfTable) {
  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest request,
                       test_lib::IrWriteRequestToPi(
                           R"pb(
                             updates {
                               type: INSERT
                               entity {
                                 table_entry {
                                   table_name: "vrf_table"
                                   matches {
                                     name: "vrf_id"
                                     exact { str: "\x01\x33\x00\xF1" }
                                   }
                                   action { name: "no_action" }
                                 }
                               }
                             })pb",
                           ir_p4_info_));
  EXPECT_THAT(
      p4_runtime::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                   request),
      StatusIs(absl::StatusCode::kUnknown, AllOf(HasSubstr("INVALID_ARGUMENT"),
                                                 HasSubstr("Invalid UTF-8"))));
}

TEST_F(Utf8ValidityTest, NonUtf8StringFailsInQosQueue) {
  ASSERT_OK_AND_ASSIGN(
      p4::v1::WriteRequest request,
      test_lib::PdWriteRequestToPi(
          R"pb(
            updates {
              type: INSERT
              table_entry {
                acl_ingress_table_entry {
                  match { is_ip { value: "0x1" } }
                  priority: 10
                  action { acl_copy { qos_queue: "\x01\x33\x00\x89" } }
                }
              }
            }
          )pb",
          ir_p4_info_));
  EXPECT_THAT(
      p4_runtime::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                   request),
      StatusIs(absl::StatusCode::kUnknown, AllOf(HasSubstr("INVALID_ARGUMENT"),
                                                 HasSubstr("Invalid UTF-8"))));
}

TEST_F(Utf8ValidityTest, NonUtf8StringFailsInMulticastQueue) {
  ASSERT_OK_AND_ASSIGN(
      p4::v1::WriteRequest request,
      test_lib::PdWriteRequestToPi(
          R"pb(
            updates {
              type: INSERT
              table_entry {
                acl_ingress_qos_table_entry {
                  match { is_ip { value: "0x1" } }
                  priority: 10
                  action {
                    set_forwarding_queues {
                      green_multicast_queue: "1"
                      green_unicast_queue: "2"
                      red_unicast_queue: "3"
                      red_multicast_queue: "\x01\x33\x00\x89"
                    }
                  }
                  meter_config { bytes_per_second: 123 burst_bytes: 345 }
                }
              }
            }
          )pb",
          ir_p4_info_));
  EXPECT_THAT(
      p4_runtime::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                   request),
      StatusIs(absl::StatusCode::kUnknown, AllOf(HasSubstr("INVALID_ARGUMENT"),
                                                 HasSubstr("Invalid UTF-8"))));
}

TEST_F(Utf8ValidityTest, NonUtf8StringFailsInReplicaPort) {
  ASSERT_OK(
      p4rt_service_.GetP4rtServer().AddPortTranslation("\x01\x33\x80", "1"));
  ASSERT_OK_AND_ASSIGN(
      p4::v1::WriteRequest request,
      test_lib::IrWriteRequestToPi(
          R"pb(
            updates {
              type: INSERT
              entity {
                packet_replication_engine_entry {
                  multicast_group_entry {
                    multicast_group_id: 17
                    replicas { port: "\x01\x33\x80" instance: 1 }
                  }
                }
              }
            })pb",
          ir_p4_info_));

  EXPECT_THAT(
      p4_runtime::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                   request),
      StatusIs(absl::StatusCode::kUnknown, AllOf(HasSubstr("INVALID_ARGUMENT"),
                                                 HasSubstr("Invalid UTF-8"))));
}

TEST_F(Utf8ValidityTest, NonUtf8StringFailsInPacketOut) {
  ASSERT_OK(
      p4rt_service_.GetP4rtServer().AddPortTranslation("\x01\x33\x89", "1"));
  sai::PacketOut packet_out;
  packet_out.set_payload(std::string("test packet"));
  sai::PacketOut::Metadata& metadata = *packet_out.mutable_metadata();
  metadata.set_egress_port("\x01\x33\x89");
  metadata.set_submit_to_ingress(string_encodings::BitsetToHexString<1>(0));

  p4::v1::StreamMessageRequest request;
  ASSERT_OK_AND_ASSIGN(*request.mutable_packet(),
                       pdpi::PdPacketOutToPi(ir_p4_info_, packet_out));
  EXPECT_TRUE(p4rt_session_->StreamChannelWrite(request));
  ASSERT_OK_AND_ASSIGN(
      std::vector<p4::v1::StreamMessageResponse> actual_responses,
      p4rt_session_->ReadStreamChannelResponsesAndFinish());
  EXPECT_EQ(actual_responses[0].error().canonical_code(),
            grpc::StatusCode::INVALID_ARGUMENT);
}

}  // namespace
}  // namespace p4rt_app
