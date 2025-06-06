// Copyright (c) 2024, Google Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "lib/basic_traffic/basic_traffic.h"

#include <functional>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/memory/memory.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "absl/strings/str_split.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "gmock/gmock.h"
#include "grpcpp/support/status.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto_matchers.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "p4_infra/packetlib/packetlib.h"
#include "p4_infra/packetlib/packetlib.pb.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "proto/gnmi/gnmi.pb.h"
#include "proto/gnmi/gnmi_mock.grpc.pb.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "thinkit/control_device.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/mock_control_device.h"
#include "thinkit/mock_generic_testbed.h"
#include "thinkit/mock_switch.h"
#include "thinkit/packet_generation_finalizer.h"
#include "thinkit/proto/generic_testbed.pb.h"

namespace pins_test::basic_traffic {
namespace {

using ::gutil::EqualsProto;
using ::testing::_;
using ::testing::ByMove;
using ::testing::DoAll;
using ::testing::Expectation;
using ::testing::ExpectationSet;
using ::testing::Field;
using ::testing::IsEmpty;
using ::testing::MockFunction;
using ::testing::Return;
using ::testing::ReturnRef;
using ::testing::SetArgPointee;
using ::testing::UnorderedElementsAre;

TEST(BasicTraffic, OneToOne) {
  EXPECT_THAT(
      OneToOne({"a", "b", "c"}, {"d", "e", "f"}),
      UnorderedElementsAre(
          InterfacePair{.ingress_interface = "a", .egress_interface = "d"},
          InterfacePair{.ingress_interface = "b", .egress_interface = "e"},
          InterfacePair{.ingress_interface = "c", .egress_interface = "f"}));

  EXPECT_THAT(
      OneToOne({"a", "b"}, {"d", "e", "f"}),
      UnorderedElementsAre(
          InterfacePair{.ingress_interface = "a", .egress_interface = "d"},
          InterfacePair{.ingress_interface = "b", .egress_interface = "e"}));

  EXPECT_THAT(OneToOne({"a", "b"}, {}), IsEmpty());
}

TEST(BasicTraffic, ManyToMany) {
  EXPECT_THAT(
      ManyToMany({"a", "b"}, {"d", "e"}),
      UnorderedElementsAre(
          InterfacePair{.ingress_interface = "a", .egress_interface = "d"},
          InterfacePair{.ingress_interface = "a", .egress_interface = "e"},
          InterfacePair{.ingress_interface = "b", .egress_interface = "d"},
          InterfacePair{.ingress_interface = "b", .egress_interface = "e"}));

  EXPECT_THAT(ManyToMany({"a", "b"}, {}), IsEmpty());
}

TEST(BasicTraffic, AllToAll) {
  EXPECT_THAT(
      AllToAll({"a", "b", "c"}),
      UnorderedElementsAre(
          InterfacePair{.ingress_interface = "a", .egress_interface = "b"},
          InterfacePair{.ingress_interface = "a", .egress_interface = "c"},
          InterfacePair{.ingress_interface = "b", .egress_interface = "a"},
          InterfacePair{.ingress_interface = "b", .egress_interface = "c"},
          InterfacePair{.ingress_interface = "c", .egress_interface = "a"},
          InterfacePair{.ingress_interface = "c", .egress_interface = "b"}));

  EXPECT_THAT(AllToAll({"a"}), IsEmpty());

  EXPECT_THAT(AllToAll({}), IsEmpty());
}

class FakePacketGenerationFinalizer
    : public thinkit::PacketGenerationFinalizer {
 public:
  absl::Status HandlePacketsFor(absl::Duration /*duration*/,
                                thinkit::PacketCallback callback) override {
    for (const auto& [interface, packet] : packets_) {
      callback(interface, packet);
    }
    packets_.clear();
    return absl::OkStatus();
  }

  void CollectPacket(absl::string_view interface, absl::string_view packet) {
    packets_.push_back(std::pair<std::string, std::string>(interface, packet));
  }

 private:
  std::vector<std::pair<std::string, std::string>> packets_;
};

// Returns the expected gNMI response that implies a certainn
// `interface_to_port_id` mapping.
gnmi::GetResponse GenerateResponseForInterfaceToPortID(
    absl::Span<const std::pair<absl::string_view, int>> interface_to_port_id) {
  constexpr absl::string_view kResponseTemplate =
      R"pb(notification {
             timestamp: 1620348032128305716
             prefix { origin: "openconfig" }
             update {
               path { elem { name: "interfaces" } }
               val {
                 json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[$0]}}"
               }
             }
           })pb";
  constexpr absl::string_view kInterfaceTemplate =
      R"({\"name\":\"$0\",\"state\":{\"openconfig-p4rt:id\":$1}})";
  std::vector<std::string> interfaces;
  interfaces.reserve(interface_to_port_id.size());
  for (const auto& [interface, id] : interface_to_port_id) {
    interfaces.push_back(absl::Substitute(kInterfaceTemplate, interface, id));
  }
  return gutil::ParseProtoOrDie<gnmi::GetResponse>(
      absl::Substitute(kResponseTemplate, absl::StrJoin(interfaces, ",")));
}

// This test simulates sending IPv4 UDP packets on two flows:
// 1. Ingress on SUT Ethernet0 and egress on SUT Ethernet1.
// 2. Ingress on SUT Ethernet0 and egress on SUT Ethernet2.
// For simplicity, the port IDs are 0 for Ethernet0, 1 for Ethernet1, etc.
TEST(BasicTraffic, SendTraffic) {
  // This mock function validates the function performs the P4RT programming
  // requests properly. `SendTraffic` should also revert all flows programmed.
  MockFunction<absl::Status(pdpi::P4RuntimeSession*,
                            const p4::v1::WriteRequest&)>
      mock_write_request;

  // Expect the default VRF.
  Expectation add_vrf =
      EXPECT_CALL(
          mock_write_request,
          Call(_,
               EqualsProto(R"pb(updates {
                                  type: INSERT
                                  entity {
                                    table_entry {
                                      table_id: 33554506
                                      match {
                                        field_id: 1
                                        exact { value: "traffic-vrf" }
                                      }
                                      action { action { action_id: 24742814 } }
                                    }
                                  }
                                })pb")))
          .WillOnce(Return(absl::OkStatus()));
  Expectation attach_vrf =
      EXPECT_CALL(mock_write_request,
                  Call(_, EqualsProto(R"pb(
                         updates {
                           type: INSERT
                           entity {
                             table_entry {
                               table_id: 33554689
                               action {
                                 action {
                                   action_id: 16777472
                                   params { param_id: 1 value: "traffic-vrf" }
                                 }
                               }
                               priority: 1132
                             }
                           }
                         }
                       )pb")))
          .After(add_vrf)
          .WillOnce(Return(absl::OkStatus()));

  // Expect the router interfaces for ingress and egress interfaces.
  ExpectationSet add_router_interfaces;
  for (int port_id : {0, 1, 2}) {
    add_router_interfaces +=
        EXPECT_CALL(
            mock_write_request,
            Call(_, EqualsProto(absl::Substitute(
                        R"pb(
                          updates {
                            type: INSERT
                            entity {
                              table_entry {
                                table_id: 33554497
                                match {
                                  field_id: 1
                                  exact { value: "traffic-router-interface-$0" }
                                }
                                action {
                                  action {
                                    action_id: 16777218
                                    params { param_id: 1 value: "$0" }
                                    params { param_id: 2 value: "\00$0" }
                                  }
                                }
                              }
                            }
                          }
                        )pb",
                        port_id))))
            .After(attach_vrf)
            .WillOnce(Return(absl::OkStatus()));
  }

  // Expect the IPv4 routes for egress interfaces.
  ExpectationSet add_ipv4_routes;
  for (int port_id : {1, 2}) {
    // Neighbor entry.
    add_ipv4_routes +=
        EXPECT_CALL(
            mock_write_request,
            Call(
                _,
                EqualsProto(absl::Substitute(
                    R"pb(
                      updates {
                        type: INSERT
                        entity {
                          table_entry {
                            table_id: 33554496
                            match {
                              field_id: 1
                              exact { value: "traffic-router-interface-$0" }
                            }
                            match {
                              field_id: 2
                              exact {
                                value: "\376\200\000\000\000\000\000\000\002\032\021\377\376\027\000\200"
                              }
                            }
                            action {
                              action {
                                action_id: 16777217
                                params {
                                  param_id: 1
                                  value: "\032\021\027\000\200"
                                }
                              }
                            }
                          }
                        }
                      }
                    )pb",
                    port_id))))
            .After(add_router_interfaces)
            .WillOnce(Return(absl::OkStatus()));

    // Nexthop entry.
    Expectation add_nexthop =
        EXPECT_CALL(
            mock_write_request,
            Call(
                _,
                EqualsProto(absl::Substitute(
                    R"pb(
                      updates {
                        type: INSERT
                        entity {
                          table_entry {
                            table_id: 33554498
                            match {
                              field_id: 1
                              exact { value: "traffic-nexthop-$0" }
                            }
                            action {
                              action {
                                action_id: 16777236
                                params {
                                  param_id: 1
                                  value: "traffic-router-interface-$0"
                                }
                                params {
                                  param_id: 2
                                  value: "\376\200\000\000\000\000\000\000\002\032\021\377\376\027\000\200"
                                }
                              }
                            }
                          }
                        }
                      }
                    )pb",
                    port_id))))
            .After(add_router_interfaces)
            .WillOnce(Return(absl::OkStatus()));

    // IPv4 table entry.
    add_ipv4_routes +=
        EXPECT_CALL(
            mock_write_request,
            Call(_,
                 EqualsProto(absl::Substitute(
                     R"pb(
                       updates {
                         type: INSERT
                         entity {
                           table_entry {
                             table_id: 33554500
                             match {
                               field_id: 1
                               exact { value: "traffic-vrf" }
                             }
                             match {
                               field_id: 2
                               lpm { value: "\x0a\x00\x00\x0$0" prefix_len: 32 }
                             }
                             action {
                               action {
                                 action_id: 16777221
                                 params {
                                   param_id: 1
                                   value: "traffic-nexthop-$0"
                                 }
                               }
                             }
                           }
                         }
                       }
                     )pb",
                     port_id))))
            .After(add_nexthop)
            .WillOnce(Return(absl::OkStatus()));
  }

  // Expect adding L3 admit table entry.
  ExpectationSet add_l3_admit_table;
  EXPECT_CALL(
      mock_write_request,
      Call(_, EqualsProto(R"pb(
             updates {
               type: INSERT
               entity {
                 table_entry {
                   table_id: 33554503
                   match {
                     field_id: 1
                     ternary { value: "\000" mask: "\001\000\000\000\000\000" }
                   }
                   action { action { action_id: 16777224 } }
                   priority: 1
                   metadata: "Experimental_type: VARIOUS_L3ADMIT_PUNTFLOW"
                 }
               }
             }
           )pb")))
      .After(add_ipv4_routes)
      .WillOnce(Return(absl::OkStatus()));

  // Expect deleting L3 admit table entry.
  ExpectationSet delete_l3_admit_table;
  EXPECT_CALL(
      mock_write_request,
      Call(_, EqualsProto(R"pb(
             updates {
               type: DELETE
               entity {
                 table_entry {
                   table_id: 33554503
                   match {
                     field_id: 1
                     ternary { value: "\000" mask: "\001\000\000\000\000\000" }
                   }
                   action { action { action_id: 16777224 } }
                   priority: 1
                   metadata: "Experimental_type: VARIOUS_L3ADMIT_PUNTFLOW"
                 }
               }
             }
           )pb")))
      .After(add_l3_admit_table)
      .WillOnce(Return(absl::OkStatus()));

  // Expect deleting IPv4 routes for egress interfaces.
  ExpectationSet delete_ipv4_routes;
  for (int port_id : {1, 2}) {
    // IPv4 table entry.
    Expectation delete_ipv4 =
        EXPECT_CALL(
            mock_write_request,
            Call(_,
                 EqualsProto(absl::Substitute(
                     R"pb(
                       updates {
                         type: DELETE
                         entity {
                           table_entry {
                             table_id: 33554500
                             match {
                               field_id: 1
                               exact { value: "traffic-vrf" }
                             }
                             match {
                               field_id: 2
                               lpm { value: "\x0a\x00\x00\x0$0" prefix_len: 32 }
                             }
                             action {
                               action {
                                 action_id: 16777221
                                 params {
                                   param_id: 1
                                   value: "traffic-nexthop-$0"
                                 }
                               }
                             }
                           }
                         }
                       }
                     )pb",
                     port_id))))
            .After(delete_l3_admit_table)
            .WillOnce(Return(absl::OkStatus()));

    // Nexthop entry.
    delete_ipv4_routes +=
        EXPECT_CALL(
            mock_write_request,
            Call(
                _,
                EqualsProto(absl::Substitute(
                    R"pb(
                      updates {
                        type: DELETE
                        entity {
                          table_entry {
                            table_id: 33554498
                            match {
                              field_id: 1
                              exact { value: "traffic-nexthop-$0" }
                            }
                            action {
                              action {
                                action_id: 16777236
                                params {
                                  param_id: 1
                                  value: "traffic-router-interface-$0"
                                }
                                params {
                                  param_id: 2
                                  value: "\376\200\000\000\000\000\000\000\002\032\021\377\376\027\000\200"
                                }
                              }
                            }
                          }
                        }
                      }
                    )pb",
                    port_id))))
            .After(delete_ipv4)
            .WillOnce(Return(absl::OkStatus()));

    // Neighbor entry.
    delete_ipv4_routes +=
        EXPECT_CALL(
            mock_write_request,
            Call(
                _,
                EqualsProto(absl::Substitute(
                    R"pb(
                      updates {
                        type: DELETE
                        entity {
                          table_entry {
                            table_id: 33554496
                            match {
                              field_id: 1
                              exact { value: "traffic-router-interface-$0" }
                            }
                            match {
                              field_id: 2
                              exact {
                                value: "\376\200\000\000\000\000\000\000\002\032\021\377\376\027\000\200"
                              }
                            }
                            action {
                              action {
                                action_id: 16777217
                                params {
                                  param_id: 1
                                  value: "\032\021\027\000\200"
                                }
                              }
                            }
                          }
                        }
                      }
                    )pb",
                    port_id))))
            .After(add_ipv4_routes)
            .WillOnce(Return(absl::OkStatus()));
  }

  // Expect deleting router interfaces for ingress and egress interfaces.
  ExpectationSet delete_router_interfaces;
  for (int port_id : {0, 1, 2}) {
    delete_router_interfaces +=
        EXPECT_CALL(
            mock_write_request,
            Call(_, EqualsProto(absl::Substitute(
                        R"pb(
                          updates {
                            type: DELETE
                            entity {
                              table_entry {
                                table_id: 33554497
                                match {
                                  field_id: 1
                                  exact { value: "traffic-router-interface-$0" }
                                }
                                action {
                                  action {
                                    action_id: 16777218
                                    params { param_id: 1 value: "$0" }
                                    params { param_id: 2 value: "\00$0" }
                                  }
                                }
                              }
                            }
                          }
                        )pb",
                        port_id))))
            .After(delete_ipv4_routes)
            .WillOnce(Return(absl::OkStatus()));
  }

  // Expect deleting the default VRF.
  Expectation delete_attach_vrf =
      EXPECT_CALL(mock_write_request,
                  Call(_, EqualsProto(R"pb(
                         updates {
                           type: DELETE
                           entity {
                             table_entry {
                               table_id: 33554689
                               action {
                                 action {
                                   action_id: 16777472
                                   params { param_id: 1 value: "traffic-vrf" }
                                 }
                               }
                               priority: 1132
                             }
                           }
                         }
                       )pb")))
          .After(delete_router_interfaces)
          .WillOnce(Return(absl::OkStatus()));
  EXPECT_CALL(
      mock_write_request,
      Call(_, EqualsProto(R"pb(updates {
                                 type: DELETE
                                 entity {
                                   table_entry {
                                     table_id: 33554506
                                     match {
                                       field_id: 1
                                       exact { value: "traffic-vrf" }
                                     }
                                     action { action { action_id: 24742814 } }
                                   }
                                 }
                               })pb")))
      .After(delete_attach_vrf)
      .WillOnce(Return(absl::OkStatus()));

  // The mock SUT returns a mock gNMI stub that returns the interface to port ID
  // mapping.
  thinkit::MockSwitch mock_sut;
  auto mock_gnmi_stub = absl::make_unique<gnmi::MockgNMIStub>();
  EXPECT_CALL(*mock_gnmi_stub, Get(_, _, _))
      .WillOnce(
          DoAll(SetArgPointee<2>(GenerateResponseForInterfaceToPortID(
                    {{"Ethernet0", 0}, {"Ethernet1", 1}, {"Ethernet2", 2}})),
                Return(grpc::Status::OK)));
  EXPECT_CALL(mock_sut, CreateGnmiStub())
      .WillOnce(Return(ByMove(std::move(mock_gnmi_stub))));

  // The mock control device simulates the injection and forwarding/collection
  // of packets based on the destination IP.
  thinkit::MockControlDevice mock_control_device;

  // This pointer is assigned when `CollectPackets` is called, which should
  // happen before `SendPacket` is called.
  FakePacketGenerationFinalizer* fake_finalizer = nullptr;
  EXPECT_CALL(mock_control_device, CollectPackets)
      .WillOnce([&fake_finalizer]()
                    -> absl::StatusOr<
                        std::unique_ptr<thinkit::PacketGenerationFinalizer>> {
        auto finalizer = absl::make_unique<FakePacketGenerationFinalizer>();
        fake_finalizer = finalizer.get();
        return finalizer;
      });
  EXPECT_CALL(mock_control_device, SendPacket)
      .WillRepeatedly([&fake_finalizer](
                          absl::string_view interface, absl::string_view packet,
                          std::optional<absl::Duration> packet_delay) {
        if (fake_finalizer == nullptr) {
          return absl::FailedPreconditionError(
              "`failed_finalizer` is nullptr.");
        }

        // Use the destination IP to determine which interface the `packet`
        // would have been sent to.
        packetlib::Packet parsed_packet = packetlib::ParsePacket(packet);
        if (!parsed_packet.reasons_invalid().empty()) {
          return absl::InvalidArgumentError(absl::StrCat(
              "Packet failed to parse: ", parsed_packet.DebugString()));
        }
        if (parsed_packet.headers_size() < 2 ||
            !parsed_packet.headers(1).has_ipv4_header()) {
          return absl::InvalidArgumentError(
              absl::StrCat("Packet does not have the IPv4 header: ",
                           parsed_packet.DebugString()));
        }
        // The last octet is the port ID % 256, which in our case is 0, 1, or 2.
        absl::string_view destination_ip =
            parsed_packet.headers(1).ipv4_header().ipv4_destination();
        std::vector<absl::string_view> octets =
            absl::StrSplit(destination_ip, '.');
        int port_id;
        if (octets.size() != 4 || !absl::SimpleAtoi(octets[3], &port_id)) {
          return absl::InvalidArgumentError(
              absl::StrCat("IPv4 address malformed: ", destination_ip));
        }
        // SUT EthernetN has port ID N, and connects to Ethernet1N on the
        // control device.
        fake_finalizer->CollectPacket(absl::StrCat("Ethernet1", port_id),
                                      packet);
        return absl::OkStatus();
      });

  // The mock generic testbed returns the test topology and the mock SUT and
  // control device.
  thinkit::MockGenericTestbed mock_generic_testbed;
  EXPECT_CALL(mock_generic_testbed, GetSutInterfaceInfo())
      .WillOnce(Return(absl::flat_hash_map<std::string, thinkit::InterfaceInfo>{
          {"Ethernet0",
           thinkit::InterfaceInfo{
               .interface_modes = {thinkit::CONTROL_INTERFACE},
               .peer_interface_name = "Ethernet10"}},
          {"Ethernet1",
           thinkit::InterfaceInfo{
               .interface_modes = {thinkit::CONTROL_INTERFACE},
               .peer_interface_name = "Ethernet11"}},
          {"Ethernet2", thinkit::InterfaceInfo{
                            .interface_modes = {thinkit::CONTROL_INTERFACE},
                            .peer_interface_name = "Ethernet12"}}}));
  EXPECT_CALL(mock_generic_testbed, Sut()).WillRepeatedly(ReturnRef(mock_sut));
  EXPECT_CALL(mock_generic_testbed, ControlDevice())
      .WillRepeatedly(ReturnRef(mock_control_device));

  auto packet = gutil::ParseProtoOrDie<packetlib::Packet>(R"pb(
    headers {
      ethernet_header {
        ethernet_destination: "02:03:04:05:06:07"
        ethernet_source: "00:01:02:03:04:05"
        ethertype: "0x0800"
      }
    }
    headers {
      ipv4_header {
        version: "0x4"
        ihl: "0x5"
        dscp: "0x03"
        ecn: "0x0"
        identification: "0x0000"
        flags: "0x0"
        fragment_offset: "0x0000"
        ttl: "0x20"
        protocol: "0x11"
        ipv4_source: "1.2.3.4"
        ipv4_destination: "1.2.3.4"
      }
    }
    headers { udp_header { source_port: "0x0000" destination_port: "0x0000" } }
    payload: "Basic L3 test packet")pb");
  ASSERT_OK_AND_ASSIGN(
      std::vector<TrafficStatistic> statistics,
      SendTraffic(mock_generic_testbed, /*session=*/nullptr,
                  sai::GetIrP4Info(sai::Instantiation::kMiddleblock),
                  ManyToMany({"Ethernet0"}, {"Ethernet1", "Ethernet2"}),
                  {std::move(packet)}, absl::Seconds(1),
                  SendTrafficOptions{
                      .packets_per_second = 10,
                      .write_request = mock_write_request.AsStdFunction()}));
  // Should have one statistic per flow (since there is only one packet, 2).
  EXPECT_THAT(statistics,
              UnorderedElementsAre(
                  Field(&TrafficStatistic::interfaces,
                        InterfacePair{.ingress_interface = "Ethernet0",
                                      .egress_interface = "Ethernet1"}),
                  Field(&TrafficStatistic::interfaces,
                        InterfacePair{.ingress_interface = "Ethernet0",
                                      .egress_interface = "Ethernet2"})));
  // All sent packets should be received and not tracked as routed incorrectly.
  for (const TrafficStatistic& statistic : statistics) {
    EXPECT_GT(statistic.packets_sent, 0);
    EXPECT_EQ(statistic.packets_sent, statistic.packets_received);
    EXPECT_EQ(statistic.packets_routed_incorrectly, 0);
  }
}

// This test checks that packets sent to the wrong port are tracked as such.
TEST(BasicTraffic, SendTrafficTracksIncorrectlyRoutedPackets) {
  // The `SendTraffic` test above tests the flow programming, so just return OK.
  MockFunction<absl::Status(pdpi::P4RuntimeSession*,
                            const p4::v1::WriteRequest&)>
      mock_write_request;
  EXPECT_CALL(mock_write_request, Call(_, _))
      .WillRepeatedly(Return(absl::OkStatus()));

  // The mock SUT returns a mock gNMI stub that returns the interface to port ID
  // mapping.
  thinkit::MockSwitch mock_sut;
  auto mock_gnmi_stub = absl::make_unique<gnmi::MockgNMIStub>();
  EXPECT_CALL(*mock_gnmi_stub, Get(_, _, _))
      .WillOnce(
          DoAll(SetArgPointee<2>(GenerateResponseForInterfaceToPortID(
                    {{"Ethernet0", 0}, {"Ethernet1", 1}, {"Ethernet2", 2}})),
                Return(grpc::Status::OK)));
  EXPECT_CALL(mock_sut, CreateGnmiStub())
      .WillOnce(Return(ByMove(std::move(mock_gnmi_stub))));

  // The mock control device simulates the injection and forwarding/collection
  // of packets based on the destination IP.
  thinkit::MockControlDevice mock_control_device;

  // This pointer is assigned when `CollectPackets` is called, which should
  // happen before `SendPacket` is called.
  FakePacketGenerationFinalizer* fake_finalizer = nullptr;
  EXPECT_CALL(mock_control_device, CollectPackets)
      .WillOnce([&fake_finalizer]()
                    -> absl::StatusOr<
                        std::unique_ptr<thinkit::PacketGenerationFinalizer>> {
        auto finalizer = absl::make_unique<FakePacketGenerationFinalizer>();
        fake_finalizer = finalizer.get();
        return finalizer;
      });
  EXPECT_CALL(mock_control_device, SendPacket(_, _, _))
      .WillRepeatedly([&fake_finalizer](
                          absl::string_view interface, absl::string_view packet,
                          std::optional<absl::Duration> packet_delay) {
        if (fake_finalizer == nullptr) {
          return absl::FailedPreconditionError(
              "`failed_finalizer` is nullptr.");
        }
        // Just send the packet to a port that isn't expected, such as
        // Ethernet10, which is connected to the SUT's Ethernet0, which is not
        // an egress destiation.
        fake_finalizer->CollectPacket("Ethernet10", packet);
        return absl::OkStatus();
      });

  // The mock generic testbed returns the test topology and the mock SUT and
  // control device.
  thinkit::MockGenericTestbed mock_generic_testbed;
  EXPECT_CALL(mock_generic_testbed, GetSutInterfaceInfo())
      .WillOnce(Return(absl::flat_hash_map<std::string, thinkit::InterfaceInfo>{
          {"Ethernet0",
           thinkit::InterfaceInfo{
               .interface_modes = {thinkit::CONTROL_INTERFACE},
               .peer_interface_name = "Ethernet10"}},
          {"Ethernet1",
           thinkit::InterfaceInfo{
               .interface_modes = {thinkit::CONTROL_INTERFACE},
               .peer_interface_name = "Ethernet11"}},
          {"Ethernet2", thinkit::InterfaceInfo{
                            .interface_modes = {thinkit::CONTROL_INTERFACE},
                            .peer_interface_name = "Ethernet12"}}}));
  EXPECT_CALL(mock_generic_testbed, Sut()).WillRepeatedly(ReturnRef(mock_sut));
  EXPECT_CALL(mock_generic_testbed, ControlDevice())
      .WillRepeatedly(ReturnRef(mock_control_device));

  auto packet =
      gutil::ParseProtoOrDie<packetlib::Packet>(R"pb(
        headers {
          ethernet_header {
            ethernet_destination: "02:03:04:05:06:07"
            ethernet_source: "00:01:02:03:04:05"
            ethertype: "0x0800"
          }
        }
        headers {
          ipv4_header {
            version: "0x4"
            ihl: "0x5"
            dscp: "0x03"
            ecn: "0x0"
            identification: "0x0000"
            flags: "0x0"
            fragment_offset: "0x0000"
            ttl: "0x20"
            protocol: "0x11"
            ipv4_source: "1.2.3.4"
            ipv4_destination: "1.2.3.4"
          }
        }
        headers {
          udp_header { source_port: "0x0000" destination_port: "0x0000" }
        })pb");
  ASSERT_OK_AND_ASSIGN(
      std::vector<TrafficStatistic> statistics,
      SendTraffic(mock_generic_testbed, /*session=*/nullptr,
                  sai::GetIrP4Info(sai::Instantiation::kMiddleblock),
                  ManyToMany({"Ethernet0"}, {"Ethernet1", "Ethernet2"}),
                  {std::move(packet)}, absl::Seconds(1),
                  SendTrafficOptions{
                      .packets_per_second = 10,
                      .write_request = mock_write_request.AsStdFunction()}));
  // Should have one statistic per flow (since there is only one packet, 2).
  EXPECT_THAT(statistics,
              UnorderedElementsAre(
                  Field(&TrafficStatistic::interfaces,
                        InterfacePair{.ingress_interface = "Ethernet0",
                                      .egress_interface = "Ethernet1"}),
                  Field(&TrafficStatistic::interfaces,
                        InterfacePair{.ingress_interface = "Ethernet0",
                                      .egress_interface = "Ethernet2"})));
  // All sent packets should be tracked as routed incorrectly and not received.
  for (const TrafficStatistic& statistic : statistics) {
    EXPECT_GT(statistic.packets_sent, 0);
    EXPECT_EQ(statistic.packets_sent, statistic.packets_routed_incorrectly);
    EXPECT_EQ(statistic.packets_received, 0);
  }
}

// This test checks that packets sent keep the same payload size if it's larger
// than the minimum size.
TEST(BasicTraffic, SendTrafficBigPackets) {
  static constexpr int kPayloadSize = 500;

  // The `SendTraffic` test above tests the flow programming, so just return OK.
  MockFunction<absl::Status(pdpi::P4RuntimeSession*,
                            const p4::v1::WriteRequest&)>
      mock_write_request;
  EXPECT_CALL(mock_write_request, Call(_, _))
      .WillRepeatedly(Return(absl::OkStatus()));

  // The mock SUT returns a mock gNMI stub that returns the interface to port ID
  // mapping.
  thinkit::MockSwitch mock_sut;
  auto mock_gnmi_stub = absl::make_unique<gnmi::MockgNMIStub>();
  EXPECT_CALL(*mock_gnmi_stub, Get(_, _, _))
      .WillOnce(
          DoAll(SetArgPointee<2>(GenerateResponseForInterfaceToPortID(
                    {{"Ethernet0", 0}, {"Ethernet1", 1}, {"Ethernet2", 2}})),
                Return(grpc::Status::OK)));
  EXPECT_CALL(mock_sut, CreateGnmiStub())
      .WillOnce(Return(ByMove(std::move(mock_gnmi_stub))));

  // The mock control device simulates the injection and forwarding/collection
  // of packets based on the destination IP.
  thinkit::MockControlDevice mock_control_device;

  // This pointer is assigned when `CollectPackets` is called, which should
  // happen before `SendPacket` is called.
  FakePacketGenerationFinalizer* fake_finalizer = nullptr;
  EXPECT_CALL(mock_control_device, CollectPackets)
      .WillOnce([&fake_finalizer]()
                    -> absl::StatusOr<
                        std::unique_ptr<thinkit::PacketGenerationFinalizer>> {
        auto finalizer = absl::make_unique<FakePacketGenerationFinalizer>();
        fake_finalizer = finalizer.get();
        return finalizer;
      });
  EXPECT_CALL(mock_control_device, SendPacket(_, _, _))
      .WillRepeatedly([&fake_finalizer](
                          absl::string_view interface, absl::string_view packet,
                          std::optional<absl::Duration> packet_delay) {
        if (fake_finalizer == nullptr) {
          return absl::FailedPreconditionError(
              "`failed_finalizer` is nullptr.");
        }
        // Just send the packet to a port that isn't expected, such as
        // Ethernet10, which is connected to the SUT's Ethernet0, which is not
        // an egress destiation.
        fake_finalizer->CollectPacket("Ethernet10", packet);
        return absl::OkStatus();
      });

  // The mock generic testbed returns the test topology and the mock SUT and
  // control device.
  thinkit::MockGenericTestbed mock_generic_testbed;
  EXPECT_CALL(mock_generic_testbed, GetSutInterfaceInfo())
      .WillOnce(Return(absl::flat_hash_map<std::string, thinkit::InterfaceInfo>{
          {"Ethernet0",
           thinkit::InterfaceInfo{
               .interface_modes = {thinkit::CONTROL_INTERFACE},
               .peer_interface_name = "Ethernet10"}},
          {"Ethernet1",
           thinkit::InterfaceInfo{
               .interface_modes = {thinkit::CONTROL_INTERFACE},
               .peer_interface_name = "Ethernet11"}},
          {"Ethernet2", thinkit::InterfaceInfo{
                            .interface_modes = {thinkit::CONTROL_INTERFACE},
                            .peer_interface_name = "Ethernet12"}}}));
  EXPECT_CALL(mock_generic_testbed, Sut()).WillRepeatedly(ReturnRef(mock_sut));
  EXPECT_CALL(mock_generic_testbed, ControlDevice())
      .WillRepeatedly(ReturnRef(mock_control_device));

  auto packet = gutil::ParseProtoOrDie<packetlib::Packet>(absl::Substitute(
      R"pb(
        headers {
          ethernet_header {
            ethernet_destination: "02:03:04:05:06:07"
            ethernet_source: "00:01:02:03:04:05"
            ethertype: "0x0800"
          }
        }
        headers {
          ipv4_header {
            version: "0x4"
            ihl: "0x5"
            dscp: "0x03"
            ecn: "0x0"
            identification: "0x0000"
            flags: "0x0"
            fragment_offset: "0x0000"
            ttl: "0x20"
            protocol: "0x11"
            ipv4_source: "1.2.3.4"
            ipv4_destination: "1.2.3.4"
          }
        }
        headers {
          udp_header { source_port: "0x0000" destination_port: "0x0000" }
        }
        payload: "$0")pb",
      std::string(kPayloadSize, 'a')));
  ASSERT_OK_AND_ASSIGN(
      std::vector<TrafficStatistic> statistics,
      SendTraffic(mock_generic_testbed, /*session=*/nullptr,
                  sai::GetIrP4Info(sai::Instantiation::kMiddleblock),
                  ManyToMany({"Ethernet0"}, {"Ethernet1", "Ethernet2"}),
                  {std::move(packet)}, absl::Seconds(1),
                  SendTrafficOptions{
                      .packets_per_second = 10,
                      .write_request = mock_write_request.AsStdFunction()}));
  // Should have one statistic per flow (since there is only one packet, 2).
  EXPECT_THAT(statistics,
              UnorderedElementsAre(
                  Field(&TrafficStatistic::interfaces,
                        InterfacePair{.ingress_interface = "Ethernet0",
                                      .egress_interface = "Ethernet1"}),
                  Field(&TrafficStatistic::interfaces,
                        InterfacePair{.ingress_interface = "Ethernet0",
                                      .egress_interface = "Ethernet2"})));
  // All actually sent packets should have the same payload size.
  for (const TrafficStatistic& statistic : statistics) {
    EXPECT_EQ(statistic.packet.payload().size(), kPayloadSize);
    // The rest of the test is the same as the routed incorrectly test.
    EXPECT_GT(statistic.packets_sent, 0);
    EXPECT_EQ(statistic.packets_sent, statistic.packets_routed_incorrectly);
    EXPECT_EQ(statistic.packets_received, 0);
  }
}

// This test checks that packets_sent value returned by the function matches the
// number of times the function calls the SendPacket function.
TEST(BasicTraffic, SendTrafficPacketsSentAccurate) {
  static constexpr int kPayloadSize = 500;

  // The `SendTraffic` test above tests the flow programming, so just return OK.
  MockFunction<absl::Status(pdpi::P4RuntimeSession*,
                            const p4::v1::WriteRequest&)>
      mock_write_request;
  EXPECT_CALL(mock_write_request, Call(_, _))
      .WillRepeatedly(Return(absl::OkStatus()));

  // The mock SUT returns a mock gNMI stub that returns the interface to port ID
  // mapping.
  thinkit::MockSwitch mock_sut;
  auto mock_gnmi_stub = absl::make_unique<gnmi::MockgNMIStub>();
  EXPECT_CALL(*mock_gnmi_stub, Get(_, _, _))
      .WillOnce(
          DoAll(SetArgPointee<2>(GenerateResponseForInterfaceToPortID(
                    {{"Ethernet0", 0}, {"Ethernet1", 1}, {"Ethernet2", 2}})),
                Return(grpc::Status::OK)));
  EXPECT_CALL(mock_sut, CreateGnmiStub())
      .WillOnce(Return(ByMove(std::move(mock_gnmi_stub))));

  // The mock control device simulates the injection and forwarding/collection
  // of packets based on the destination IP.
  thinkit::MockControlDevice mock_control_device;

  // This pointer is assigned when `CollectPackets` is called, which should
  // happen before `SendPacket` is called.
  FakePacketGenerationFinalizer* fake_finalizer = nullptr;
  EXPECT_CALL(mock_control_device, CollectPackets)
      .WillOnce([&fake_finalizer]()
                    -> absl::StatusOr<
                        std::unique_ptr<thinkit::PacketGenerationFinalizer>> {
        auto finalizer = absl::make_unique<FakePacketGenerationFinalizer>();
        fake_finalizer = finalizer.get();
        return finalizer;
      });

  // Tracks the number of times SendPacket is called. This should match the
  // value returned by the function for `packets_sent`.
  int send_packet_calls = 0;
  EXPECT_CALL(mock_control_device, SendPacket(_, _, _))
      .WillRepeatedly([&fake_finalizer, &send_packet_calls](
                          absl::string_view interface, absl::string_view packet,
                          std::optional<absl::Duration> packet_delay) {
        if (fake_finalizer == nullptr) {
          return absl::FailedPreconditionError(
              "`failed_finalizer` is nullptr.");
        }
        // Just send the packet to a port that isn't expected, such as
        // Ethernet10, which is connected to the SUT's Ethernet0, which is not
        // an egress destiation.
        fake_finalizer->CollectPacket("Ethernet10", packet);
        send_packet_calls++;
        return absl::OkStatus();
      });

  // The mock generic testbed returns the test topology and the mock SUT and
  // control device.
  thinkit::MockGenericTestbed mock_generic_testbed;
  EXPECT_CALL(mock_generic_testbed, GetSutInterfaceInfo())
      .WillOnce(Return(absl::flat_hash_map<std::string, thinkit::InterfaceInfo>{
          {"Ethernet0",
           thinkit::InterfaceInfo{
               .interface_modes = {thinkit::CONTROL_INTERFACE},
               .peer_interface_name = "Ethernet10"}},
          {"Ethernet1",
           thinkit::InterfaceInfo{
               .interface_modes = {thinkit::CONTROL_INTERFACE},
               .peer_interface_name = "Ethernet11"}},
          {"Ethernet2", thinkit::InterfaceInfo{
                            .interface_modes = {thinkit::CONTROL_INTERFACE},
                            .peer_interface_name = "Ethernet12"}}}));
  EXPECT_CALL(mock_generic_testbed, Sut()).WillRepeatedly(ReturnRef(mock_sut));
  EXPECT_CALL(mock_generic_testbed, ControlDevice())
      .WillRepeatedly(ReturnRef(mock_control_device));

  auto packet = gutil::ParseProtoOrDie<packetlib::Packet>(absl::Substitute(
      R"pb(
        headers {
          ethernet_header {
            ethernet_destination: "02:03:04:05:06:07"
            ethernet_source: "00:01:02:03:04:05"
            ethertype: "0x0800"
          }
        }
        headers {
          ipv4_header {
            version: "0x4"
            ihl: "0x5"
            dscp: "0x03"
            ecn: "0x0"
            identification: "0x0000"
            flags: "0x0"
            fragment_offset: "0x0000"
            ttl: "0x20"
            protocol: "0x11"
            ipv4_source: "1.2.3.4"
            ipv4_destination: "1.2.3.4"
          }
        }
        headers {
          udp_header { source_port: "0x0000" destination_port: "0x0000" }
        }
        payload: "$0")pb",
      std::string(kPayloadSize, 'a')));

  static constexpr absl::Duration kTrafficDuration = absl::Seconds(10);
  int packets_sent = 0;
  ASSERT_OK_AND_ASSIGN(
      std::vector<TrafficStatistic> statistics,
      SendTraffic(mock_generic_testbed, /*session=*/nullptr,
                  sai::GetIrP4Info(sai::Instantiation::kMiddleblock),
                  ManyToMany({"Ethernet0"}, {"Ethernet1", "Ethernet2"}),
                  {std::move(packet)}, kTrafficDuration,
                  SendTrafficOptions{
                      .packets_per_second = 100,
                      .write_request = mock_write_request.AsStdFunction(),
                      .packets_sent = &packets_sent}));
  EXPECT_EQ(packets_sent, send_packet_calls);
}

}  // namespace
}  // namespace pins_test::basic_traffic
