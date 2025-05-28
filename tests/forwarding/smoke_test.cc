// Copyright 2024 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "tests/forwarding/smoke_test.h"

#include <memory>
#include <optional>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "gmock/gmock.h"
#include "google/protobuf/util/message_differencer.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto_matchers.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
#include "lib/gnmi/gnmi_helper.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/netaddr/ipv6_address.h"
#include "p4_infra/netaddr/mac_address.h"
#include "p4_infra/p4_pdpi/ir.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "p4_infra/p4_pdpi/p4_runtime_session_extras.h"
#include "p4_infra/p4_pdpi/pd.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "sai_p4/instantiations/google/test_tools/test_entries.h"
#include "tests/forwarding/test_data.h"
#include "tests/lib/p4rt_fixed_table_programming_helper.h"
#include "tests/lib/switch_test_setup_helpers.h"
#include "thinkit/mirror_testbed.h"
#include "thinkit/test_environment.h"

namespace pins_test {
namespace {

using ::gutil::EqualsProto;
using ::gutil::IsOk;
using ::gutil::StatusIs;
using ::testing::ElementsAre;
using ::testing::Not;

TEST_P(SmokeTestFixture, CanEstablishConnections) {
  thinkit::MirrorTestbed& testbed =
      GetParam().mirror_testbed->GetMirrorTestbed();
  std::unique_ptr<pdpi::P4RuntimeSession> sut_p4rt_session,
      control_switch_p4rt_session;

  // Initialize the connection, clear table entries, and push GNMI
  // configuration (if given) for the SUT and Control switch.
  ASSERT_OK_AND_ASSIGN(
      std::tie(sut_p4rt_session, control_switch_p4rt_session),
      pins_test::ConfigureSwitchPairAndReturnP4RuntimeSessionPair(
          testbed.Sut(), testbed.ControlSwitch(), GetParam().gnmi_config,
          GetParam().p4info));
  ASSERT_NE(sut_p4rt_session, nullptr);
  ASSERT_NE(control_switch_p4rt_session, nullptr);
}

TEST_P(SmokeTestFixture, AclTableAddModifyDeleteOk) {
  thinkit::MirrorTestbed& testbed =
      GetParam().mirror_testbed->GetMirrorTestbed();

  // Initialize the connection, clear table entries, and push GNMI
  // configuration (if given) for the SUT and Control switch.
  std::unique_ptr<pdpi::P4RuntimeSession> sut_p4rt_session,
      control_switch_p4rt_session;
  ASSERT_OK_AND_ASSIGN(
      std::tie(sut_p4rt_session, control_switch_p4rt_session),
      pins_test::ConfigureSwitchPairAndReturnP4RuntimeSessionPair(
          testbed.Sut(), testbed.ControlSwitch(), GetParam().gnmi_config,
          GetParam().p4info));

  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info ir_p4info,
                       pdpi::GetIrP4Info(*sut_p4rt_session));

  const sai::WriteRequest pd_insert = gutil::ParseProtoOrDie<sai::WriteRequest>(
      R"pb(
        updates {
          type: INSERT
          table_entry {
            acl_ingress_table_entry {
              match { is_ip { value: "0x1" } }
              priority: 10
              action { acl_copy { qos_queue: "0x1" } }
            }
          }
        }
      )pb");
  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest pi_insert,
          pdpi::PdWriteRequestToPi(ir_p4info, pd_insert)); 
 
  const sai::WriteRequest pd_modify = gutil::ParseProtoOrDie<sai::WriteRequest>(
      R"pb(
        updates {
          type: MODIFY
          table_entry {
            acl_ingress_table_entry {
              match { is_ip { value: "0x1" } }
              priority: 10
              action { acl_forward {} }
            }
          }
        }
      )pb");
  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest pi_modify,
                       pdpi::PdWriteRequestToPi(ir_p4info, pd_modify));
  
  const sai::WriteRequest pd_delete = gutil::ParseProtoOrDie<sai::WriteRequest>(
      R"pb(
        updates {
          type: DELETE
          table_entry {
            acl_ingress_table_entry {
              match { is_ip { value: "0x1" } }
              priority: 10
              action { acl_forward {} }
            }
          }
        }
      )pb");
  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest pi_delete,
                       pdpi::PdWriteRequestToPi(ir_p4info, pd_delete));

  // Insert works.
  ASSERT_OK(pdpi::SetMetadataAndSendPiWriteRequest(sut_p4rt_session.get(),
                                                   pi_insert));

  // ACL table entries are expected to contain counter data. However, it's
  // updated periodically and may not be avaialable immediatly after writing so
  // we poll the entry for a few seconds until we see the data.
  absl::Time timeout = absl::Now() + absl::Seconds(11);
  p4::v1::ReadResponse pi_read_response;
  p4::v1::ReadRequest pi_read_request;
  pi_read_request.add_entities()->mutable_table_entry();
  do {
    ASSERT_OK_AND_ASSIGN(pi_read_response,
                         pdpi::SetMetadataAndSendPiReadRequest(
                             sut_p4rt_session.get(), pi_read_request));
    ASSERT_EQ(pi_read_response.entities_size(), 1);

    if (absl::Now() > timeout) {
      FAIL() << "ACL table entry does not have counter data.";
    }
  } while (!pi_read_response.entities(0).table_entry().has_counter_data());

  ASSERT_OK(pdpi::SetMetadataAndSendPiWriteRequest(sut_p4rt_session.get(),
                                                   pi_modify));
  // Delete works.
  ASSERT_OK(pdpi::SetMetadataAndSendPiWriteRequest(sut_p4rt_session.get(),
                                                   pi_delete));
}

TEST_P(SmokeTestFixture, FixedTableAddModifyDeleteOk) {
  thinkit::MirrorTestbed& testbed =
      GetParam().mirror_testbed->GetMirrorTestbed();

  // Initialize the connection, clear table entries, and push GNMI
  // configuration (if given) for the SUT and Control switch.
  std::unique_ptr<pdpi::P4RuntimeSession> sut_p4rt_session,
      control_switch_p4rt_session;
  ASSERT_OK_AND_ASSIGN(
      std::tie(sut_p4rt_session, control_switch_p4rt_session),
      pins_test::ConfigureSwitchPairAndReturnP4RuntimeSessionPair(
          testbed.Sut(), testbed.ControlSwitch(), GetParam().gnmi_config,
          GetParam().p4info));

  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info ir_p4info,
                       pdpi::GetIrP4Info(*sut_p4rt_session));

  p4::v1::WriteRequest pi_request;
  ASSERT_OK_AND_ASSIGN(
      *pi_request.add_updates(),
      pins::VrfTableUpdate(
	      ir_p4info, p4::v1::Update::INSERT, "vrf-1"));
  ASSERT_OK_AND_ASSIGN(
      *pi_request.add_updates(),
      pins::RouterInterfaceTableUpdate(ir_p4info, p4::v1::Update::INSERT,
                                       "router-intf-1", /*port=*/"1",
                                       /*src_mac=*/"00:01:02:03:04:05"));
  ASSERT_OK_AND_ASSIGN(*pi_request.add_updates(),
                       pins::NeighborTableUpdate(
                           ir_p4info, p4::v1::Update::INSERT, "router-intf-1",
                           /*neighbor_id=*/"fe80::0000:00ff:fe17:5f80",
                           /*dst_mac=*/"00:01:02:03:04:06"));
  ASSERT_OK_AND_ASSIGN(
      *pi_request.add_updates(),
      pins::NexthopTableUpdate(ir_p4info, p4::v1::Update::INSERT, "nexthop-1",
                                "router-intf-1",
                                /*neighbor_id=*/"fe80::0000:00ff:fe17:5f80"));
  ASSERT_OK(pdpi::SetMetadataAndSendPiWriteRequest(sut_p4rt_session.get(),
                                                   pi_request));

  // Add and modify IPV4 table entry with different number of action params.
  pi_request.Clear();
  ASSERT_OK_AND_ASSIGN(
      *pi_request.add_updates(),
      pins::Ipv4TableUpdate(
	  ir_p4info, p4::v1::Update::INSERT,
          pins::IpTableOptions{
              .vrf_id = "vrf-1",
              .dst_addr_lpm = std::make_pair("20.0.0.1", 32),
              .action = pins::IpTableOptions::Action::kSetNextHopId,
              .nexthop_id = "nexthop-1",
          }));
  ASSERT_OK(pdpi::SetMetadataAndSendPiWriteRequest(sut_p4rt_session.get(),
                                                   pi_request));
  pi_request.Clear();
  ASSERT_OK_AND_ASSIGN(
      *pi_request.add_updates(),
      pins::Ipv4TableUpdate(ir_p4info,
	                     p4::v1::Update::MODIFY,
                             pins::IpTableOptions{
                                 .vrf_id = "vrf-1",
                                 .dst_addr_lpm = std::make_pair("20.0.0.1", 32),
                                 .action = pins::IpTableOptions::Action::kDrop,
                             }));
  ASSERT_OK(pdpi::SetMetadataAndSendPiWriteRequest(sut_p4rt_session.get(),
                                                   pi_request));

  pi_request.Clear();
  ASSERT_OK_AND_ASSIGN(
      *pi_request.add_updates(),
      pins::Ipv4TableUpdate(ir_p4info,
	                     p4::v1::Update::DELETE,
                             pins::IpTableOptions{
                                 .vrf_id = "vrf-1",
                                 .dst_addr_lpm = std::make_pair("20.0.0.1", 32),
                                 .action = pins::IpTableOptions::Action::kDrop,
                             }));

  ASSERT_OK(pdpi::SetMetadataAndSendPiWriteRequest(sut_p4rt_session.get(),
                                                   pi_request));

  // This used to fail with a read error.
  ASSERT_OK(pdpi::ClearTableEntries(sut_p4rt_session.get()));
}

TEST_P(SmokeTestFixture, InsertTableEntry) {
  thinkit::MirrorTestbed& testbed =
      GetParam().mirror_testbed->GetMirrorTestbed();

  // Initialize the connection, clear table entries, and push GNMI
  // configuration (if given) for the SUT and Control switch.
  std::unique_ptr<pdpi::P4RuntimeSession> sut_p4rt_session,
      control_switch_p4rt_session;
  ASSERT_OK_AND_ASSIGN(
      std::tie(sut_p4rt_session, control_switch_p4rt_session),
      pins_test::ConfigureSwitchPairAndReturnP4RuntimeSessionPair(
          testbed.Sut(), testbed.ControlSwitch(), GetParam().gnmi_config,
          GetParam().p4info));

  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info ir_p4info,
                       pdpi::GetIrP4Info(*sut_p4rt_session));

  const sai::TableEntry pd_entry = gutil::ParseProtoOrDie<sai::TableEntry>(
      R"pb(
        router_interface_table_entry {
          match { router_interface_id: "router-interface-1" }
          action {
            set_port_and_src_mac { port: "1" src_mac: "02:2a:10:00:00:03" }
          }
        }
      )pb");

  ASSERT_OK_AND_ASSIGN(const p4::v1::TableEntry pi_entry,
                       pdpi::PartialPdTableEntryToPiTableEntry(
		       ir_p4info, pd_entry));
  ASSERT_OK(pdpi::InstallPiTableEntry(sut_p4rt_session.get(), pi_entry));
}

TEST_P(SmokeTestFixture, InsertTableEntryFailsWithNonUtf8Character) {
  thinkit::MirrorTestbed& testbed =
      GetParam().mirror_testbed->GetMirrorTestbed();

  // Initialize the connection, clear table entries, and push GNMI
  // configuration (if given) for the SUT and Control switch.
  std::unique_ptr<pdpi::P4RuntimeSession> sut_p4rt_session,
      control_switch_p4rt_session;
  ASSERT_OK_AND_ASSIGN(
      std::tie(sut_p4rt_session, control_switch_p4rt_session),
      pins_test::ConfigureSwitchPairAndReturnP4RuntimeSessionPair(
          testbed.Sut(), testbed.ControlSwitch(), GetParam().gnmi_config,
          GetParam().p4info));

  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info ir_p4info,
                       pdpi::GetIrP4Info(*sut_p4rt_session));

  sai::TableEntry pd_entry = gutil::ParseProtoOrDie<sai::TableEntry>(
      R"pb(
        router_interface_table_entry {
          match { router_interface_id: "\x01\x33\x00\xff,\":'}(*{+-" }
          action {
            set_port_and_src_mac { port: "1" src_mac: "02:2a:10:00:00:03" }
          }
        }
      )pb");

  ASSERT_OK_AND_ASSIGN(
      const p4::v1::TableEntry pi_entry,
      pdpi::PartialPdTableEntryToPiTableEntry(ir_p4info, pd_entry));
  EXPECT_THAT(pdpi::InstallPiTableEntry(sut_p4rt_session.get(), pi_entry),
              StatusIs(absl::StatusCode::kUnknown));
}

TEST_P(SmokeTestFixture, InsertAndReadTableEntries) {

  thinkit::MirrorTestbed& testbed =
      GetParam().mirror_testbed->GetMirrorTestbed();

  // Initialize the connection, clear table entries, and push GNMI
  // configuration (if given) for the SUT and Control switch.
  std::unique_ptr<pdpi::P4RuntimeSession> sut_p4rt_session,
      control_switch_p4rt_session;
  ASSERT_OK_AND_ASSIGN(
      std::tie(sut_p4rt_session, control_switch_p4rt_session),
      pins_test::ConfigureSwitchPairAndReturnP4RuntimeSessionPair(
          testbed.Sut(), testbed.ControlSwitch(), GetParam().gnmi_config,
          GetParam().p4info));

  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info ir_p4info,
                       pdpi::GetIrP4Info(*sut_p4rt_session));

  std::vector<sai::TableEntry> write_pd_entries =
      sai_pd::CreateUpTo255GenericTableEntries(3);

  thinkit::TestEnvironment& test_environment = testbed.Environment();
  std::vector<p4::v1::TableEntry> write_pi_entries;
  p4::v1::ReadResponse expected_read_response;
  write_pi_entries.reserve(write_pd_entries.size());
  for (const auto& pd_entry : write_pd_entries) {
    ASSERT_OK_AND_ASSIGN(p4::v1::TableEntry pi_entry,
                         pdpi::PartialPdTableEntryToPiTableEntry(ir_p4info, pd_entry));

    ASSERT_OK(test_environment.AppendToTestArtifact(
        "pi_entries_written.pb.txt",
        absl::StrCat(pi_entry.DebugString(), "\n")));
    *expected_read_response.add_entities()->mutable_table_entry() = pi_entry;
    write_pi_entries.push_back(std::move(pi_entry));
  }

  ASSERT_OK(pdpi::InstallPiTableEntries(sut_p4rt_session.get(), ir_p4info,
                                        write_pi_entries));

  p4::v1::ReadRequest read_request;
  read_request.add_entities()->mutable_table_entry();
  ASSERT_OK_AND_ASSIGN(p4::v1::ReadResponse read_response,
                       pdpi::SetMetadataAndSendPiReadRequest(
                           sut_p4rt_session.get(), read_request));

  for (const auto& entity : read_response.entities()) {
    ASSERT_OK(test_environment.AppendToTestArtifact(
        "pi_entries_read_back.pb.txt",
        absl::StrCat(entity.table_entry().DebugString(), "\n")));
  }

  // Compare the result in proto format since the fields being compared are
  // nested and out of order. Also ignore any dynamic fields (e.g. counters).
  google::protobuf::util::MessageDifferencer diff;
  diff.set_repeated_field_comparison(
      google::protobuf::util::MessageDifferencer::RepeatedFieldComparison::
           AS_SET);
  diff.IgnoreField(
      p4::v1::TableEntry::descriptor()->FindFieldByName("counter_data"));
  EXPECT_TRUE(diff.Compare(read_response, expected_read_response))
      << "Expected: " << expected_read_response.DebugString()
      << "\nActual: " << read_response.DebugString();
}

// Ensures that both CreateWithP4InfoAndClearTables and ClearTableEntries
// properly clear the table entries of a table.
TEST_P(SmokeTestFixture, EnsureClearTables) {
  thinkit::MirrorTestbed& testbed =
      GetParam().mirror_testbed->GetMirrorTestbed();

  // Initialize the connection, clear table entries, and push GNMI
  // configuration (if given) for the SUT and Control switch.
  std::unique_ptr<pdpi::P4RuntimeSession> sut_p4rt_session,
      control_switch_p4rt_session;
  ASSERT_OK_AND_ASSIGN(
      std::tie(sut_p4rt_session, control_switch_p4rt_session),
      pins_test::ConfigureSwitchPairAndReturnP4RuntimeSessionPair(
          testbed.Sut(), testbed.ControlSwitch(), GetParam().gnmi_config,
          GetParam().p4info));

  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info ir_p4info,
                       pdpi::GetIrP4Info(*sut_p4rt_session));

  // The table should be clear after setup.
  ASSERT_OK(pdpi::CheckNoTableEntries(sut_p4rt_session.get()));
  // Sets up an example table entry.
  const sai::TableEntry pd_entry = gutil::ParseProtoOrDie<sai::TableEntry>(
      R"pb(
        router_interface_table_entry {
          match { router_interface_id: "router-interface-1" }
          action {
            set_port_and_src_mac { port: "1" src_mac: "02:2a:10:00:00:03" }
          }
        }
      )pb");
  ASSERT_OK_AND_ASSIGN(p4::v1::TableEntry pi_entry,
                       pdpi::PartialPdTableEntryToPiTableEntry(
		       ir_p4info, pd_entry));
  ASSERT_OK(
      pdpi::InstallPiTableEntries(sut_p4rt_session.get(), 
	      ir_p4info, {pi_entry}));
  ASSERT_OK(pdpi::ClearTableEntries(sut_p4rt_session.get()));
  // The table should be clear after clearing.
  ASSERT_OK(pdpi::CheckNoTableEntries(sut_p4rt_session.get()));
  
  ASSERT_OK(
      pdpi::InstallPiTableEntries(sut_p4rt_session.get(), 
	      ir_p4info, {pi_entry}));

  ASSERT_OK_AND_ASSIGN(
      auto session2,
      pins_test::ConfigureSwitchAndReturnP4RuntimeSession(
          testbed.Sut(), /*gnmi_config=*/std::nullopt, GetParam().p4info));

  // The table should be clear for both sessions after setting up a new session.
  ASSERT_OK(pdpi::CheckNoTableEntries(sut_p4rt_session.get()));
  ASSERT_OK(pdpi::CheckNoTableEntries(session2.get()));
}

// Ensures that a GNMI Config can be pushed even with programmed flows already
// on the switch.
// TODO: Re-enable once pushing a config from the switch, to the
// switch is supported.
TEST_P(SmokeTestFixture, DISABLED_PushGnmiConfigWithFlows) {
  thinkit::MirrorTestbed& testbed =
      GetParam().mirror_testbed->GetMirrorTestbed();

  // Initialize the connection, clear table entries, and push GNMI
  // configuration (if given) for the SUT and Control switch.
  std::unique_ptr<pdpi::P4RuntimeSession> sut_p4rt_session,
      control_switch_p4rt_session;
  ASSERT_OK_AND_ASSIGN(
      std::tie(sut_p4rt_session, control_switch_p4rt_session),
      pins_test::ConfigureSwitchPairAndReturnP4RuntimeSessionPair(
          testbed.Sut(), testbed.ControlSwitch(), GetParam().gnmi_config,
          GetParam().p4info));

  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info ir_p4info,
                       pdpi::GetIrP4Info(*sut_p4rt_session));

  // All tables should be clear after setup.
  ASSERT_OK(pdpi::CheckNoTableEntries(sut_p4rt_session.get()));
  // Get a gNMI config from the switch to use for testing.
  ASSERT_OK_AND_ASSIGN(auto sut_gnmi_stub, testbed.Sut().CreateGnmiStub());
  ASSERT_OK_AND_ASSIGN(std::string sut_gnmi_config,
                       pins_test::GetGnmiConfig(*sut_gnmi_stub));

  // Pushing a Gnmi Config is OK when tables are cleared.
  ASSERT_OK(pins_test::PushGnmiConfig(testbed.Sut(), sut_gnmi_config));

  // Sets up an example table entry.
  const sai::TableEntry pd_entry = gutil::ParseProtoOrDie<sai::TableEntry>(
      R"pb(
        router_interface_table_entry {
          match { router_interface_id: "router-interface-1" }
          action {
            set_port_and_src_mac { port: "1" src_mac: "02:2a:10:00:00:03" }
          }
        }
      )pb");
  ASSERT_OK_AND_ASSIGN(p4::v1::TableEntry pi_entry,
                       pdpi::PartialPdTableEntryToPiTableEntry(
		       ir_p4info, pd_entry));

  ASSERT_OK(pdpi::InstallPiTableEntries(sut_p4rt_session.get(),
                                        ir_p4info, {pi_entry}));

  // Pushing the same Gnmi Config is also OK when entries are programmed.
  ASSERT_OK(pins_test::PushGnmiConfig(testbed.Sut(), sut_gnmi_config));
}

TEST_P(SmokeTestFixture, DeleteReferencedNeighborNotOk) {
  thinkit::MirrorTestbed& testbed =
      GetParam().mirror_testbed->GetMirrorTestbed();

  // Initialize the connection, clear table entries, and push GNMI
  // configuration (if given) for the SUT and Control switch.
  std::unique_ptr<pdpi::P4RuntimeSession> sut_p4rt_session,
      control_switch_p4rt_session;
  ASSERT_OK_AND_ASSIGN(
      std::tie(sut_p4rt_session, control_switch_p4rt_session),
      pins_test::ConfigureSwitchPairAndReturnP4RuntimeSessionPair(
          testbed.Sut(), testbed.ControlSwitch(), GetParam().gnmi_config,
          GetParam().p4info));

  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info ir_p4info,
                       pdpi::GetIrP4Info(*sut_p4rt_session));

  constexpr absl::string_view kRifId = "rif";
  constexpr absl::string_view kNeighborId = "::1";

  ASSERT_OK_AND_ASSIGN(
      p4::v1::Update insert_and_delete_neighbor_update,
      pins::NeighborTableUpdate(ir_p4info, p4::v1::Update::INSERT, kRifId,
                                kNeighborId, /*dst_mac=*/"01:02:03:04:05:06"));
  ASSERT_OK_AND_ASSIGN(const p4::v1::Update rif_update,
                       pins::RouterInterfaceTableUpdate(
                           ir_p4info, p4::v1::Update::INSERT, kRifId,
                           /*port=*/"1", /*src_mac=*/"00:02:03:04:05:06"));

  // Install RIF then Neighbor entries.
  ASSERT_OK(pdpi::SendPiUpdates(
      sut_p4rt_session.get(), {rif_update, insert_and_delete_neighbor_update}));

  // Install either a tunnel or a nexthop depending on if tunnels are supported.
  if (GetParam().does_not_support_gre_tunnels) {
    ASSERT_OK_AND_ASSIGN(
        const p4::v1::Update nexthop_update,
        pins::NexthopTableUpdate(ir_p4info, p4::v1::Update::INSERT,
                                  /*nexthop_id=*/"nid", kRifId, kNeighborId));
    ASSERT_OK(pdpi::SendPiUpdates(sut_p4rt_session.get(), {nexthop_update}));
  } else {
    ASSERT_OK_AND_ASSIGN(
        const p4::v1::Update tunnel_update,
        pins::TunnelTableUpdate(
            ir_p4info, p4::v1::Update::INSERT, /*tunnel_id=*/"tid",
            /*encap_dst_ip=*/kNeighborId, /*encap_src_ip=*/"::2", kRifId));
    ASSERT_OK(pdpi::SendPiUpdates(sut_p4rt_session.get(), {tunnel_update}));
  }

  // Cannot delete the neighbor table entry because it is used by the tunnel
  // entry or the nexthop entry.
  insert_and_delete_neighbor_update.set_type(p4::v1::Update::DELETE);
  EXPECT_THAT(pdpi::SendPiUpdates(sut_p4rt_session.get(),
                                  {insert_and_delete_neighbor_update}),
              Not(IsOk()));

  // We should always be able to re-install entries read from the switch.
  // Otherwise, the switch is in a corrupted state.
  ASSERT_OK_AND_ASSIGN(const pdpi::IrTableEntries read_entries,
                       pdpi::ReadIrTableEntries(*sut_p4rt_session));
  ASSERT_OK(pdpi::ClearEntities(*sut_p4rt_session));
  EXPECT_OK(pdpi::InstallIrTableEntries(*sut_p4rt_session, read_entries));
}

TEST_P(SmokeTestFixture, DeleteReferencedMulticastRifNotOk) {
  thinkit::MirrorTestbed& testbed =
      GetParam().mirror_testbed->GetMirrorTestbed();

  // Initialize the connection, clear table entries, and push GNMI
  // configuration (if given) for the SUT and Control switch.
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<pdpi::P4RuntimeSession> sut_p4rt_session,
      pins_test::ConfigureSwitchAndReturnP4RuntimeSession(
          testbed.Sut(), GetParam().gnmi_config, GetParam().p4info));

  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info ir_p4info,
                       pdpi::GetIrP4Info(*sut_p4rt_session));

  constexpr absl::string_view kVrf = "vrf";
  constexpr int kMulticastGroupId = 1;
  const sai::Replica kReplica = sai::Replica{
      .egress_port = "1",
      .instance = 0,
  };

  // Install a multicast route with:
  // - A multicast RIF
  // - A multicast group referring to that RIF.
  // - An Ipv6 multicast table entry referring to that group.
  // - Other auxiliary entries
  ASSERT_OK(sai::EntryBuilder()
                .AddVrfEntry(kVrf)
                // Makes the ipv6_dst "ff05::".
                .AddMulticastRoute(kVrf, netaddr::Ipv6Address(0xff05),
                                   kMulticastGroupId)
                .AddMulticastGroupEntry(kMulticastGroupId, {kReplica})
                .AddMrifEntryRewritingSrcMac(
                    kReplica.egress_port, kReplica.instance,
                    netaddr::MacAddress(0x22, 0x22, 0x22, 0x22, 0x22, 0x22))
                .InstallDedupedEntities(*sut_p4rt_session));

  // Try to delete entities that are referenced by other entities.
  pdpi::IrEntity multicast_rif_entity;
  pdpi::IrEntity multicast_group_entity;
  ASSERT_OK_AND_ASSIGN(const pdpi::IrEntities entities,
                       pdpi::ReadIrEntities(*sut_p4rt_session));
  for (const pdpi::IrEntity& entity : entities.entities()) {
    if (entity.has_packet_replication_engine_entry()) {
      multicast_group_entity = entity;
    } else if (entity.has_table_entry() &&
               entity.table_entry().table_name() ==
                   "multicast_router_interface_table") {
      multicast_rif_entity = entity;
    }
  }
  ASSERT_TRUE(multicast_rif_entity.has_table_entry())
      << "Could not find multicast RIF on switch after successfully installing "
         "it.";
  ASSERT_TRUE(multicast_group_entity.has_packet_replication_engine_entry())
      << "Could not find multicast group on switch after successfully "
         "installing it.";

  // Cannot delete the multicast RIF because it is used by the multicast group.
  EXPECT_THAT(pdpi::DeleteIrEntity(*sut_p4rt_session, multicast_rif_entity),
              Not(IsOk()));
  // Cannot delete the multicast group because it is used by the IPv6 route.
  EXPECT_THAT(pdpi::DeleteIrEntity(*sut_p4rt_session, multicast_group_entity),
              Not(IsOk()));

  // We should always be able to delete and re-install entities read from the
  // switch. Otherwise, the switch is in a corrupted state.
  ASSERT_OK_AND_ASSIGN(const pdpi::IrEntities read_entities,
                       pdpi::ReadIrEntities(*sut_p4rt_session));
  ASSERT_OK(pdpi::ClearEntities(*sut_p4rt_session));
  EXPECT_OK(pdpi::InstallIrEntities(*sut_p4rt_session, read_entities));
}

}  // namespace
}  // namespace pins
