// Copyright 2025 Google LLC
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

#include "tests/forwarding/acl_feature_test.h"

#include <memory>
#include <optional>
#include <string>
#include <tuple>
#include <vector>

#include "absl/log/check.h"
#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "dvaas/dataplane_validation.h"
#include "dvaas/test_vector.h"
#include "dvaas/validation_result.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status.h"  // IWYU pragma: keep
#include "gutil/status.h"
#include "gutil/status_matchers.h"  // IWYU pragma: keep
#include "gutil/testing.h"
#include "lib/gnmi/gnmi_helper.h"
#include "net/google::protobuf/contrib/fixtures/proto-fixture-repository.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/p4_runtime_session_extras.h"
#include "p4_pdpi/packetlib/packetlib.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_pdpi/pd.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "sai_p4/instantiations/google/test_tools/test_entries.h"
#include "tests/lib/switch_test_setup_helpers.h"
#include "thinkit/mirror_testbed.h"

namespace pins_test {
namespace {

using ::google::protobuf::contrib::fixtures::ProtoFixtureRepository;

packetlib::Packet ParsePacketAndFillInComputedFields(
    const ProtoFixtureRepository& repo, absl::string_view packet_pb) {
  packetlib::Packet packet = repo.ParseTextOrDie<packetlib::Packet>(packet_pb);
  CHECK_OK(packetlib::PadPacketToMinimumSize(packet));
  CHECK_OK(packetlib::UpdateMissingComputedFields(packet));
  return packet;
}

// Setup ingress ACL forward all packets.
absl::Status SetUpIngressAclForwardingAllPackets(
    pdpi::P4RuntimeSession* p4_session, const pdpi::IrP4Info& ir_p4info) {
  sai::TableEntry pd_entry = gutil::ParseProtoOrDie<sai::TableEntry>(
      R"pb(
        acl_ingress_table_entry {
          match {}  # Wildcard match.
          action { acl_forward {} }
          priority: 1
        }
      )pb");

  ASSIGN_OR_RETURN(
      const p4::v1::TableEntry pi_entry,
      pdpi::PartialPdTableEntryToPiTableEntry(ir_p4info, pd_entry));
  return pdpi::InstallPiTableEntry(p4_session, pi_entry);
}

// Helper function to build a UDP packet
dvaas::PacketTestVector UdpPacket(std::string control_port,
                                  absl::string_view dst_mac,
                                  absl::string_view dst_ip,
                                  std::optional<sai::PuntAction> punt_action) {
  ProtoFixtureRepository repo;

  repo.RegisterValue("@payload", dvaas::MakeTestPacketTagFromUniqueId(1))
      .RegisterValue("@ingress_port", control_port)
      .RegisterValue("@egress_port", control_port)
      .RegisterValue("@dst_ip", dst_ip)
      .RegisterValue("@dst_mac", dst_mac)
      .RegisterValue("@ttl", "0x10")
      .RegisterValue("@decremented_ttl", "0x0f");

  dvaas::PacketTestVector test_vector =
      repo.RegisterSnippetOrDie<packetlib::Header>("@ethernet", R"pb(
            ethernet_header {
              ethernet_destination: @dst_mac,
              ethernet_source: "00:00:22:22:00:00"
              ethertype: "0x0800"  # Udp
            }
          )pb")
          .RegisterSnippetOrDie<packetlib::Header>("@ipv4", R"pb(
            ipv4_header {
              version: "0x4"
              dscp: "0x1b"
              ecn: "0x1"
              ihl: "0x5"
              identification: "0x0000"
              flags: "0x0"
              ttl: @ttl
              fragment_offset: "0x0000"
              # payload_length: filled in automatically.
              protocol: "0x11"
              ipv4_source: "10.0.0.8"
              ipv4_destination: @dst_ip
            }
          )pb")
          .RegisterSnippetOrDie<packetlib::Header>("@udp", R"pb(
            udp_header { source_port: "0x0014" destination_port: "0x000a" }
          )pb")
          .RegisterMessage("@input_packet", ParsePacketAndFillInComputedFields(
                                                repo,
                                                R"pb(
                                                  headers: @ethernet
                                                  headers: @ipv4
                                                  headers: @udp
                                                  payload: @payload
                                                )pb"))
          .RegisterMessage(
              "@output_packet", ParsePacketAndFillInComputedFields(repo, R"pb(
                headers: @ethernet {
                  ethernet_header {
                    ethernet_destination: "02:03:04:05:06:07"
                    ethernet_source: "00:01:02:03:04:05"
                  }
                }
                headers: @ipv4 { ipv4_header { ttl: @decremented_ttl } }
                headers: @udp
                payload: @payload
              )pb"))
          .ParseTextOrDie<dvaas::PacketTestVector>(R"pb(
            input {
              type: DATAPLANE
              packet { port: @ingress_port parsed: @input_packet }
            }
            acceptable_outputs {
              packets { port: @egress_port parsed: @output_packet }
              packet_ins { parsed: @output_packet }
            }
          )pb");

  for (dvaas::SwitchOutput& output :
       *test_vector.mutable_acceptable_outputs()) {
    if (!punt_action.has_value()) {
      output.clear_packet_ins();
    } else if (punt_action.value() == sai::PuntAction::kTrap) {
      output.clear_packets();
    }
  }
  return test_vector;
}

// Helper routine to install L3 route
absl::Status InstallL3Route(pdpi::P4RuntimeSession* switch_session,
                            pdpi::IrP4Info ir_p4info, std::string given_port,
                            std::optional<sai::PuntAction> punt_action) {
  std::vector<p4::v1::Entity> pi_entities;
  LOG(INFO) << "Installing L3 route";

  sai::EntryBuilder entry_builder =
      sai::EntryBuilder()
          .AddVrfEntry("vrf-1")
          .AddPreIngressAclEntryAssigningVrfForGivenIpType(
              "vrf-1", sai::IpVersion::kIpv4)
          .AddDefaultRouteForwardingAllPacketsToGivenPort(
              given_port, sai::IpVersion::kIpv4, "vrf-1")
          .AddEntryAdmittingAllPacketsToL3();

  if (punt_action.has_value()) {
    entry_builder.AddEntryPuntingAllPackets(punt_action.value());
  } else {
    RETURN_IF_ERROR(
        SetUpIngressAclForwardingAllPackets(switch_session, ir_p4info));
  }
  ASSIGN_OR_RETURN(
      pi_entities,
      entry_builder.LogPdEntries().GetDedupedPiEntities(ir_p4info));
  RETURN_IF_ERROR(pdpi::InstallPiEntities(*switch_session, pi_entities));
  return absl::OkStatus();
}

TEST_P(AclFeatureTestFixture, AclDenyAction) {
  const AclFeatureTestParams& params = GetParam();

  thinkit::MirrorTestbed& testbed =
      GetParam().mirror_testbed->GetMirrorTestbed();
  std::unique_ptr<pdpi::P4RuntimeSession> sut_p4rt_session,
      control_switch_p4rt_session;

  ASSERT_OK_AND_ASSIGN(
      std::tie(sut_p4rt_session, control_switch_p4rt_session),
      pins_test::ConfigureSwitchPairAndReturnP4RuntimeSessionPair(
          testbed.Sut(), testbed.ControlSwitch(), std::nullopt,
          GetParam().p4info));

  // Initialize the connection, clear table entries, and push GNMI
  // configuration (if given) for the SUT and Control switch.
  ASSERT_NE(sut_p4rt_session, nullptr);
  ASSERT_OK_AND_ASSIGN(
      p4::v1::GetForwardingPipelineConfigResponse sut_config,
      pdpi::GetForwardingPipelineConfig(sut_p4rt_session.get()));
  ASSERT_OK(testbed.Environment().StoreTestArtifact(
      "sut_p4Info.textproto", sut_config.config().p4info().DebugString()));
  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info sut_ir_p4info,
                       pdpi::CreateIrP4Info(sut_config.config().p4info()));

  ASSERT_OK(pdpi::ClearTableEntries(sut_p4rt_session.get()));

  // Get control ports to test on.
  ASSERT_OK_AND_ASSIGN(
      auto gnmi_stub_control,
      GetParam().mirror_testbed->GetMirrorTestbed().Sut().CreateGnmiStub());
  ASSERT_OK_AND_ASSIGN(std::string control_port,
                       pins_test::GetAnyUpInterfacePortId(*gnmi_stub_control));

  ASSERT_OK(InstallL3Route(sut_p4rt_session.get(), sut_ir_p4info, control_port,
                           params.punt_action));

  // remove the skip
  if (params.punt_action.has_value()) {
    // Run test with custom packet test vector.
    dvaas::DataplaneValidationParams dvaas_params = params.dvaas_params;
    dvaas_params.packet_test_vector_override = {
        UdpPacket(control_port, /*dst_mac=*/"00:aa:bb:cc:cc:dd",
                  /*dst_ip=*/"10.0.0.1", params.punt_action)};
    ASSERT_OK_AND_ASSIGN(
        dvaas::ValidationResult validation_result,
        GetParam().dvaas->ValidateDataplane(testbed, dvaas_params));

    // Log statistics and check that things succeeded.
    validation_result.LogStatistics();
    EXPECT_OK(validation_result.HasSuccessRateOfAtLeast(1.0));
  }
}

}  // namespace
}  // namespace pins_test
