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

#include <optional>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/log/check.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "gutil/testing.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session_extras.h"
#include "p4_pdpi/packetlib/packetlib.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "platforms/networking/p4/p4_infra/bmv2/bmv2.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "sai_p4/instantiations/google/test_tools/set_up_bmv2.h"
#include "sai_p4/instantiations/google/test_tools/test_entries.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"

namespace pins {
namespace {

using ::orion::p4::test::Bmv2;
using ::testing::ElementsAre;
using ::testing::Key;

using PacketsByPort = absl::flat_hash_map<int, packetlib::Packets>;

void PreparePacketOrDie(packetlib::Packet &packet) {
  CHECK_OK(packetlib::PadPacketToMinimumSize(packet).status()); // Crash OK.
  CHECK_OK(
      packetlib::UpdateMissingComputedFields(packet).status()); // Crash OK.
}

packetlib::Packet GetIpv4PacketOrDie() {
  auto packet = gutil::ParseProtoOrDie<packetlib::Packet>(R"pb(
    headers {
      ethernet_header {
        ethernet_destination: "02:03:04:05:06:07"
        ethernet_source: "00:01:02:03:04:05"
        ethertype: "0x0800"  # IPv4
      }
    }
    headers {
      ipv4_header {
        version: "0x4"
        ihl: "0x5"
        dscp: "0x1c"
        ecn: "0x0"
        identification: "0x0000"
        flags: "0x0"
        fragment_offset: "0x0000"
        ttl: "0x20"
        protocol: "0xfe"
        ipv4_source: "192.168.100.2"
        ipv4_destination: "192.168.100.1"
      }
    }
    payload: "Untagged IPv4 packet."
  )pb");
  PreparePacketOrDie(packet);
  return packet;
}

TEST(ExperimentalTorLoopbackTest, PacketsSentToLoopbackPortsGetRecirculated) {
  const sai::Instantiation kInstantiation =
      sai::Instantiation::kExperimentalTor;
  const pdpi::IrP4Info kIrP4Info = sai::GetIrP4Info(kInstantiation);
  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(kInstantiation));

  constexpr int kIngressPort = 4;
  constexpr int kLoobackPort = 5;
  constexpr int kEgressPort = 6;
  constexpr absl::string_view kLoobackPortProto = "\005";
  constexpr absl::string_view kEgressPortProto = "\006";

  constexpr absl::string_view kRedirectNexthopId = "redirect-nexthop";

  {
    // Install entries to send packets to kLoobackPort.
    // For packets ingressing from the kLoobackPort, send them to kEgressPort.
    // However, do NOT yet install the entry to make kLoobackPort a loopback
    // port.
    ASSERT_OK_AND_ASSIGN(
        std::vector<p4::v1::Entity> pi_entities,
        sai::EntryBuilder()
            .AddEntriesForwardingIpPacketsToGivenPort(kLoobackPortProto)
            .AddIngressAclEntryRedirectingToNexthop(
                kRedirectNexthopId,
                /*in_port_match=*/kLoobackPortProto)
            .AddNexthopRifNeighborEntries(kRedirectNexthopId, kEgressPortProto)
            .LogPdEntries()
            .GetDedupedPiEntities(kIrP4Info, /*allow_unsupported=*/true));
    ASSERT_OK(pdpi::InstallPiEntities(bmv2.P4RuntimeSession(), pi_entities));

    // Inject a test packet to kIngressPort.
    ASSERT_OK_AND_ASSIGN(PacketsByPort output_by_port,
                         bmv2.SendPacket(kIngressPort, GetIpv4PacketOrDie()));
    // The packet must be forwarded to kLoobackPort.
    ASSERT_THAT(output_by_port, ElementsAre(Key(kLoobackPort)));
  }

  {
    // Now install an entry to make kLoobackPort a loopback port.
    ASSERT_OK_AND_ASSIGN(
        std::vector<p4::v1::Entity> pi_entities,
        sai::EntryBuilder()
            .AddEgressPortLoopbackEntry(kLoobackPortProto)
            .LogPdEntries()
            .GetDedupedPiEntities(kIrP4Info, /*allow_unsupported=*/true));
    ASSERT_OK(pdpi::InstallPiEntities(bmv2.P4RuntimeSession(), pi_entities));

    // Inject a test packet to kIngressPort.
    ASSERT_OK_AND_ASSIGN(PacketsByPort output_by_port,
                         bmv2.SendPacket(kIngressPort, GetIpv4PacketOrDie()));
    // The packet must be (looped back and eventually) forwarded to kEgressPort.
    ASSERT_THAT(output_by_port, ElementsAre(Key(kEgressPort)));
  }
}

} // namespace
} // namespace pins
