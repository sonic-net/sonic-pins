// TDD: FourwardPinsSwitch behaves like a real PINS switch.
//
// Auxiliary entries (PRE clone sessions, VLAN membership, etc.) are
// installed transparently and invisible to the user. These tests verify
// the contract by checking that behavior changes with auxiliary entries
// and that they don't appear in P4Runtime reads.
//
// These tests are expected to FAIL until the pre-packet hook and
// auxiliary entry reconciliation are implemented.

#include "fourward/fourward_switch.h"

#include <memory>
#include <string>

#include "gtest/gtest.h"
#include "gutil/io.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_runtime/p4_runtime_session.h"
#include "p4_infra/p4_runtime/p4_runtime_session_extras.h"
#include "packetlib/packetlib.h"
#include "packetlib/packetlib.pb.h"
#include "sai_p4/instantiations/google/test_tools/test_entries.h"
#include "tools/cpp/runfiles/runfiles.h"

namespace dvaas {
namespace {

using ::bazel::tools::cpp::runfiles::Runfiles;
using ::gutil::ParseProtoOrDie;

p4::v1::ForwardingPipelineConfig LoadFourwardConfig() {
  std::string error;
  std::unique_ptr<Runfiles> runfiles(Runfiles::CreateForTest(&error));
  EXPECT_NE(runfiles, nullptr) << "Failed to create Runfiles: " << error;
  absl::StatusOr<std::string> contents = gutil::ReadFile(
      runfiles->Rlocation("_main/fourward/sai_middleblock_fourward.binpb"));
  EXPECT_OK(contents);
  p4::v1::ForwardingPipelineConfig config;
  EXPECT_TRUE(config.ParseFromString(*contents));
  return config;
}

std::string SerializeTestPacket(absl::string_view textproto) {
  packetlib::Packet packet = ParseProtoOrDie<packetlib::Packet>(textproto);
  CHECK_OK(packetlib::PadPacketToMinimumSize(packet));
  CHECK_OK(packetlib::UpdateAllComputedFields(packet));
  absl::StatusOr<std::string> serialized = packetlib::SerializePacket(packet);
  CHECK_OK(serialized);
  return *serialized;
}

constexpr absl::string_view kUdpPacket = R"pb(
  headers {
    ethernet_header {
      ethernet_destination: "02:02:02:02:02:02"
      ethernet_source: "00:aa:bb:cc:dd:ee"
      ethertype: "0x0800"
    }
  }
  headers {
    ipv4_header {
      version: "0x4"
      ihl: "0x5"
      dscp: "0x00"
      ecn: "0x0"
      identification: "0x0000"
      flags: "0x0"
      fragment_offset: "0x0000"
      ttl: "0x40"
      protocol: "0x11"
      ipv4_source: "192.168.1.1"
      ipv4_destination: "10.1.2.3"
    }
  }
  headers { udp_header { source_port: "0x0000" destination_port: "0x0000" } }
)pb";

// ---------------------------------------------------------------------------
// Litmus test 1: ACL trap requires PRE auxiliary entry
// ---------------------------------------------------------------------------

// An ACL trap entry punts matching packets to the CPU via the Packet
// Replication Engine. Without the PRE clone session (an auxiliary entry),
// the punt silently fails. With it, the packet arrives as a PacketIn.
TEST(FourwardPinsSwitchTest, DISABLED_AclTrapPuntsPacketWithAuxEntries) {
  p4::v1::ForwardingPipelineConfig config = LoadFourwardConfig();
  ASSERT_OK_AND_ASSIGN(FourwardSwitch pins_switch, FourwardSwitch::Create());
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<p4_runtime::P4RuntimeSession> session,
      p4_runtime::P4RuntimeSession::Create(pins_switch));
  ASSERT_OK(p4_runtime::SetMetadataAndSetForwardingPipelineConfig(
      session.get(),
      p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
      config));

  // Install only an ACL trap entry — no manual PRE or auxiliary entries.
  ASSERT_OK(sai::EntryBuilder()
                .AddEntryPuntingAllPackets(sai::PuntAction::kTrap)
                .InstallDedupedEntities(*session));

  // Send a packet via the switch's dataplane.
  // TODO: Use switch's Dataplane service once exposed.

  // Verify: packet should arrive as PacketIn (punt succeeded).
  // Without auxiliary entries, this would fail (no PRE clone session).
  p4::v1::StreamMessageResponse response;
  ASSERT_TRUE(session->StreamChannelRead(response, absl::Seconds(5)))
      << "Expected PacketIn from ACL trap, but no response received. "
         "The PRE clone session (auxiliary entry) is likely missing.";
  EXPECT_TRUE(response.has_packet())
      << "Expected PacketIn, got: " << response.DebugString();
}

// ---------------------------------------------------------------------------
// Litmus test 2: L3 forwarding requires VLAN auxiliary entries
// ---------------------------------------------------------------------------

// L3 forwarding requires VLAN check disable entries. Without them,
// packets are dropped before reaching the routing tables.
TEST(FourwardPinsSwitchTest,
     DISABLED_L3ForwardingWorksWithAuxEntries) {
  p4::v1::ForwardingPipelineConfig config = LoadFourwardConfig();
  ASSERT_OK_AND_ASSIGN(FourwardSwitch pins_switch, FourwardSwitch::Create());
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<p4_runtime::P4RuntimeSession> session,
      p4_runtime::P4RuntimeSession::Create(pins_switch));
  ASSERT_OK(p4_runtime::SetMetadataAndSetForwardingPipelineConfig(
      session.get(),
      p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
      config));

  // Install ONLY forwarding entries — no VLAN disable entries.
  ASSERT_OK(sai::EntryBuilder()
                .AddEntriesForwardingIpPacketsToGivenPort("1")
                .InstallDedupedEntities(*session));

  // Send a packet via the switch's dataplane.
  // TODO: Use switch's Dataplane service once exposed.
  // Verify: packet should be forwarded to port 1, not dropped by VLAN.
}

// ---------------------------------------------------------------------------
// Litmus test 3: Auxiliary entries are invisible to P4Runtime reads
// ---------------------------------------------------------------------------

// A wildcard read by a sdn_controller session should NOT return
// auxiliary entries installed by the pins_auxiliary role.
TEST(FourwardPinsSwitchTest,
     DISABLED_AuxiliaryEntriesInvisibleToReads) {
  p4::v1::ForwardingPipelineConfig config = LoadFourwardConfig();
  ASSERT_OK_AND_ASSIGN(FourwardSwitch pins_switch, FourwardSwitch::Create());
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<p4_runtime::P4RuntimeSession> session,
      p4_runtime::P4RuntimeSession::Create(pins_switch));
  ASSERT_OK(p4_runtime::SetMetadataAndSetForwardingPipelineConfig(
      session.get(),
      p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
      config));

  // Install one user entry.
  ASSERT_OK(sai::EntryBuilder()
                .AddEntryPuntingAllPackets(sai::PuntAction::kTrap)
                .InstallDedupedEntities(*session));

  // Trigger auxiliary entry reconciliation (via a packet or explicit call).
  // TODO: Send a packet to trigger the pre-packet hook.

  // Read all entries as sdn_controller.
  p4::v1::ReadRequest read_request;
  read_request.set_device_id(pins_switch.DeviceId());
  read_request.add_entities()->mutable_table_entry();
  ASSERT_OK_AND_ASSIGN(p4::v1::ReadResponse read_response,
                       session->Read(read_request));

  // Verify: only the user-installed ACL entry should be visible.
  // Auxiliary entries (PRE clone session, VLAN entries, etc.) should NOT
  // appear in the read response.
  for (const p4::v1::Entity& entity : read_response.entities()) {
    if (entity.has_table_entry()) {
      // None of the returned entries should be auxiliary entries.
      // TODO: Check against known auxiliary table IDs.
    }
  }

  // At minimum, the user's ACL entry should be present.
  EXPECT_GT(read_response.entities_size(), 0)
      << "Expected at least the user-installed ACL entry";
}

// ---------------------------------------------------------------------------
// Litmus test 4: With vs without — prove auxiliary entries are the cause
// ---------------------------------------------------------------------------

// Same switch, same ACL trap entry, same packet. First inject WITHOUT
// auxiliary entries (hook disabled or not yet triggered) and verify the
// punt fails. Then inject WITH auxiliary entries and verify it succeeds.
// This proves causality — the auxiliary entries are what makes it work.
TEST(FourwardPinsSwitchTest,
     DISABLED_AclTrapFailsWithoutAuxEntriesSucceedsWith) {
  p4::v1::ForwardingPipelineConfig config = LoadFourwardConfig();
  ASSERT_OK_AND_ASSIGN(FourwardSwitch pins_switch, FourwardSwitch::Create());
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<p4_runtime::P4RuntimeSession> session,
      p4_runtime::P4RuntimeSession::Create(pins_switch));
  ASSERT_OK(p4_runtime::SetMetadataAndSetForwardingPipelineConfig(
      session.get(),
      p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
      config));

  // Install only an ACL trap entry.
  ASSERT_OK(sai::EntryBuilder()
                .AddEntryPuntingAllPackets(sai::PuntAction::kTrap)
                .InstallDedupedEntities(*session));

  // Phase 1: WITHOUT auxiliary entries.
  // TODO: Inject packet via Dataplane service with hook disabled.
  // Verify: no PacketIn (punt fails silently — no PRE clone session).
  p4::v1::StreamMessageResponse response;
  EXPECT_FALSE(session->StreamChannelRead(response, absl::Seconds(2)))
      << "Expected NO PacketIn without auxiliary entries, but got: "
      << response.DebugString();

  // Phase 2: WITH auxiliary entries.
  // TODO: Inject same packet with hook enabled (or call reconcile).
  // Verify: PacketIn arrives (punt succeeds — PRE clone session exists).
  ASSERT_TRUE(session->StreamChannelRead(response, absl::Seconds(5)))
      << "Expected PacketIn with auxiliary entries, but none received.";
  EXPECT_TRUE(response.has_packet());
}

}  // namespace
}  // namespace dvaas
