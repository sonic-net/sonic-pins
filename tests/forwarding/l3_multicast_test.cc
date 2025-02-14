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
#include "tests/forwarding/l3_multicast_test.h"

#include <memory>
#include <optional>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"  // IWYU pragma: keep
#include "lib/gnmi/gnmi_helper.h"
#include "lib/gnmi/openconfig.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/netaddr/ipv4_address.h"
#include "p4_pdpi/netaddr/ipv6_address.h"
#include "p4_pdpi/netaddr/mac_address.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "sai_p4/instantiations/google/test_tools/test_entries.h"
#include "tests/lib/switch_test_setup_helpers.h"
#include "thinkit/switch.h"

namespace pins_test {
namespace {

using ::gutil::StatusIs;
using ::testing::AllOf;
using ::testing::HasSubstr;

// Common programming parameters.
constexpr absl::string_view kDefaultMulticastVrf = "vrf-mcast";
constexpr netaddr::MacAddress kOriginalSrcMacAddress(0x00, 0x22, 0x33, 0x44,
                                                     0x55, 0x66);
constexpr int kDefaultInstance = 0;

// Pair of port ID and instance.
using ReplicaPair = std::pair<std::string, int>;

// IPv4 addresses of the form 226.10.#.#.  The last two bytes are computed
// based on the multicast group ID.
absl::StatusOr<netaddr::Ipv4Address> GetIpv4AddressForReplica(
    int multicast_group_id) {
  if (multicast_group_id >= 0 && multicast_group_id < 0xffff) {
    return netaddr::Ipv4Address(226, 10, (multicast_group_id + 1) >> 8,
                                (multicast_group_id + 1) & 0xff);
  } else {
    return absl::FailedPreconditionError(
        absl::StrCat("Multicast group ID '", multicast_group_id,
                     "' is larger than test's maximum value of ", 0xfffe));
  }
}

// IPv6 addresses of the form ff00:0:1111:2222:3333:4444:5555.#.  The last
// 16-bits of the address are based on the multicast group ID.
absl::StatusOr<netaddr::Ipv6Address> GetIpv6AddressForReplica(
    int multicast_group_id) {
  if (multicast_group_id >= 0 && (multicast_group_id + 1) < 0xffff) {
    return netaddr::Ipv6Address(0xff00, 0x0, 0x1111, 0x2222, 0x3333, 0x4444,
                                0x5555, multicast_group_id + 1);
  } else {
    return absl::FailedPreconditionError(
        absl::StrCat("Multicast group ID '", multicast_group_id,
                     "' is larger than test's maximum value of ", 0xfffe));
  }
}

absl::StatusOr<std::vector<std::string>> GetNUpInterfaceIDs(
    thinkit::Switch& device, int num_interfaces) {
  // The test fixture pushes a new config during setup so we give the switch a
  // few minutes to converge before failing to report no valid ports.
  absl::Duration time_limit = absl::Minutes(3);
  absl::Time stop_time = absl::Now() + time_limit;
  std::vector<std::string> port_names;
  while (port_names.size() < num_interfaces) {
    if (absl::Now() > stop_time) {
      return absl::FailedPreconditionError(
          absl::StrCat("Could not find ", num_interfaces, " interfaces in ",
                       absl::FormatDuration(time_limit), "."));
    }
    ASSIGN_OR_RETURN(auto gnmi_stub, device.CreateGnmiStub());
    ASSIGN_OR_RETURN(port_names,
                     pins_test::GetUpInterfacesOverGnmi(
                         *gnmi_stub, pins_test::InterfaceType::kSingleton));
  }
  ASSIGN_OR_RETURN(auto gnmi_stub, device.CreateGnmiStub());
  ASSIGN_OR_RETURN(auto port_id_by_name,
                   GetAllInterfaceNameToPortId(*gnmi_stub));

  // Return encoded port ID as result.
  std::vector<std::string> result;
  for (const auto& port_name : port_names) {
    if (auto it = port_id_by_name.find(port_name);
        it != port_id_by_name.end()) {
      result.push_back(it->second);
    }
  }
  return result;
}

// Add table entries for multicast_router_interface_table.
absl::StatusOr<std::vector<p4::v1::Entity>> CreateRifTableEntities(
    const pdpi::IrP4Info& ir_p4info, const std::string& port_id,
    const int instance, const netaddr::MacAddress& src_mac) {
  ASSIGN_OR_RETURN(std::vector<p4::v1::Entity> entities,
                   sai::EntryBuilder()
                       .AddMulticastRouterInterfaceEntry(
                           {.multicast_replica_port = port_id,
                            .multicast_replica_instance = instance,
                            .src_mac = src_mac})
                       .LogPdEntries()
                       .GetDedupedPiEntities(ir_p4info,
                                             /*allow_unsupported=*/true));
  return entities;
}

// Add packet replication engine entries.
absl::StatusOr<std::vector<p4::v1::Entity>> CreateMulticastGroupEntities(
    const pdpi::IrP4Info& ir_p4info, int multicast_group_id,
    const std::vector<ReplicaPair>& replicas) {
  std::vector<sai::Replica> sai_replicas;
  for (const auto& [port, instance] : replicas) {
    sai_replicas.push_back(
        sai::Replica{.egress_port = port, .instance = instance});
  }

  ASSIGN_OR_RETURN(std::vector<p4::v1::Entity> entities,
                   sai::EntryBuilder()
                       .AddMulticastGroupEntry(multicast_group_id, sai_replicas)
                       .LogPdEntries()
                       .GetDedupedPiEntities(ir_p4info));
  return entities;
}

// Add table entries for ipv4_multicast_table.
absl::StatusOr<std::vector<p4::v1::Entity>> CreateIpv4MulticastTableEntities(
    const pdpi::IrP4Info& ir_p4info, const std::string& vrf_id,
    const netaddr::Ipv4Address& ip_address, int multicast_group_id) {
  ASSIGN_OR_RETURN(
      std::vector<p4::v1::Entity> entities,
      sai::EntryBuilder()
          .AddMulticastRoute(vrf_id, ip_address, multicast_group_id)
          .LogPdEntries()
          .GetDedupedPiEntities(ir_p4info,
                                /*allow_unsupported=*/true));
  return entities;
}

// Add table entries for ipv6_multicast_table.
absl::StatusOr<std::vector<p4::v1::Entity>> CreateIpv6MulticastTableEntities(
    const pdpi::IrP4Info& ir_p4info, const std::string& vrf_id,
    const netaddr::Ipv6Address& ip_address, int multicast_group_id) {
  ASSIGN_OR_RETURN(
      std::vector<p4::v1::Entity> entities,
      sai::EntryBuilder()
          .AddMulticastRoute(vrf_id, ip_address, multicast_group_id)
          .LogPdEntries()
          .GetDedupedPiEntities(ir_p4info,
                                /*allow_unsupported=*/true));
  return entities;
}

absl::Status ProgramPiEntities(pdpi::P4RuntimeSession& session,
                               const pdpi::IrP4Info& ir_p4info,
                               absl::Span<const p4::v1::Entity> pi_entities,
                               const p4::v1::Update_Type& update_type) {
  std::vector<p4::v1::Update> pi_updates =
      pdpi::CreatePiUpdates(pi_entities, update_type);
  // We serialize the programming call, because the call to
  // pdpi::SequencePiUpdatesIntoWriteRequests cannot handle packet replication
  // engine entity types.  This function may see a mix of table entries
  // and packet replication engine entries.
  for (auto& pi_update : pi_updates) {
    std::vector<p4::v1::WriteRequest> write_requests;
    p4::v1::WriteRequest write_request;
    *write_request.add_updates() = pi_update;
    write_requests.push_back(std::move(write_request));
    RETURN_IF_ERROR(
        pdpi::SetMetadataAndSendPiWriteRequests(&session, write_requests));
  }
  return absl::OkStatus();
}

TEST_P(L3MulticastTestFixture, InsertMulticastGroupBeforeRifFails) {
  const int kNumberRifs = 2;
  ASSERT_OK_AND_ASSIGN(
      auto sut_ports_ids,
      GetNUpInterfaceIDs(GetParam().mirror_testbed->GetMirrorTestbed().Sut(),
                         kNumberRifs));

  // If we do not have a RIF, we cannot create multicast group members.
  std::vector<ReplicaPair> replicas;
  for (int r = 0; r < kNumberRifs; ++r) {
    const std::string& port_id = sut_ports_ids.at(r);
    replicas.push_back(std::make_pair(port_id, kDefaultInstance));
  }
  ASSERT_OK_AND_ASSIGN(auto entities, CreateMulticastGroupEntities(
                                          ir_p4info_,
                                          /*multicast_group_id=*/2, replicas));
  EXPECT_THAT(
      ProgramPiEntities(*sut_p4rt_session_, ir_p4info_, entities,
                        p4::v1::Update::INSERT),
      StatusIs(
          absl::StatusCode::kUnknown,
          AllOf(HasSubstr("#1: NOT_FOUND"),
                HasSubstr("[OrchAgent] Multicast group member"),
                HasSubstr("does not have an associated RIF available yet"))));
}

TEST_P(L3MulticastTestFixture,
       InsertIpMulticastEntryBeforeMulticastGroupFails) {
  // Create a VRF.
  ASSERT_OK_AND_ASSIGN(std::vector<p4::v1::Entity> vrf_entities,
                       sai::EntryBuilder()
                           .AddVrfEntry(kDefaultMulticastVrf)
                           .LogPdEntries()
                           .GetDedupedPiEntities(ir_p4info_));
  EXPECT_OK(ProgramPiEntities(*sut_p4rt_session_, ir_p4info_, vrf_entities,
                              p4::v1::Update::INSERT));

  // If we have not created a multicast group yet, we cannot create an IPMC
  // entry.
  const int kMulticastGroupId = 7;
  ASSERT_OK_AND_ASSIGN(auto ipv4_address,
                       GetIpv4AddressForReplica(kMulticastGroupId));

  ASSERT_OK_AND_ASSIGN(auto entities_v4,
                       CreateIpv4MulticastTableEntities(
                           ir_p4info_, std::string(kDefaultMulticastVrf),
                           ipv4_address, kMulticastGroupId));

  EXPECT_THAT(
      ProgramPiEntities(*sut_p4rt_session_, ir_p4info_, entities_v4,
                        p4::v1::Update::INSERT),
      StatusIs(
          absl::StatusCode::kUnknown,
          AllOf(HasSubstr("#1: NOT_FOUND"),
                HasSubstr("[OrchAgent] No multicast group ID found for"))));
  // Clean up.
  EXPECT_OK(ProgramPiEntities(*sut_p4rt_session_, ir_p4info_, vrf_entities,
                              p4::v1::Update::DELETE));
}

TEST_P(L3MulticastTestFixture, DeleteNonexistentRifEntryFails) {
  // Unable to delete RIF entry that was not added.
  ASSERT_OK_AND_ASSIGN(
      auto entities,
      CreateRifTableEntities(ir_p4info_, /*port_id=*/"1", kDefaultInstance,
                             kOriginalSrcMacAddress));

  EXPECT_THAT(ProgramPiEntities(*sut_p4rt_session_, ir_p4info_, entities,
                                p4::v1::Update::DELETE),
              StatusIs(absl::StatusCode::kUnknown,
                       AllOf(HasSubstr("#1: NOT_FOUND"),
                             HasSubstr("given key does not exist in table "
                                       "'multicast_router_interface_table'"))));
}

TEST_P(L3MulticastTestFixture, DeleteNonexistentMulticastGroupFails) {
  const int kNumberRifs = 2;
  ASSERT_OK_AND_ASSIGN(
      auto sut_ports_ids,
      GetNUpInterfaceIDs(GetParam().mirror_testbed->GetMirrorTestbed().Sut(),
                         kNumberRifs));
  std::vector<ReplicaPair> replicas;
  for (int r = 0; r < kNumberRifs; ++r) {
    const std::string& port_id = sut_ports_ids.at(r);
    replicas.push_back(std::make_pair(port_id, kDefaultInstance));
  }

  // Unable to delete multicast group entry that was not added.
  ASSERT_OK_AND_ASSIGN(auto entities, CreateMulticastGroupEntities(
                                          ir_p4info_,
                                          /*multicast_group_id=*/1, replicas));
  EXPECT_THAT(
      ProgramPiEntities(*sut_p4rt_session_, ir_p4info_, entities,
                        p4::v1::Update::DELETE),
      StatusIs(
          absl::StatusCode::kUnknown,
          AllOf(
              HasSubstr("#1: NOT_FOUND"),
              HasSubstr(
                  "entry with key of multicast group ID '1' does not exist"))));
}

TEST_P(L3MulticastTestFixture, DeleteNonexistentIpmcEntryFails) {
  // Unable to delete IPMC entry that was not added.
  const int kMulticastGroupId = 1;
  const std::string vrf_id = "vrf-mcast-1";
  ASSERT_OK_AND_ASSIGN(auto ipv4_address,
                       GetIpv4AddressForReplica(kMulticastGroupId));
  ASSERT_OK_AND_ASSIGN(auto ipv6_address,
                       GetIpv6AddressForReplica(kMulticastGroupId));

  ASSERT_OK_AND_ASSIGN(auto entities_v4, CreateIpv4MulticastTableEntities(
                                             ir_p4info_, vrf_id, ipv4_address,
                                             kMulticastGroupId));
  ASSERT_OK_AND_ASSIGN(auto entities_v6, CreateIpv6MulticastTableEntities(
                                             ir_p4info_, vrf_id, ipv6_address,
                                             kMulticastGroupId));

  EXPECT_THAT(ProgramPiEntities(*sut_p4rt_session_, ir_p4info_, entities_v4,
                                p4::v1::Update::DELETE),
              StatusIs(absl::StatusCode::kUnknown,
                       AllOf(HasSubstr("#1: NOT_FOUND"),
                             HasSubstr("given key does not exist in table "
                                       "'ipv4_multicast_table'"))));
  EXPECT_THAT(ProgramPiEntities(*sut_p4rt_session_, ir_p4info_, entities_v6,
                                p4::v1::Update::DELETE),
              StatusIs(absl::StatusCode::kUnknown,
                       AllOf(HasSubstr("#1: NOT_FOUND"),
                             HasSubstr("given key does not exist in table "
                                       "'ipv6_multicast_table'"))));
}

}  // namespace

void L3MulticastTestFixture::SetUp() {
  GetParam().mirror_testbed->SetUp();

  thinkit::MirrorTestbed& testbed =
      GetParam().mirror_testbed->GetMirrorTestbed();

  // Initialize the connection and clear table entries for the SUT and Control
  // switch.
  ASSERT_OK_AND_ASSIGN(
      std::tie(sut_p4rt_session_, control_switch_p4rt_session_),
      pins_test::ConfigureSwitchPairAndReturnP4RuntimeSessionPair(
          testbed.Sut(), testbed.ControlSwitch(), GetParam().gnmi_config,
          GetParam().p4info));

  ASSERT_OK_AND_ASSIGN(ir_p4info_, pdpi::CreateIrP4Info(*GetParam().p4info));
}

}  // namespace pins_test
