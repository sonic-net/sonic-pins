// Copyright 2020 Google LLC
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
#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <memory>
#include <random>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/numeric/int128.h"
#include "absl/random/distributions.h"
#include "absl/random/random.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_split.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "gflags/gflags.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "google/protobuf/text_format.h"
#include "grpcpp/client_context.h"
#include "grpcpp/grpcpp.h"
#include "gtest/gtest.h"
#include "gutil/proto.h"
#include "gutil/collections.h"
#include "gutil/io.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/netaddr/ipv4_address.h"
#include "p4_pdpi/netaddr/ipv6_address.h"
#include "p4_pdpi/netaddr/mac_address.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "tests/lib/p4rt_fixed_table_programming_helper.h"

// The test can be run over a unix socket or TCP connection. In general (i.e.
// verify for your own enviornment) the socket will be unsecured while the TCP
// connection requires authentication.
//
// NOTE: if not using a socket then the server_address should be formated as
//       <IP_address>:9559.
DEFINE_string(server_address, "unix:/sock/p4rt.sock",
              "The address of the server to connect to");

DEFINE_bool(insecure, true, "Use insecure connection");
DEFINE_string(ca_cert, "/keys/ca_cert.lnk",
              "CA bundle file. Used when insecure is false");
DEFINE_string(cert, "/keys/gpins_test_user.cert",
              "Cert file. Used when insecure is false");
DEFINE_string(key, "/keys/gpins_test_user.key",
              "Key file. Used when insecure is false");
DEFINE_string(host_name, "",
              "Host name of the switch for validating the switch cert. Used "
              "when insecure is false");

// P4RT connections require a device and election ID to program flows. By
// default we use a time based election ID, and it shouldn't need to be set
// manually. However, the device ID should always be set and must match the
// machine being used.
//
// Device ID can generally be found in redis using:
//   $ redis-cli -n 4 hget "NODE_CFG|integrated_circuit0" "node-id"
DEFINE_int64(election_id, -1, "Election id to be used");
DEFINE_uint64(p4rt_device_id, 1, "P4RT device ID");

// The test will create and install a random set of routes (i.e. RIFs, VRFs, and
// NextHops) that the IPv4 flows can be programmed against. The time needed to
// install these flows is not included in the reported latency.
DEFINE_string(port_ids, "1", "A comma separated list of usable ports.");
DEFINE_int32(vrfs, 64, "The number of VRFs to install.");
DEFINE_int32(rifs, 64, "The number of router interfaces to install.");
DEFINE_int32(next_hops, 512, "The number of next-hop entries to install.");

// A run will automatically generate `number_batches` write requests each with
// `batch_size` updates (i.e. number_batches x batch_size total flows). Runtime
// only includes the P4RT Write() time, and not the generation.
DEFINE_int32(number_batches, 10, "Number of batches");
DEFINE_int32(batch_size, 1000, "Number of entries in each batch");

// By default we only run the IPv4 tests. However, because the tested tables
// don't overlap users can run multiple, and they will happen sequentially.
// Users should be careful when running multiple tests since the batch sizes are
// reused.
DEFINE_bool(run_ipv4, true, "Run IPv4 route latency tests.");
DEFINE_bool(run_ipv6, false, "Run IPv6 route latency tests.");
DEFINE_bool(run_wcmp, false, "Run IPv4 route latency tests.");

// Extra configs that affect WCMP batch sizes and flows.
DEFINE_int32(wcmp_members_per_group, 2,
             "Number of members in each WCMP group.");
DEFINE_int32(wcmp_total_group_weight, 2,
             "Total accumulated weight for all members in a WCMP group.");
DEFINE_bool(wcmp_update_weights_when_modifying, true,
            "Change weight values when modifying WCMP groups.");
DEFINE_bool(wcmp_update_nexthops_when_modifying, false,
            "Change nexthop values when modifying WCMP groups.");
DEFINE_bool(wcmp_increasing_weights, false,
            "Force the weight of a member to be >= the weight of the member "
            "that came before it.");

namespace p4rt_app {
namespace {

using P4RTUpdateByNameMap = absl::flat_hash_map<std::string, p4::v1::Update>;

template <typename T>
absl::StatusOr<absl::flat_hash_set<T>> RandomSetOfValues(absl::BitGen& bitgen,
                                                         const T& min_value,
                                                         const T& max_value,
                                                         int size) {
  // We use the max strikes count to prevent infinite loops.
  const int max_strikes = 2 * size;
  int strikes = 0;

  absl::flat_hash_set<T> result;
  while (result.size() < size) {
    if (!result.insert(absl::Uniform<T>(bitgen, min_value, max_value)).second) {
      strikes++;
    }
    if (strikes > max_strikes) {
      return absl::UnknownError(
          absl::StrCat("Could not generate ", size, " random values."));
    }
  }
  return result;
}

absl::StatusOr<std::vector<std::string>> GetKeys(
    const P4RTUpdateByNameMap& updates) {
  if (updates.empty()) {
    return absl::InvalidArgumentError("no updates were created");
  }
  std::vector<std::string> result;
  for (const auto& [name, _] : updates) {
    result.push_back(name);
  }
  return result;
}

void AppendUpdatesToWriteRequest(p4::v1::WriteRequest& request,
                                 const P4RTUpdateByNameMap& updates_by_name) {
  for (const auto& [_, update] : updates_by_name) {
    *request.add_updates() = update;
  }
}

std::string ReadFileOrEmpty(const std::string& path) {
  auto file = gutil::ReadFile(path);
  if (file.ok()) {
    return *file;
  }
  return "";
}

absl::StatusOr<std::unique_ptr<pdpi::P4RuntimeSession>> OpenP4RuntimeSession() {
  std::string server_address = FLAGS_server_address;
  uint64_t device_id = FLAGS_p4rt_device_id;
  int64_t election_id_high = FLAGS_election_id == -1
                                 ? absl::ToUnixSeconds(absl::Now())
                                 : FLAGS_election_id;

  LOG(INFO) << "Opening P4RT connection to: " << server_address;
  std::unique_ptr<p4::v1::P4Runtime::Stub> stub;
  if (FLAGS_insecure) {
    stub = pdpi::CreateP4RuntimeStub(FLAGS_server_address,
                                     grpc::InsecureChannelCredentials());
  } else {
    grpc::SslCredentialsOptions sslOpts;
    sslOpts.pem_root_certs = ReadFileOrEmpty(FLAGS_ca_cert);
    sslOpts.pem_private_key = ReadFileOrEmpty(FLAGS_key);
    sslOpts.pem_cert_chain = ReadFileOrEmpty(FLAGS_cert);
    stub = pdpi::CreateP4RuntimeStub(
        FLAGS_server_address, grpc::SslCredentials(sslOpts), FLAGS_host_name);
  }

  return pdpi::P4RuntimeSession::Create(
      std::move(stub), device_id,
      pdpi::P4RuntimeSessionOptionalArgs{
          .election_id = absl::MakeUint128(election_id_high, 0),
      });
}

// Checks the switch for any active P4Info configs and returns that, or defaults
// to a middleblock config.
absl::StatusOr<pdpi::IrP4Info> GetExistingP4InfoOrSetDefault(
    pdpi::P4RuntimeSession& session, sai::Instantiation default_instance) {
  ASSIGN_OR_RETURN(
      p4::v1::GetForwardingPipelineConfigResponse response,
      pdpi::GetForwardingPipelineConfig(
          &session, p4::v1::GetForwardingPipelineConfigRequest::ALL));
  if (response.has_config()) {
    LOG(INFO) << "Switch already has an active config.";
    return pdpi::CreateIrP4Info(response.config().p4info());
  }

  LOG(INFO) << "Pushing a " << sai::InstantiationToString(default_instance)
            << " config to the switch for testing.";
  RETURN_IF_ERROR(pdpi::SetMetadataAndSetForwardingPipelineConfig(
      &session,
      p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
      sai::GetP4Info(default_instance)));
  return sai::GetIrP4Info(default_instance);
}

// For each test we want to measure the INSERT, MODIFY, and DELETE performance.
struct P4WriteRequests {
  std::vector<p4::v1::WriteRequest> inserts;
  std::vector<p4::v1::WriteRequest> modifies;
  std::vector<p4::v1::WriteRequest> deletes;
};

// Sanity checks that we are generating the correct number of batch requests,
// and each request has the correct number of entries.
absl::Status VerifyP4WriteReuqestSizes(const P4WriteRequests& requests,
                                       uint32_t expected_batches,
                                       uint32_t expected_requests_per_batch) {
  if (requests.inserts.size() != expected_batches) {
    return absl::UnknownError(absl::StrFormat(
        "Failed to generate enough insert batches: want=%d got=%d",
        expected_batches, requests.inserts.size()));
  }
  for (int i = 0; i < requests.inserts.size(); ++i) {
    int got = requests.inserts[i].updates_size();
    if (got != expected_requests_per_batch) {
      return absl::UnknownError(
          absl::StrFormat("Failed to generate enough insert requests in batch "
                          "%d: want=%d got=%d",
                          i, expected_requests_per_batch, got));
    }
  }

  if (requests.modifies.size() != expected_batches) {
    return absl::UnknownError(absl::StrFormat(
        "Failed to generate enough modify batches: want=%d got=%d",
        expected_batches, requests.modifies.size()));
  }
  for (int i = 0; i < requests.modifies.size(); ++i) {
    int got = requests.modifies[i].updates_size();
    if (got != expected_requests_per_batch) {
      return absl::UnknownError(
          absl::StrFormat("Failed to generate enough modify requests in batch "
                          "%d: want=%d got=%d",
                          i, expected_requests_per_batch, got));
    }
  }

  if (requests.deletes.size() != expected_batches) {
    return absl::UnknownError(absl::StrFormat(
        "Failed to generate enough delete batches: want=%d got=%d",
        expected_batches, requests.deletes.size()));
  }
  for (int i = 0; i < requests.deletes.size(); ++i) {
    int got = requests.deletes[i].updates_size();
    if (got != expected_requests_per_batch) {
      return absl::UnknownError(
          absl::StrFormat("Failed to generate enough delete requests in batch "
                          "%d: want=%d got=%d",
                          i, expected_requests_per_batch, got));
    }
  }

  return absl::OkStatus();
}

absl::Status VerifyP4WcmpWriteSizes(
    const std::vector<p4::v1::WriteRequest>& requests, int expected_members,
    int expected_weight) {
  int total_members = 0;
  int total_weight = 0;
  for (const auto& request : requests) {
    for (const auto& update : request.updates()) {
      for (const auto& action : update.entity()
                                    .table_entry()
                                    .action()
                                    .action_profile_action_set()
                                    .action_profile_actions()) {
        total_members++;
        total_weight += action.weight();
      }
    }
  }

  if (total_members != expected_members) {
    return absl::UnknownError(
        absl::StrFormat("Failed to generate enough members: want=%d got=%d",
                        expected_members, total_members));
  }
  if (total_weight != expected_weight) {
    return absl::UnknownError(absl::StrFormat(
        "Failed to generate enough member weight: want=%d got=%d",
        expected_weight, total_weight));
  }
  return absl::OkStatus();
}

class P4rtRouteTest : public testing::Test {
 protected:
  void SetUp() override {
    ASSERT_OK_AND_ASSIGN(p4rt_session_, OpenP4RuntimeSession());
    ASSERT_OK_AND_ASSIGN(ir_p4info_,
                         GetExistingP4InfoOrSetDefault(
                             *p4rt_session_, sai::Instantiation::kMiddleblock));

    // Clear the current table entries, if any.
    ASSERT_OK(pdpi::ClearTableEntries(p4rt_session_.get()));
  }

  void TearDown() override {
    // Remove table entries that were created.
    if (p4rt_session_ != nullptr) {
      ASSERT_OK(pdpi::ClearTableEntries(p4rt_session_.get()));
    }
  }

  // Set connection & switch IDs so the request will not be rejected.
  void UpdateRequestMetadata(std::vector<p4::v1::WriteRequest>& requests) {
    for (auto& request : requests) {
      request.set_device_id(p4rt_session_->DeviceId());
      request.set_role(p4rt_session_->Role());
      *request.mutable_election_id() = p4rt_session_->ElectionId();
    }
  }

  void UpdateRequestMetadata(P4WriteRequests& requests) {
    UpdateRequestMetadata(requests.inserts);
    UpdateRequestMetadata(requests.modifies);
    UpdateRequestMetadata(requests.deletes);
  }

  absl::StatusOr<absl::Duration> SendBatchRequest(
      const std::vector<p4::v1::WriteRequest>& requests) {
    absl::Duration total_execution_time;
    for (const auto& request : requests) {
      // Send a batch of requests to the server and measure the response time.
      absl::Time start = absl::Now();

      // We don't expect any errors in the test. So if we see one we invalidate
      // the run.
      RETURN_IF_ERROR(p4rt_session_->Write(request));
      total_execution_time += absl::Now() - start;
    }

    return total_execution_time;
  }

  std::unique_ptr<pdpi::P4RuntimeSession> p4rt_session_;
  pdpi::IrP4Info ir_p4info_;
};

// When testing we randomly generate routes to program. RouteEntryInfo acts as a
// cache of table entries subsiquent flows can build upon. This also makes the
// order this object is built important! For example we should have a list of
// usable port IDs before creating RIFs which rely on port IDs. Similarly for
// NextHops which requires RIFs.
struct RouteEntryInfo {
  std::vector<int32_t> port_ids;
  P4RTUpdateByNameMap vrfs_by_name;
  P4RTUpdateByNameMap router_interfaces_by_name;
  P4RTUpdateByNameMap neighbors_by_name;
  P4RTUpdateByNameMap next_hops_by_name;
};

absl::StatusOr<std::vector<int32_t>> ParsePortIds(
    absl::string_view available_port_ids) {
  std::vector<int32_t> port_ids;
  for (const auto& str : absl::StrSplit(available_port_ids, ',')) {
    int32_t id = 0;
    if (!absl::SimpleAtoi(str, &id)) {
      return absl::InvalidArgumentError(
          absl::StrCat("Could not translate '", str, "' to an int."));
    }

    if (id == 0) {
      return absl::InvalidArgumentError(
          absl::StrCat("Port ID 0 is invalid: ", str));
    }
    port_ids.push_back(id);
  }
  return port_ids;
}

absl::Status GenerateRandomVrfs(absl::BitGen& bitgen, RouteEntryInfo& routes,
                                const pdpi::IrP4Info& ir_p4info,
                                int32_t count) {
  ASSIGN_OR_RETURN(auto vrfs,
                   RandomSetOfValues<int16_t>(bitgen, /*min_value=*/1,
                                              /*max_value=*/0x00FF, count));
  for (const auto& vrf : vrfs) {
    std::string name = absl::StrCat("vrf-", vrf);
    ASSIGN_OR_RETURN(
        routes.vrfs_by_name[name],
        gpins::VrfTableUpdate(ir_p4info, p4::v1::Update::INSERT, name));
  }
  return absl::OkStatus();
}

absl::Status GenerateRandomRIFs(absl::BitGen& bitgen, RouteEntryInfo& routes,
                                const pdpi::IrP4Info& ir_p4info,
                                int32_t count) {
  if (routes.port_ids.empty()) {
    return absl::InvalidArgumentError(
        "Port IDs need to be created before RIFs");
  }

  ASSIGN_OR_RETURN(
      auto addresses,
      RandomSetOfValues<int64_t>(bitgen, /*min_value=*/0,
                                 /*max_value=*/0x00'FF'FF'FF'FF'FF, count));
  for (const auto& address : addresses) {
    netaddr::MacAddress mac(0x10'00'00'00'00'00 + address);
    std::string name = absl::StrCat("rif-", mac.ToString());

    size_t port = absl::Uniform<size_t>(bitgen, 0, routes.port_ids.size());
    ASSIGN_OR_RETURN(routes.router_interfaces_by_name[name],
                     gpins::RouterInterfaceTableUpdate(
                         ir_p4info, p4::v1::Update::INSERT, name,
                         absl::StrCat(routes.port_ids[port]), mac.ToString()));
  }
  return absl::OkStatus();
}

absl::Status GenerateRandomNextHops(absl::BitGen& bitgen,
                                    RouteEntryInfo& routes,
                                    const pdpi::IrP4Info& ir_p4info,
                                    int32_t count) {
  ASSIGN_OR_RETURN(std::vector<std::string> rifs,
                   GetKeys(routes.router_interfaces_by_name),
                   _ << "RIFs need to be created before next hops");
  ASSIGN_OR_RETURN(
      auto addresses,
      RandomSetOfValues<int64_t>(bitgen, /*min_value=*/0,
                                 /*max_value=*/0x00'FF'FF'FF'FF'FF, count));
  for (const auto& address : addresses) {
    netaddr::MacAddress mac(0x20'00'00'00'00'00 + address);
    std::string neighbor_name = mac.ToLinkLocalIpv6Address().ToString();
    std::string nexthop_name = absl::StrCat("nh-", mac.ToString());
    std::string rif = rifs[absl::Uniform<size_t>(bitgen, 0, rifs.size())];

    ASSIGN_OR_RETURN(
        routes.neighbors_by_name[neighbor_name],
        gpins::NeighborTableUpdate(ir_p4info, p4::v1::Update::INSERT, rif,
                                   neighbor_name, mac.ToString()));
    ASSIGN_OR_RETURN(
        routes.next_hops_by_name[nexthop_name],
        gpins::NexthopTableUpdate(ir_p4info, p4::v1::Update::INSERT,
                                  nexthop_name, rif, neighbor_name));
  }
  return absl::OkStatus();
}

absl::StatusOr<P4WriteRequests> ComputeIpv4WriteRequests(
    absl::BitGen& bitgen, const RouteEntryInfo& routes,
    const pdpi::IrP4Info& ir_p4info, uint32_t number_batches,
    uint32_t batch_size) {
  ASSIGN_OR_RETURN(std::vector<std::string> vrfs, GetKeys(routes.vrfs_by_name),
                   _ << "VRFs need to be created before IPv4");
  ASSIGN_OR_RETURN(std::vector<std::string> nexthops,
                   GetKeys(routes.next_hops_by_name),
                   _ << "Next hops need to be created before IPv4");
  ASSIGN_OR_RETURN(auto addresses,
                   RandomSetOfValues<int32_t>(bitgen, /*min_value=*/0x0100'0000,
                                              /*max_value=*/0x1FFF'FFFF,
                                              number_batches * batch_size));

  P4WriteRequests requests;
  for (const int32_t address : addresses) {
    if (requests.inserts.empty() ||
        requests.inserts.back().updates_size() == batch_size) {
      requests.inserts.push_back(p4::v1::WriteRequest{});
      requests.modifies.push_back(p4::v1::WriteRequest{});
      requests.deletes.push_back(p4::v1::WriteRequest{});
    }

    // The initial INSERT request.
    netaddr::Ipv4Address ip(address);
    std::string vrf = vrfs[absl::Uniform<size_t>(bitgen, 0, vrfs.size())];
    std::string nexthop =
        nexthops[absl::Uniform<size_t>(bitgen, 0, nexthops.size())];
    ASSIGN_OR_RETURN(
        *requests.inserts.back().add_updates(),
        gpins::Ipv4TableUpdate(
            ir_p4info, p4::v1::Update::INSERT,
            gpins::IpTableOptions{
                .vrf_id = vrf,
                .dst_addr_lpm = std::make_pair(ip.ToString(), 32),
                .action = gpins::IpTableOptions::Action::kSetNextHopId,
                .nexthop_id = nexthop,
            }));

    // MODIFY the nexthop action.
    nexthop = nexthops[absl::Uniform<size_t>(bitgen, 0, nexthops.size())];
    ASSIGN_OR_RETURN(
        *requests.modifies.back().add_updates(),
        gpins::Ipv4TableUpdate(
            ir_p4info, p4::v1::Update::MODIFY,
            gpins::IpTableOptions{
                .vrf_id = vrf,
                .dst_addr_lpm = std::make_pair(ip.ToString(), 32),
                .action = gpins::IpTableOptions::Action::kSetNextHopId,
                .nexthop_id = nexthop,
            }));

    // DELETE the entry.
    ASSIGN_OR_RETURN(
        *requests.deletes.back().add_updates(),
        gpins::Ipv4TableUpdate(
            ir_p4info, p4::v1::Update::DELETE,
            gpins::IpTableOptions{
                .vrf_id = vrf,
                .dst_addr_lpm = std::make_pair(ip.ToString(), 32),
                .action = gpins::IpTableOptions::Action::kSetNextHopId,
                .nexthop_id = nexthop,
            }));
  }

  RETURN_IF_ERROR(
      VerifyP4WriteReuqestSizes(requests, number_batches, batch_size));
  return requests;
}

// WCMP entries are required to have a positive weight. This method will assign
// a weight of 1 to all members (i.e. even if the `total_group_weight` is less
// than the `size`). Then it will assign any remaining weight randomly.
std::vector<int> RandmizeWeights(absl::BitGen& bitgen, int size,
                                 int total_group_weight) {
  // All actions need at least a weight of 1 to be functionally correct.
  std::vector<int> weights(size, 1);
  int remaining_weight = total_group_weight - size;

  // If there is any weights remaining then we assign them randomly across
  // the actions.
  while (remaining_weight > 0) {
    --remaining_weight;
    weights[absl::Uniform<size_t>(bitgen, 0, weights.size())]++;
  }

  // Switches can preallocate weights as members are added. The worst case
  // is when weights get larger and larger with the members. Users can set a
  // flag to force this behavior (i.e. get worst case performance).
  if (FLAGS_wcmp_increasing_weights) {
    std::sort(weights.begin(), weights.end());
  }

  return weights;
}

absl::StatusOr<P4WriteRequests> ComputeWcmpWriteRequests(
    absl::BitGen& bitgen, const RouteEntryInfo& routes,
    const pdpi::IrP4Info& ir_p4info, uint32_t number_batches,
    uint32_t batch_size, int members_per_group, int total_group_weight) {
  bool change_weights_on_modify = FLAGS_wcmp_update_weights_when_modifying;
  bool change_nexthops_on_modify = FLAGS_wcmp_update_nexthops_when_modifying;
  // If both these flags are false then modify will have no affect. Report a
  // warning incase of user error.
  if (!change_weights_on_modify && !change_nexthops_on_modify) {
    LOG(WARNING) << "We are not changing the weights or the nexthops on modify "
                    "so all requests will match the inserts.";
  }

  // WCMP requests will reference next hops so they need to be created first.
  ASSIGN_OR_RETURN(std::vector<std::string> nexthops,
                   GetKeys(routes.next_hops_by_name),
                   _ << "Next hops need to be created before WCMP");

  P4WriteRequests requests;
  requests.inserts.resize(number_batches);
  requests.modifies.resize(number_batches);
  requests.deletes.resize(number_batches);
  int group_id = 0;
  for (int batch_num = 0; batch_num < number_batches; ++batch_num) {
    for (int entry_num = 0; entry_num < batch_size; ++entry_num) {
      std::string group_name = absl::StrCat("group-", ++group_id);

      // The initial INSERT request.
      std::vector<gpins::WcmpAction> actions(members_per_group);

      // Get a random set of next hops, but don't allow duplicates.
      ASSIGN_OR_RETURN(auto nexthop_indices,
                       RandomSetOfValues<size_t>(bitgen, 0, nexthops.size(),
                                                 members_per_group));
      for (int action_num = 0; action_num < members_per_group; ++action_num) {
        actions[action_num].nexthop_id = nexthops[action_num];
      }
      std::vector<int> weights =
          RandmizeWeights(bitgen, actions.size(), total_group_weight);
      for (size_t i = 0; i < actions.size(); ++i) {
        actions[i].weight = weights[i];
      }
      ASSIGN_OR_RETURN(
          *requests.inserts[batch_num].add_updates(),
          gpins::WcmpGroupTableUpdate(ir_p4info, p4::v1::Update::INSERT,
                                      group_name, actions));

      // MODIFY the nexthop actions and/or weights depending on FLAGs.
      if (change_nexthops_on_modify) {
        ASSIGN_OR_RETURN(nexthop_indices,
                         RandomSetOfValues<size_t>(bitgen, 0, nexthops.size(),
                                                   members_per_group));
        for (int action_num = 0; action_num < members_per_group; ++action_num) {
          actions[action_num].nexthop_id = nexthops[action_num];
        }
      }
      if (change_weights_on_modify) {
        weights = RandmizeWeights(bitgen, actions.size(), total_group_weight);
        for (size_t i = 0; i < actions.size(); ++i) {
          actions[i].weight = weights[i];
        }
      }
      ASSIGN_OR_RETURN(
          *requests.modifies[batch_num].add_updates(),
          gpins::WcmpGroupTableUpdate(ir_p4info, p4::v1::Update::MODIFY,
                                      group_name, actions));

      // DELETE the entries.
      ASSIGN_OR_RETURN(
          *requests.deletes[batch_num].add_updates(),
          gpins::WcmpGroupTableUpdate(ir_p4info, p4::v1::Update::DELETE,
                                      group_name, actions));
    }
  }

  // Verify that we generated the correct number of members and their weights.
  // We do not verify that those values make sense (i.e. we could generate more
  // weights than a device supports)
  int expected_members = number_batches * batch_size * members_per_group;
  int expected_weight = number_batches * batch_size * total_group_weight;
  RETURN_IF_ERROR(VerifyP4WcmpWriteSizes(requests.inserts, expected_members,
                                         expected_weight));
  RETURN_IF_ERROR(VerifyP4WcmpWriteSizes(requests.modifies, expected_members,
                                         expected_weight));
  RETURN_IF_ERROR(
      VerifyP4WriteReuqestSizes(requests, number_batches, batch_size));
  return requests;
}

absl::StatusOr<P4WriteRequests> ComputeIpv6WriteRequests(
    absl::BitGen& bitgen, const RouteEntryInfo& routes,
    const pdpi::IrP4Info& ir_p4info, uint32_t number_batches,
    uint32_t batch_size) {
  ASSIGN_OR_RETURN(std::vector<std::string> vrfs, GetKeys(routes.vrfs_by_name),
                   _ << "VRFs need to be created before IPv6");
  ASSIGN_OR_RETURN(std::vector<std::string> nexthops,
                   GetKeys(routes.next_hops_by_name),
                   _ << "Next hops need to be created before IPv6");
  ASSIGN_OR_RETURN(
      auto addresses,
      RandomSetOfValues<int64_t>(bitgen, /*min_value=*/0x0000'0000'0000'0001,
                                 /*max_value=*/0x1FFF'FFFF'FFFF'FFFF,
                                 number_batches * batch_size));

  P4WriteRequests requests;
  for (const int64_t address : addresses) {
    if (requests.inserts.empty() ||
        requests.inserts.back().updates_size() == batch_size) {
      requests.inserts.push_back(p4::v1::WriteRequest{});
      requests.modifies.push_back(p4::v1::WriteRequest{});
      requests.deletes.push_back(p4::v1::WriteRequest{});
    }

    // The initial INSERT request.
    netaddr::Ipv6Address ip(absl::MakeUint128(address, /*low=*/0));
    std::string vrf = vrfs[absl::Uniform<size_t>(bitgen, 0, vrfs.size())];
    std::string nexthop =
        nexthops[absl::Uniform<size_t>(bitgen, 0, nexthops.size())];
    ASSIGN_OR_RETURN(
        *requests.inserts.back().add_updates(),
        gpins::Ipv6TableUpdate(
            ir_p4info, p4::v1::Update::INSERT,
            gpins::IpTableOptions{
                .vrf_id = vrf,
                .dst_addr_lpm = std::make_pair(ip.ToString(), 64),
                .action = gpins::IpTableOptions::Action::kSetNextHopId,
                .nexthop_id = nexthop,
            }));

    // MODIFY the nexthop action.
    nexthop = nexthops[absl::Uniform<size_t>(bitgen, 0, nexthops.size())];
    ASSIGN_OR_RETURN(
        *requests.modifies.back().add_updates(),
        gpins::Ipv6TableUpdate(
            ir_p4info, p4::v1::Update::MODIFY,
            gpins::IpTableOptions{
                .vrf_id = vrf,
                .dst_addr_lpm = std::make_pair(ip.ToString(), 64),
                .action = gpins::IpTableOptions::Action::kSetNextHopId,
                .nexthop_id = nexthop,
            }));

    // DELETE the entry.
    ASSIGN_OR_RETURN(
        *requests.deletes.back().add_updates(),
        gpins::Ipv6TableUpdate(
            ir_p4info, p4::v1::Update::DELETE,
            gpins::IpTableOptions{
                .vrf_id = vrf,
                .dst_addr_lpm = std::make_pair(ip.ToString(), 64),
                .action = gpins::IpTableOptions::Action::kSetNextHopId,
                .nexthop_id = nexthop,
            }));
  }

  RETURN_IF_ERROR(
      VerifyP4WriteReuqestSizes(requests, number_batches, batch_size));
  return requests;
}

absl::StatusOr<std::vector<p4::v1::WriteRequest>> ComputeWcmpWriteRequests(
    absl::BitGen& bitgen, const RouteEntryInfo& routes,
    const pdpi::IrP4Info& ir_p4info, uint32_t number_batches,
    uint32_t batch_size, int members_per_group, int total_group_weight) {
  ASSIGN_OR_RETURN(std::vector<std::string> nexthops,
                   GetKeys(routes.next_hops_by_name),
                   _ << "Next hops need to be created before WCMP");

  std::vector<p4::v1::WriteRequest> requests(number_batches);
  int group_id = 0;
  for (int batch_num = 0; batch_num < number_batches; ++batch_num) {
    for (int entry_num = 0; entry_num < batch_size; ++entry_num) {
      // Create a random group of actions with a weight of 1.
      std::vector<gpins::WcmpAction> actions(members_per_group);

      // Get a random set of next hops, but don't allow duplicates.
      ASSIGN_OR_RETURN(auto nexthop_indices,
                       RandomSetOfValues<size_t>(bitgen, 0, nexthops.size(),
                                                 members_per_group));
      for (int action_num = 0; action_num < members_per_group; ++action_num) {
        actions[action_num].nexthop_id = nexthops[action_num];
      }

      // All actions need at least a weight of 1 to be functionally correct.
      int remaining_weight = total_group_weight;
      std::vector<int> weights(actions.size(), 1);
      remaining_weight -= actions.size();

      // If there is any weights remaining then we assign them randomly across
      // the actions.
      while (remaining_weight > 0) {
        --remaining_weight;
        weights[absl::Uniform<size_t>(bitgen, 0, weights.size())]++;
      }

      // Switches can preallocate weights as members are added. The worst case
      // is when weights get larger and larger with the members. Users can set a
      // flag to force this behavior (i.e. get worst case performance).
      if (FLAGS_wcmp_increasing_weights) {
        std::sort(weights.begin(), weights.end());
      }

      for (size_t i = 0; i < actions.size(); ++i) {
        actions[i].weight = weights[i];
      }
      ASSIGN_OR_RETURN(*requests[batch_num].add_updates(),
                       gpins::WcmpGroupTableUpdate(
                           ir_p4info, p4::v1::Update::INSERT,
                           absl::StrCat("group-", ++group_id), actions));
    }
  }

  // Verify that we generated the correct number of members and their weights.
  // We do not verify that those values make sense (i.e. we could generate more
  // weights than a device supports).
  RETURN_IF_ERROR(VerifyP4WcmpWriteSizes(
      requests,
      /*expected_members=*/number_batches * batch_size * members_per_group,
      /*expected_weight=*/number_batches * batch_size * total_group_weight));
  return requests;
}

absl::StatusOr<std::vector<p4::v1::WriteRequest>> ComputeIpv6WriteRequests(
    absl::BitGen& bitgen, const RouteEntryInfo& routes,
    const pdpi::IrP4Info& ir_p4info, uint32_t number_batches,
    uint32_t batch_size) {
  ASSIGN_OR_RETURN(std::vector<std::string> vrfs, GetKeys(routes.vrfs_by_name),
                   _ << "VRFs need to be created before IPv6");
  ASSIGN_OR_RETURN(std::vector<std::string> nexthops,
                   GetKeys(routes.next_hops_by_name),
                   _ << "Next hops need to be created before IPv6");
  ASSIGN_OR_RETURN(
      auto addresses,
      RandomSetOfValues<int64_t>(bitgen, /*min_value=*/0x0000'0000'0000'0001,
                                 /*max_value=*/0x1FFF'FFFF'FFFF'FFFF,
                                 number_batches * batch_size));

  std::vector<p4::v1::WriteRequest> requests;
  for (const int64_t address : addresses) {
    if (requests.empty() || requests.back().updates_size() == batch_size) {
      requests.push_back(p4::v1::WriteRequest{});
    }

    netaddr::Ipv6Address ip(absl::MakeUint128(address, /*low=*/0));
    std::string vrf = vrfs[absl::Uniform<size_t>(bitgen, 0, vrfs.size())];
    std::string nexthop =
        nexthops[absl::Uniform<size_t>(bitgen, 0, nexthops.size())];
    ASSIGN_OR_RETURN(
        *requests.back().add_updates(),
        gpins::Ipv6TableUpdate(
            ir_p4info, p4::v1::Update::INSERT,
            gpins::IpTableOptions{
                .vrf_id = vrf,
                .dst_addr_lpm = std::make_pair(ip.ToString(), 64),
                .action = gpins::IpTableOptions::Action::kSetNextHopId,
                .nexthop_id = nexthop,
            }));
  }

  // Sanity checks.
  if (requests.size() != number_batches) {
    return absl::UnknownError(
        absl::StrCat("Failed to generate enough batches: want=", number_batches,
                     " got=", requests.size()));
  }
  return requests;
}

TEST_F(P4rtRouteTest, MeasureWriteLatency) {
  int32_t number_of_batches = FLAGS_number_batches;
  int32_t requests_per_batch = FLAGS_batch_size;
  std::string available_port_ids = FLAGS_port_ids;
  int32_t number_of_vrfs = FLAGS_vrfs;
  int32_t number_of_rifs = FLAGS_rifs;
  int32_t number_of_nexthops = FLAGS_next_hops;

  // Randomly generate the routes that will be used by these tests.
  absl::BitGen bitgen;
  RouteEntryInfo routes;
  ASSERT_OK_AND_ASSIGN(routes.port_ids, ParsePortIds(available_port_ids));
  ASSERT_OK(GenerateRandomVrfs(bitgen, routes, ir_p4info_, number_of_vrfs));
  ASSERT_OK(GenerateRandomRIFs(bitgen, routes, ir_p4info_, number_of_rifs));
  ASSERT_OK(
      GenerateRandomNextHops(bitgen, routes, ir_p4info_, number_of_nexthops));

  // Install the route entries that are needed by the IPv4 flows.
  std::vector<p4::v1::WriteRequest> premeasurement_requests;
  AppendUpdatesToWriteRequest(premeasurement_requests.emplace_back(),
                              routes.vrfs_by_name);
  AppendUpdatesToWriteRequest(premeasurement_requests.emplace_back(),
                              routes.router_interfaces_by_name);
  AppendUpdatesToWriteRequest(premeasurement_requests.emplace_back(),
                              routes.neighbors_by_name);
  AppendUpdatesToWriteRequest(premeasurement_requests.emplace_back(),
                              routes.next_hops_by_name);
  UpdateRequestMetadata(premeasurement_requests);
  ASSERT_OK(SendBatchRequest(premeasurement_requests).status());

  if (FLAGS_run_ipv4) {
    // Pre-compute all the IPv4 requests so they can be sent as quickly as
    // possible to the switch under test.
    ASSERT_OK_AND_ASSIGN(
        P4WriteRequests requests,
        ComputeIpv4WriteRequests(bitgen, routes, ir_p4info_, number_of_batches,
                                 requests_per_batch));
    UpdateRequestMetadata(requests);
    ASSERT_OK_AND_ASSIGN(absl::Duration insert_time,
                         SendBatchRequest(requests.inserts));
    ASSERT_OK_AND_ASSIGN(absl::Duration modify_time,
                         SendBatchRequest(requests.modifies));
    ASSERT_OK_AND_ASSIGN(absl::Duration delete_time,
                         SendBatchRequest(requests.deletes));

    // Write the results to stdout so that the callers can parse the output.
    int64_t total_entries = number_of_batches * requests_per_batch;
    std::cout
        << absl::StreamFormat(
               "ipv4_requests=%d ipv4_entry_total=%lld "
               "ipv4_insert_time=%lld(msecs) ipv4_modify_time=%lld(msecs) "
               "ipv4_delete_time=%lld(msecs)",
               number_of_batches, total_entries,
               absl::ToInt64Milliseconds(insert_time),
               absl::ToInt64Milliseconds(modify_time),
               absl::ToInt64Milliseconds(delete_time))
        << std::endl;

    // TODO: remove once we migrate the Perfkit dashboard to the
    // new tags.
    std::cout << "Successfully wrote IpTable entries to the switch, time: "
              << ToInt64Milliseconds(insert_time) << "(msecs)" << std::endl;
  }

  if (FLAGS_run_ipv6) {
    // Pre-compute all the IPv6 requests so they can be sent as quickly as
    // possible to the switch under test.
    ASSERT_OK_AND_ASSIGN(
        P4WriteRequests requests,
        ComputeIpv6WriteRequests(bitgen, routes, ir_p4info_, number_of_batches,
                                 requests_per_batch));
    UpdateRequestMetadata(requests);
    ASSERT_OK_AND_ASSIGN(absl::Duration insert_time,
                         SendBatchRequest(requests.inserts));
    ASSERT_OK_AND_ASSIGN(absl::Duration modify_time,
                         SendBatchRequest(requests.modifies));
    ASSERT_OK_AND_ASSIGN(absl::Duration delete_time,
                         SendBatchRequest(requests.deletes));

    // Write the results to stdout so that the callers can parse the output.
    int64_t total_entries = number_of_batches * requests_per_batch;
    std::cout
        << absl::StreamFormat(
               "ipv6_requests=%d ipv6_entry_total=%lld "
               "ipv6_insert_time=%lld(msecs) ipv6_modify_time=%lld(msecs) "
               "ipv6_delete_time=%lld(msecs)",
               number_of_batches, total_entries,
               absl::ToInt64Milliseconds(insert_time),
               absl::ToInt64Milliseconds(modify_time),
               absl::ToInt64Milliseconds(delete_time))
        << std::endl;
  }

  if (FLAGS_run_ipv6) {
    // Pre-compute all the IPv6 requests so they can be sent as quickly as
    // possible to the switch under test.
    ASSERT_OK_AND_ASSIGN(
        std::vector<p4::v1::WriteRequest> requests,
        ComputeIpv6WriteRequests(bitgen, routes, ir_p4info_, number_of_batches,
                                 requests_per_batch));
    UpdateRequestMetadata(requests);
    ASSERT_OK_AND_ASSIGN(absl::Duration execution_time,
                         SendBatchRequest(requests));

    // Write the results to stdout so that the callers can parse the output.
    int64_t total_entries = number_of_batches * requests_per_batch;
    std::cout << absl::StreamFormat(
                     "ipv6_insert_requests=%d ipv6_insert_entry_total=%lld "
                     "ipv6_insert_time=%lld(msecs)",
                     number_of_batches, total_entries,
                     absl::ToInt64Milliseconds(execution_time))
              << std::endl;
  }

  if (FLAGS_run_wcmp) {
    int members_per_group = FLAGS_wcmp_members_per_group;
    int total_group_weight = FLAGS_wcmp_total_group_weight;

    // Pre-compute all the WCMP requests so they can be sent as quickly as
    // possible to the switch under test.
    ASSERT_OK_AND_ASSIGN(
        P4WriteRequests requests,
        ComputeWcmpWriteRequests(bitgen, routes, ir_p4info_, number_of_batches,
                                 requests_per_batch, members_per_group,
                                 total_group_weight));
    UpdateRequestMetadata(requests);
    ASSERT_OK_AND_ASSIGN(absl::Duration insert_time,
                         SendBatchRequest(requests.inserts));
    ASSERT_OK_AND_ASSIGN(absl::Duration modify_time,
                         SendBatchRequest(requests.modifies));
    ASSERT_OK_AND_ASSIGN(absl::Duration delete_time,
                         SendBatchRequest(requests.deletes));

    // Write the results to stdout so that callers can parse the output.
    int64_t total_groups = number_of_batches * requests_per_batch;
    int64_t total_members = total_groups * members_per_group;
    int64_t total_weight = total_groups * total_group_weight;
    std::cout
        << absl::StreamFormat(
               "wcmp_requests=%d wcmp_groups_total=%lld "
               "wcmp_members_total=%lld wcmp_weight_total=%lld "
               "wcmp_insert_time=%lld(msecs) wcmp_modify_time=%lld(msecs) "
               "wcmp_delete_time=%lld(msecs)",
               number_of_batches, total_groups, total_members, total_weight,
               absl::ToInt64Milliseconds(insert_time),
               absl::ToInt64Milliseconds(modify_time),
               absl::ToInt64Milliseconds(delete_time))
        << std::endl;
  }
}

}  // namespace
}  // namespace p4rt_app

// Temporary fix to have performance tests run nightly until we find a way to
// bring p4rt_test_main.cc to p4rt_app specific tests alone.
GTEST_API_ int main(int argc, char** argv) {
  gflags::ParseCommandLineFlags(&argc, &argv, true);
  google::InitGoogleLogging(argv[0]);
  testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
