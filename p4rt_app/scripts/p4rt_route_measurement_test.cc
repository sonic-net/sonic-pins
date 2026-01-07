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
#include <iostream>
#include <memory>
#include <random>
#include <string>
#include <utility>
#include <vector>

#include "absl/container/btree_map.h"
#include "absl/container/btree_set.h"
#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "absl/log/initialize.h"
#include "absl/log/log.h"
#include "absl/numeric/int128.h"
#include "absl/random/distributions.h"
#include "absl/random/random.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_join.h"
#include "absl/strings/str_split.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/collections.h"
#include "gutil/gutil/io.h"
#include "gutil/gutil/status.h"  // IWYU pragma: keep
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"  // IWYU pragma: keep
#include "p4/v1/p4runtime.grpc.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/netaddr/ipv4_address.h"
#include "p4_pdpi/netaddr/ipv6_address.h"
#include "p4_pdpi/netaddr/mac_address.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/sequencing.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "tests/lib/p4rt_fixed_table_programming_helper.h"

// The test can be run over a unix socket or TCP connection. In general (i.e.
// verify for your own enviornment) the socket will be unsecured while the TCP
// connection requires authentication.
//
// NOTE: if not using a socket then the server_address should be formatted as
//       <IP_address>:9559.
ABSL_FLAG(std::string, server_address, "unix:/sock/p4rt.sock",
          "The address of the server to connect to");

ABSL_FLAG(bool, insecure, true, "Use insecure connection");
ABSL_FLAG(std::string, ca_cert, "/keys/ca_cert.lnk",
          "CA bundle file. Used when insecure is false");
ABSL_FLAG(std::string, cert, "/keys/pins_test_user.cert",
          "Cert file. Used when insecure is false");
ABSL_FLAG(std::string, key, "/keys/pins_test_user.key",
          "Key file. Used when insecure is false");
ABSL_FLAG(std::string, host_name, "",
          "Host name of the switch for validating the switch cert. Used "
          "when insecure is false");

// P4RT connections require a device and election ID to program flows. By
// default we use a time based election ID, and it shouldn't need to be set
// manually. However, the device ID should always be set and must match the
// machine being used.
//
// Device ID can generally be found in redis using:
//   $ redis-cli -n 4 hget "NODE_CFG|integrated_circuit0" "node-id"
ABSL_FLAG(int64_t, election_id, -1, "Election id to be used");
ABSL_FLAG(uint64_t, p4rt_device_id, 1, "P4RT device ID");

// The test will create and install a random set of route-related or
// multicast-related entries (i.e. RIFs, VRFs, NextHops, Multicast groups
// and/or multicast group members).  The time needed to install dependent
// elements is not included in the reported latency.
ABSL_FLAG(std::string, port_ids, "1",
          "A comma separated list of usable ports.");
ABSL_FLAG(int32_t, vrfs, 64, "The number of VRFs to install.");
ABSL_FLAG(int32_t, rifs, 64, "The number of router interfaces to install.");
ABSL_FLAG(int32_t, next_hops, 512,
          "The number of next-hop entries to install.");
ABSL_FLAG(int32_t, encaps, 512,
          "The number of tunnel encap entries to install.");
ABSL_FLAG(int32_t, multicast_members_per_group, 8,
          "The number of multicast group members per group.");

// A run will automatically generate `number_batches` write requests each with
// `batch_size` updates (i.e. number_batches x batch_size total flows). Runtime
// only includes the P4RT Write() time, and not the generation.
ABSL_FLAG(int32_t, number_batches, 10,
          "Total number of gRPC write calls made to the switch.");
ABSL_FLAG(int32_t, batch_size, 100,
          "Total number of table entries in each gRPC write.");
ABSL_FLAG(bool, cleanup, true, "Delete all programmed flows at end of test.");

// Users should select the specific test they want to run.  Because the tested
// tables don't overlap users can run multiple, and they will happen
// sequentially. Users should be careful when running multiple tests since the
// batch sizes are reused (i.e. 10k IPv4 flows may be reasonable, but 10k WCMP
// groups may not be).
ABSL_FLAG(bool, run_ipv4, false, "Run IPv4 route latency tests.");
ABSL_FLAG(bool, run_ipv6, false, "Run IPv6 route latency tests.");
ABSL_FLAG(bool, run_wcmp, false, "Run IPv4 route latency tests.");
ABSL_FLAG(bool, run_encap, false, "Run Tunnel encap latency tests.");
ABSL_FLAG(bool, run_vlan, false, "Run vlan latency tests.");
ABSL_FLAG(bool, run_vlan_member, false, "Run vlan member latency tests.");
ABSL_FLAG(bool, run_ip_mcast_ritf, false,
          "Run IP multicast router interface latency tests.");
ABSL_FLAG(bool, run_l2_mcast_ritf, false,
          "Run L2 multicast router interface latency tests.");
ABSL_FLAG(bool, run_ip_multicast, false, "Run IP multicast latency tests.");
ABSL_FLAG(bool, run_l2_multicast, false, "Run L2 multicast latency tests.");
ABSL_FLAG(bool, run_ipv4_mcast_routes, false,
          "Run IPv4 multicast route latency tests.");
ABSL_FLAG(bool, run_ipv6_mcast_routes, false,
          "Run IPv6 multicast route latency tests.");

// Extra configs that affect WCMP batch sizes and flows.
ABSL_FLAG(int32_t, wcmp_members_per_group, 2,
          "Number of members in each WCMP group.");
ABSL_FLAG(int32_t, wcmp_total_group_weight, 2,
          "Total accumulated weight for all members in a WCMP group.");
ABSL_FLAG(bool, wcmp_update_weights_when_modifying, true,
          "Change weight values when modifying WCMP groups.");
ABSL_FLAG(bool, wcmp_update_nexthops_when_modifying, false,
          "Change nexthop values when modifying WCMP groups.");
ABSL_FLAG(bool, wcmp_increasing_weights, false,
          "Force the weight of a member to be >= the weight of the member "
          "that came before it.");
ABSL_FLAG(int32_t, wcmp_unique_weights_per_group, 512,
          "Max number of unique weights to use for each WCMP group.");
ABSL_FLAG(bool, wcmp_set_watch_port, false,
          "Use the port from the next hop as the WCMP watch port.");

// Pass a comma separated list of digits to reproduce a specific test.
ABSL_FLAG(std::string, seed_seq, "",
          "Force a specific seed_seq value to repeat a test.");

namespace p4rt_app {
namespace {

// To make runs reproducible we intentionally use a absl::btree_map.
using P4RTUpdateByNameMap = absl::btree_map<std::string, p4::v1::Update>;

constexpr int kMaxVlans = 512;
constexpr int kMaxIpMulticastGroups = 500;

// Uses the seed sequence passed by the `--seed_seq` flag. If no sequence is set
// then it will choose a random one.
std::seed_seq GetSeedSeq() {
  std::string forced_seq = absl::GetFlag(FLAGS_seed_seq);
  std::vector<int> seq;
  if (forced_seq.empty()) {
    absl::BitGen bitgen;
    seq.resize(32);
    for (int& s : seq) {
      s = absl::Uniform<int>(bitgen, 1, 10);
    }
  } else {
    for (const auto& s : absl::StrSplit(forced_seq, ',')) {
      int value;
      if (!absl::SimpleAtoi(s, &value)) {
        std::cout << "--seed_seq is invalid: " << forced_seq << std::endl;
      } else {
        seq.push_back(value);
      }
    }
  }

  std::cout << "--seed_seq=" << absl::StrJoin(seq, ",", absl::StreamFormatter())
            << std::endl;
  return std::seed_seq(seq.begin(), seq.end());
}

// Generated a random set of unique value in the range [min_value, max_value)
// To make runs reproducible we intentionally return a absl::btree_set.
template <typename T>
absl::StatusOr<absl::btree_set<T>> RandomSetOfUniqueValues(absl::BitGen& bitgen,
                                                           const T& min_value,
                                                           const T& max_value,
                                                           int size) {
  if ((max_value - min_value) < size) {
    return absl::InvalidArgumentError(absl::StrCat(
        "Interval is not enough to generate ", size,
        " unique values in the range [", min_value, ",", max_value, ")"));
  }

  // We use the max strikes count to prevent infinite loops.
  const int max_strikes = 4 * size;
  int strikes = 0;

  absl::btree_set<T> result;
  while (result.size() < size && strikes < max_strikes) {
    if (!result.insert(absl::Uniform<T>(bitgen, min_value, max_value)).second) {
      strikes++;
    }
  }
  // Try to fill the missing entries.
  if (strikes >= max_strikes) {
    for (T i = min_value; i < max_value && result.size() < size; i++) {
      result.insert(i);
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
  std::string server_address = absl::GetFlag(FLAGS_server_address);
  uint64_t device_id = absl::GetFlag(FLAGS_p4rt_device_id);
  int64_t election_id_high = absl::GetFlag(FLAGS_election_id) == -1
                                 ? absl::ToUnixSeconds(absl::Now())
                                 : absl::GetFlag(FLAGS_election_id);

  LOG(INFO) << "Opening P4RT connection to: " << server_address;
  std::unique_ptr<p4::v1::P4Runtime::Stub> stub;
  if (absl::GetFlag(FLAGS_insecure)) {
    stub = pdpi::CreateP4RuntimeStub(absl::GetFlag(FLAGS_server_address),
                                     grpc::InsecureChannelCredentials());
  } else {
    grpc::SslCredentialsOptions sslOpts;
    sslOpts.pem_root_certs = ReadFileOrEmpty(absl::GetFlag(FLAGS_ca_cert));
    sslOpts.pem_private_key = ReadFileOrEmpty(absl::GetFlag(FLAGS_key));
    sslOpts.pem_cert_chain = ReadFileOrEmpty(absl::GetFlag(FLAGS_cert));
    stub = pdpi::CreateP4RuntimeStub(absl::GetFlag(FLAGS_server_address),
                                     grpc::SslCredentials(sslOpts),
                                     absl::GetFlag(FLAGS_host_name));
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
absl::Status VerifyP4WriteRequestSizes(const P4WriteRequests& requests,
                                       uint32_t expected_batches,
                                       uint32_t expected_requests_per_batch,
                                       bool modify_supported = true) {
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

  if (modify_supported) {
    if (requests.modifies.size() != expected_batches) {
      return absl::UnknownError(absl::StrFormat(
          "Failed to generate enough modify batches: want=%d got=%d",
          expected_batches, requests.modifies.size()));
    }

    for (int i = 0; i < requests.modifies.size(); ++i) {
      int got = requests.modifies[i].updates_size();
      if (got != expected_requests_per_batch) {
        return absl::UnknownError(absl::StrFormat(
            "Failed to generate enough modify requests in batch "
            "%d: want=%d got=%d",
            i, expected_requests_per_batch, got));
      }
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
    if (absl::GetFlag(FLAGS_cleanup)) {
      ASSERT_OK(pdpi::ClearEntities(*p4rt_session_.get()));
    }
  }

  void TearDown() override {
    // Remove table entries that were created.
    if (p4rt_session_ != nullptr) {
      if (absl::GetFlag(FLAGS_cleanup)) {
        ASSERT_OK(pdpi::ClearEntities(*p4rt_session_.get()));
      }
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
    int batch_count = 0;
    for (const auto& request : requests) {
      // Send a batch of requests to the server and measure the response time.
      absl::Time start = absl::Now();

      // We don't expect any errors in the test. So if we see one we invalidate
      // the run.
      RETURN_IF_ERROR(p4rt_session_->Write(request))
          << "Failed after sending " << batch_count << " batches.";
      total_execution_time += absl::Now() - start;
      batch_count++;
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

  // Track the port for RIFs and NHs so that we can use them as watch ports if
  // needed.
  absl::flat_hash_map<std::string, std::string> port_by_rif_name;
  absl::flat_hash_map<std::string, std::string> port_by_next_hop_name;
  // Used for matching the router interface in the tunnel and neighbor tables.
  absl::btree_map<std::string, std::string> neighbor_to_router_interface_name;
};

// When testing we randomly generate multicast programming info.
// MulticastEntryInfo acts as a cache of entries to build upon.  This also makes
// the order this object is built important! For example we should have a list
// of usable port IDs before creating RIFs which rely on port IDs. Similarly for
// multicast group members, which requires RIFs.
struct MulticastEntryInfo {
  std::vector<int32_t> port_ids;
  P4RTUpdateByNameMap rifs_by_name;
  P4RTUpdateByNameMap vlans_by_name;
  P4RTUpdateByNameMap vlan_members_by_name;
  P4RTUpdateByNameMap mcast_groups_by_name;

  std::vector<pins::MulticastReplica> replicas;
  std::vector<int32_t> vlans;
  std::vector<int32_t> mcast_groups;
};

absl::StatusOr<std::vector<int32_t>> ParseIds(absl::string_view available_ids) {
  std::vector<int32_t> ids;
  if (available_ids.empty()) return ids;
  for (const auto& str : absl::StrSplit(available_ids, ',')) {
    int32_t id = 0;
    if (!absl::SimpleAtoi(str, &id)) {
      return absl::InvalidArgumentError(
          absl::StrCat("Could not translate '", str, "' to an int."));
    }

    if (id == 0) {
      return absl::InvalidArgumentError(
          absl::StrCat("Port ID 0 is invalid: ", str));
    }
    ids.push_back(id);
  }
  return ids;
}

absl::Status GenerateRandomVrfs(absl::BitGen& bitgen, RouteEntryInfo& routes,
                                const pdpi::IrP4Info& ir_p4info,
                                int32_t count) {
  ASSIGN_OR_RETURN(
      auto vrfs, RandomSetOfUniqueValues<int16_t>(bitgen, /*min_value=*/1,
                                                  /*max_value=*/0x0100, count));
  for (const auto& vrf : vrfs) {
    std::string name = absl::StrCat("vrf-", vrf);
    ASSIGN_OR_RETURN(
        routes.vrfs_by_name[name],
        pins::VrfTableUpdate(ir_p4info, p4::v1::Update::INSERT, name));
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

  ASSIGN_OR_RETURN(auto addresses,
                   RandomSetOfUniqueValues<int64_t>(
                       bitgen, /*min_value=*/0,
                       /*max_value=*/0x00'FF'FF'FF'FF'FF, count));
  for (const auto& address : addresses) {
    netaddr::MacAddress mac(0x10'00'00'00'00'00 + address);
    std::string rif_name = absl::StrCat("rif-", mac.ToString());

    size_t port = absl::Uniform<size_t>(bitgen, 0, routes.port_ids.size());
    std::string port_name = absl::StrCat(routes.port_ids[port]);
    ASSIGN_OR_RETURN(
        routes.router_interfaces_by_name[rif_name],
        pins::RouterInterfaceTableUpdate(ir_p4info, p4::v1::Update::INSERT,
                                          rif_name, port_name, mac.ToString()));
    routes.port_by_rif_name[rif_name] = port_name;
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
  ASSIGN_OR_RETURN(auto addresses,
                   RandomSetOfUniqueValues<int64_t>(
                       bitgen, /*min_value=*/0,
                       /*max_value=*/0x00'FF'FF'FF'FF'FF, count));
  for (const auto& address : addresses) {
    netaddr::MacAddress mac(0x20'00'00'00'00'00 + address);
    std::string neighbor_name = mac.ToLinkLocalIpv6Address().ToString();
    std::string nexthop_name = absl::StrCat("nh-", mac.ToString());
    std::string rif = rifs[absl::Uniform<size_t>(bitgen, 0, rifs.size())];

    ASSIGN_OR_RETURN(
        routes.neighbors_by_name[neighbor_name],
        pins::NeighborTableUpdate(ir_p4info, p4::v1::Update::INSERT, rif,
                                   neighbor_name, mac.ToString()));
    ASSIGN_OR_RETURN(
        routes.next_hops_by_name[nexthop_name],
        pins::NexthopTableUpdate(ir_p4info, p4::v1::Update::INSERT,
                                  nexthop_name, rif, neighbor_name));

    std::string* port_name = gutil::FindOrNull(routes.port_by_rif_name, rif);
    if (port_name == nullptr) {
      return gutil::NotFoundErrorBuilder()
             << "Could not find port name for rif '" << rif << "'.";
    }
    routes.port_by_next_hop_name[nexthop_name] = *port_name;
  }
  return absl::OkStatus();
}

absl::Status GenerateRandomVlans(absl::BitGen& bitgen,
                                 MulticastEntryInfo& entries,
                                 const pdpi::IrP4Info& ir_p4info,
                                 int32_t count) {
  ASSIGN_OR_RETURN(auto vlans, RandomSetOfUniqueValues<int32_t>(
                                   bitgen, /*min_value=*/2,
                                   /*max_value=*/0x0FFF, count));

  for (const auto& vlan : vlans) {
    std::string vlan_name = absl::StrCat("vlan", vlan);
    ASSIGN_OR_RETURN(
        entries.vlans_by_name[vlan_name],
        pins::VlanTableUpdate(ir_p4info, p4::v1::Update::INSERT, vlan));
    entries.vlans.push_back(vlan);
  }
  return absl::OkStatus();
}

absl::Status GenerateRandomVlansAndMembers(absl::BitGen& bitgen,
                                           MulticastEntryInfo& entries,
                                           const pdpi::IrP4Info& ir_p4info,
                                           int32_t count) {
  if (entries.port_ids.empty()) {
    return absl::InvalidArgumentError(
        "Port IDs need to be created before RIFs");
  }

  ASSIGN_OR_RETURN(auto vlans, RandomSetOfUniqueValues<int32_t>(
                                   bitgen, /*min_value=*/2,
                                   /*max_value=*/0x0FFF, count));

  for (const auto& vlan : vlans) {
    std::string vlan_name = absl::StrCat("vlan", vlan);
    ASSIGN_OR_RETURN(
        entries.vlans_by_name[vlan_name],
        pins::VlanTableUpdate(ir_p4info, p4::v1::Update::INSERT, vlan));
    for (const auto& port_id : entries.port_ids) {
      bool tag = absl::Bernoulli(bitgen, 0.5);
      std::string vlan_member_name =
          absl::StrCat("port-", port_id, "-vlan", vlan);
      ASSIGN_OR_RETURN(
          entries.vlan_members_by_name[vlan_member_name],
          pins::VlanMemberTableUpdate(ir_p4info, p4::v1::Update::INSERT,
                                      port_id, vlan, tag));
    }
    entries.vlans.push_back(vlan);
  }
  return absl::OkStatus();
}

absl::Status GenerateRandomMulticastRIFs(absl::BitGen& bitgen,
                                         MulticastEntryInfo& entries,
                                         const pdpi::IrP4Info& ir_p4info,
                                         bool is_ip_mcast, int32_t count) {
  if (entries.port_ids.empty()) {
    return absl::InvalidArgumentError(
        "Port IDs need to be created before RIFs");
  }

  ASSIGN_OR_RETURN(auto addresses,
                   RandomSetOfUniqueValues<int64_t>(
                       bitgen, /*min_value=*/0,
                       /*max_value=*/0x00'FF'FF'FF'FF'FF, count));
  ASSIGN_OR_RETURN(auto instances, RandomSetOfUniqueValues<int32_t>(
                                       bitgen, /*min_value=*/0,
                                       /*max_value=*/0xffff, count));

  absl::btree_set<int32_t> vlan_indexes;
  if (is_ip_mcast) {
    ASSIGN_OR_RETURN(vlan_indexes,
                     RandomSetOfUniqueValues<int32_t>(
                         bitgen, /*min_value=*/0,
                         /*max_value=*/entries.vlans.size(), count));
  }

  auto instances_it = instances.begin();
  auto vlan_indexes_it = vlan_indexes.begin();
  int port_idx = 0;
  for (const auto& address : addresses) {
    netaddr::MacAddress mac(0x10'00'00'00'00'00 + address);
    int instance = *instances_it++;
    std::string port_name = absl::StrCat(entries.port_ids[port_idx]);
    port_idx = (port_idx + 1) % entries.port_ids.size();
    int32_t vlan = 0;
    if (is_ip_mcast) {
      vlan = entries.vlans[*vlan_indexes_it++];
    }
    pins::MulticastReplica replica = pins::MulticastReplica(
        port_name, instance, mac.ToString(), vlan, is_ip_mcast);
    ASSIGN_OR_RETURN(entries.rifs_by_name[replica.key],
                     pins::MulticastRouterInterfaceTableUpdate(
                         ir_p4info, p4::v1::Update::INSERT, replica));
    entries.replicas.push_back(replica);
  }
  return absl::OkStatus();
}

absl::Status GenerateRandomMulticastGroups(absl::BitGen& bitgen,
                                           MulticastEntryInfo& entries,
                                           const pdpi::IrP4Info& ir_p4info,
                                           int32_t count) {
  if (entries.replicas.empty()) {
    return absl::InvalidArgumentError(
        "Multicast ritfs need to be created before multicast groups.");
  }

  int32_t number_multicast_members_per_group =
      absl::GetFlag(FLAGS_multicast_members_per_group);

  ASSIGN_OR_RETURN(auto multicast_group_ids, RandomSetOfUniqueValues<uint16_t>(
                                                 bitgen, /*min_value=*/1,
                                                 /*max_value=*/0xFFFF, count));

  for (const auto& multicast_group_id : multicast_group_ids) {
    std::string multicast_group_name =
        absl::StrCat("multicast-group-", multicast_group_id);
    std::vector<pins::MulticastReplica> replicas_to_use;
    ASSIGN_OR_RETURN(
        auto replica_indexes,
        RandomSetOfUniqueValues<int>(bitgen, /*min_value=*/0,
                                     /*max_value=*/entries.replicas.size() - 1,
                                     number_multicast_members_per_group));
    for (const int replica_index : replica_indexes) {
      replicas_to_use.push_back(entries.replicas[replica_index]);
    }
    absl::Span<pins::MulticastReplica> replicas_span{replicas_to_use};
    ASSIGN_OR_RETURN(
        entries.mcast_groups_by_name[multicast_group_name],
        pins::MulticastGroupUpdate(ir_p4info, p4::v1::Update::INSERT,
                                   multicast_group_id, replicas_span));
    entries.mcast_groups.push_back(multicast_group_id);
  }
  return absl::OkStatus();
}

absl::StatusOr<P4WriteRequests> ComputeEncapNeighbors(
    absl::BitGen& bitgen, RouteEntryInfo& route_entry,
    const pdpi::IrP4Info& ir_p4info, int batch_count, int32_t encap_count) {
  ASSIGN_OR_RETURN(std::vector<std::string> rifs,
                   GetKeys(route_entry.router_interfaces_by_name),
                   _ << "RIFs need to be created before next hops");
  ASSIGN_OR_RETURN(auto addresses,
                   RandomSetOfUniqueValues<int64_t>(
                       bitgen, /*min_value=*/0,
                       /*max_value=*/0x00'FF'FF'FF'FF'FF, encap_count),
                   _ << "Failed to get " << encap_count << " of addrs");
  P4WriteRequests requests;

  for (const auto& address : addresses) {
    if (requests.inserts.empty() ||
        requests.inserts.back().updates_size() == encap_count / batch_count) {
      requests.inserts.push_back(p4::v1::WriteRequest{});
      requests.modifies.push_back(p4::v1::WriteRequest{});
      requests.deletes.push_back(p4::v1::WriteRequest{});
    }

    netaddr::MacAddress mac(0x20'00'00'00'00'00 + address);
    std::string neighbor_name = mac.ToLinkLocalIpv6Address().ToString();
    std::string nexthop_name = absl::StrCat("nh-", mac.ToString());
    std::string rif = rifs[absl::Uniform<size_t>(bitgen, 0, rifs.size())];

    ASSIGN_OR_RETURN(
        route_entry.neighbors_by_name[neighbor_name],
        pins::NeighborTableUpdate(ir_p4info, p4::v1::Update::INSERT, rif,
                                   neighbor_name, mac.ToString()));
    *requests.inserts.back().add_updates() =
        route_entry.neighbors_by_name[neighbor_name];
    route_entry.neighbor_to_router_interface_name[neighbor_name] = rif;

    // DELETE the entry.
    ASSIGN_OR_RETURN(
        *requests.deletes.back().add_updates(),
        pins::NeighborTableUpdate(ir_p4info, p4::v1::Update::DELETE, rif,
                                   neighbor_name, mac.ToString()));
  }
  return requests;
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
                   RandomSetOfUniqueValues<int32_t>(
                       bitgen, /*min_value=*/0x0100'0000,
                       /*max_value=*/0x1FFF'FFFF, number_batches * batch_size));

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
        pins::Ipv4TableUpdate(
            ir_p4info, p4::v1::Update::INSERT,
            pins::IpTableOptions{
                .vrf_id = vrf,
                .dst_addr_lpm = std::make_pair(ip.ToString(), 32),
                .action = pins::IpTableOptions::Action::kSetNextHopId,
                .nexthop_id = nexthop,
            }));

    // MODIFY the nexthop action.
    nexthop = nexthops[absl::Uniform<size_t>(bitgen, 0, nexthops.size())];
    ASSIGN_OR_RETURN(
        *requests.modifies.back().add_updates(),
        pins::Ipv4TableUpdate(
            ir_p4info, p4::v1::Update::MODIFY,
            pins::IpTableOptions{
                .vrf_id = vrf,
                .dst_addr_lpm = std::make_pair(ip.ToString(), 32),
                .action = pins::IpTableOptions::Action::kSetNextHopId,
                .nexthop_id = nexthop,
            }));

    // DELETE the entry.
    ASSIGN_OR_RETURN(
        *requests.deletes.back().add_updates(),
        pins::Ipv4TableUpdate(
            ir_p4info, p4::v1::Update::DELETE,
            pins::IpTableOptions{
                .vrf_id = vrf,
                .dst_addr_lpm = std::make_pair(ip.ToString(), 32),
                .action = pins::IpTableOptions::Action::kSetNextHopId,
                .nexthop_id = nexthop,
            }));
  }

  RETURN_IF_ERROR(
      VerifyP4WriteRequestSizes(requests, number_batches, batch_size));
  return requests;
}

// WCMP entries are required to have a positive weight. This method will assign
// a weight of 1 to all members (i.e. even if the `total_group_weight` is less
// than the `size`). Then it will assign any remaining weight randomly.
std::vector<int> RandomizeWeights(absl::BitGen& bitgen, int size,
                                  int total_group_weight) {
  // All actions need at least a weight of 1 to be functionally correct.
  std::vector<int> weights(size, 1);
  int remaining_weight = total_group_weight - size;
  int unique_weights_per_group =
      absl::GetFlag(FLAGS_wcmp_unique_weights_per_group);

  // If there is any weights remaining then we assign them randomly across
  // the actions. Keep track of total unique weights in the group as well,
  // reserve one weight to fill in for what randomization cannot assign.
  absl::flat_hash_set<int> unique_weights = {1};
  int count = 0;
  while (remaining_weight > 0 && count < 2 * total_group_weight) {
    int selected_index = absl::Uniform<size_t>(bitgen, 0, weights.size());
    int selected_weight = weights[selected_index];
    if (!unique_weights.contains(selected_weight + 1) &&
        unique_weights.size() >= (unique_weights_per_group - 1)) {
      ++count;
      continue;
    }
    ++weights[selected_index];
    unique_weights.insert(weights[selected_index]);
    // Remove previous weight from the unique weights set if it does not exist
    // anymore.
    if (std::find(weights.begin(), weights.end(), selected_weight) ==
        weights.end()) {
      unique_weights.erase(selected_weight);
    }
    --remaining_weight;
  }
  // Add the remaining weight, if any, to the first action.
  weights[0] += remaining_weight;

  // Switches can preallocate weights as members are added. The worst case
  // is when weights get larger and larger with the members. Users can set a
  // flag to force this behavior (i.e. get worst case performance).
  if (absl::GetFlag(FLAGS_wcmp_increasing_weights)) {
    std::sort(weights.begin(), weights.end());
  }

  return weights;
}

absl::StatusOr<std::vector<pins::WcmpAction>> ComputeWcmpGroupAction(
    absl::BitGen& bitgen, int members_per_group, bool set_watch_port,
    const std::vector<std::string>& nexthops,
    const absl::flat_hash_map<std::string, std::string>& port_by_nexthop_name) {
  std::vector<pins::WcmpAction> actions(members_per_group);

  // Get a random set of next hops, but don't allow duplicates.
  ASSIGN_OR_RETURN(auto nexthop_indices,
                   RandomSetOfUniqueValues<size_t>(bitgen, 0, nexthops.size(),
                                                   members_per_group));

  int action_num = 0;
  for (const auto& nexthop : nexthop_indices) {
    std::string nexthop_name = nexthops[nexthop];
    actions[action_num].nexthop_id = nexthop_name;

    if (set_watch_port) {
      const std::string* port_name =
          gutil::FindOrNull(port_by_nexthop_name, nexthop_name);
      if (port_name == nullptr) {
        return gutil::NotFoundErrorBuilder()
               << "Could not find port for nexthop '" << nexthop_name << "'.";
      }
      actions[action_num].watch_port = *port_name;
    }

    ++action_num;
  }

  return actions;
}

absl::StatusOr<P4WriteRequests> ComputeWcmpWriteRequests(
    absl::BitGen& bitgen, const RouteEntryInfo& routes,
    const pdpi::IrP4Info& ir_p4info, uint32_t number_batches,
    uint32_t batch_size, int members_per_group, bool randomize_weights,
    int total_group_weight) {
  bool change_weights_on_modify =
      absl::GetFlag(FLAGS_wcmp_update_weights_when_modifying);
  bool change_nexthops_on_modify =
      absl::GetFlag(FLAGS_wcmp_update_nexthops_when_modifying);
  if (!change_weights_on_modify && !change_nexthops_on_modify) {
    LOG(WARNING) << "We are not changing the weights or the nexthops on modify "
                    "so all requests will match the inserts.";
  }

  bool set_watch_port = absl::GetFlag(FLAGS_wcmp_set_watch_port);

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
      ASSIGN_OR_RETURN(
          std::vector<pins::WcmpAction> actions,
          ComputeWcmpGroupAction(bitgen, members_per_group, set_watch_port,
                                 nexthops, routes.port_by_next_hop_name));

      std::vector<int> weights;
      if (randomize_weights) {
        weights = RandomizeWeights(bitgen, actions.size(), total_group_weight);
      } else {
        weights = std::vector<int>(members_per_group, 1);
      }
      for (size_t i = 0; i < actions.size(); ++i) {
        actions[i].weight = weights[i];
      }

      ASSIGN_OR_RETURN(
          *requests.inserts[batch_num].add_updates(),
          pins::WcmpGroupTableUpdate(ir_p4info, p4::v1::Update::INSERT,
                                      group_name, actions));
      VLOG(1) << "WCMP insert: "
              << requests.inserts[batch_num].ShortDebugString();

      // MODIFY the nexthop actions and/or weights depending on FLAGs.
      if (change_nexthops_on_modify) {
        ASSIGN_OR_RETURN(actions, ComputeWcmpGroupAction(
                                      bitgen, members_per_group, set_watch_port,
                                      nexthops, routes.port_by_next_hop_name));
      }
      if (change_weights_on_modify) {
        weights = RandomizeWeights(bitgen, actions.size(), total_group_weight);
        for (size_t i = 0; i < actions.size(); ++i) {
          actions[i].weight = weights[i];
        }
      }
      ASSIGN_OR_RETURN(
          *requests.modifies[batch_num].add_updates(),
          pins::WcmpGroupTableUpdate(ir_p4info, p4::v1::Update::MODIFY,
                                      group_name, actions));
      VLOG(1) << "WCMP modify: "
              << requests.modifies[batch_num].ShortDebugString();

      // DELETE the entries.
      ASSIGN_OR_RETURN(
          *requests.deletes[batch_num].add_updates(),
          pins::WcmpGroupTableUpdate(ir_p4info, p4::v1::Update::DELETE,
                                      group_name, actions));
      VLOG(1) << "WCMP delete: "
              << requests.deletes[batch_num].ShortDebugString();
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
      VerifyP4WriteRequestSizes(requests, number_batches, batch_size));
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
      RandomSetOfUniqueValues<int64_t>(
          bitgen, /*min_value=*/0x0000'0000'0000'0001,
          /*max_value=*/0x1FFF'FFFF'FFFF'FFFF, number_batches * batch_size));

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
        pins::Ipv6TableUpdate(
            ir_p4info, p4::v1::Update::INSERT,
            pins::IpTableOptions{
                .vrf_id = vrf,
                .dst_addr_lpm = std::make_pair(ip.ToString(), 64),
                .action = pins::IpTableOptions::Action::kSetNextHopId,
                .nexthop_id = nexthop,
            }));

    // MODIFY the nexthop action.
    nexthop = nexthops[absl::Uniform<size_t>(bitgen, 0, nexthops.size())];
    ASSIGN_OR_RETURN(
        *requests.modifies.back().add_updates(),
        pins::Ipv6TableUpdate(
            ir_p4info, p4::v1::Update::MODIFY,
            pins::IpTableOptions{
                .vrf_id = vrf,
                .dst_addr_lpm = std::make_pair(ip.ToString(), 64),
                .action = pins::IpTableOptions::Action::kSetNextHopId,
                .nexthop_id = nexthop,
            }));

    // DELETE the entry.
    ASSIGN_OR_RETURN(
        *requests.deletes.back().add_updates(),
        pins::Ipv6TableUpdate(
            ir_p4info, p4::v1::Update::DELETE,
            pins::IpTableOptions{
                .vrf_id = vrf,
                .dst_addr_lpm = std::make_pair(ip.ToString(), 64),
                .action = pins::IpTableOptions::Action::kSetNextHopId,
                .nexthop_id = nexthop,
            }));
  }

  RETURN_IF_ERROR(
      VerifyP4WriteRequestSizes(requests, number_batches, batch_size));
  return requests;
}

// Encap tunnel needs the following objects and is referenced by nexthop.
// Nexthop group -> Nexthop tunnel -> Tunnel -> Neighbor, RouterInterface
absl::StatusOr<P4WriteRequests> ComputeEncapWriteRequests(
    absl::BitGen& bitgen, RouteEntryInfo& route_entry,
    const pdpi::IrP4Info& ir_p4info, int num_batches, uint32_t num_encaps) {
  if (route_entry.neighbors_by_name.size() != num_encaps) {
    return absl::InvalidArgumentError(
        absl::Substitute("Not enough neighbors, required $0, got $1",
                         num_encaps, route_entry.neighbors_by_name.size()));
  }

  ASSIGN_OR_RETURN(std::vector<std::string> neighbors,
                   GetKeys(route_entry.neighbors_by_name),
                   _ << "Neighbors need to be created before Tunnel encap");
  ASSIGN_OR_RETURN(auto addresses,
                   RandomSetOfUniqueValues<int64_t>(
                       bitgen, /*min_value=*/0x0000'0000'0000'0001,
                       /*max_value=*/0x1FFF'FFFF'FFFF'FFFF, num_encaps),
                   _ << "Failed to get " << num_encaps
                     << " addresses for encap write requests");

  int batch_size = num_encaps / num_batches;
  int neighbor_index = 0;
  int count = 0;
  P4WriteRequests requests;
  for (const int64_t address : addresses) {
    if (count == 0 || count == batch_size) {
      count = 0;
      requests.inserts.push_back(p4::v1::WriteRequest{});
      requests.modifies.push_back(p4::v1::WriteRequest{});
      requests.deletes.push_back(p4::v1::WriteRequest{});
    }

    // The initial INSERT request.
    netaddr::Ipv6Address src_ip6(absl::MakeUint128(address, /*low=*/0));
    std::string neighbor = neighbors[neighbor_index++];

    std::string router_interface_id =
        route_entry.neighbor_to_router_interface_name.at(neighbor);
    std::string tunnel_name = absl::StrCat("tunnel-", neighbor);
    std::string nexthop_name = absl::StrCat("nh-", tunnel_name);

    ASSIGN_OR_RETURN(*requests.inserts.back().add_updates(),
                     pins::TunnelTableUpdate(
                         ir_p4info, p4::v1::Update::INSERT, tunnel_name,
                         neighbor, src_ip6.ToString(), router_interface_id));

    ASSIGN_OR_RETURN(
        route_entry.next_hops_by_name[nexthop_name],
        pins::NexthopTunnelTableUpdate(ir_p4info, p4::v1::Update::INSERT,
                                        nexthop_name, tunnel_name));
    *requests.inserts.back().add_updates() =
        route_entry.next_hops_by_name[nexthop_name];

    // MODIFY not supported for Tunnels.

    // DELETE the entry.
    ASSIGN_OR_RETURN(
        *requests.deletes.back().add_updates(),
        pins::NexthopTunnelTableUpdate(ir_p4info, p4::v1::Update::DELETE,
                                        nexthop_name, tunnel_name));

    ASSIGN_OR_RETURN(*requests.deletes.back().add_updates(),
                     pins::TunnelTableUpdate(
                         ir_p4info, p4::v1::Update::DELETE, tunnel_name,
                         neighbor, src_ip6.ToString(), router_interface_id));

    count++;
  }

  // Sort the requests based on dependency ordering and keep like entries
  // together for efficiency. Deletes follow the reverse order.
  for (auto& insert : requests.inserts) {
    RETURN_IF_ERROR(
        pdpi::StableSortUpdates(ir_p4info, *insert.mutable_updates()));
  }
  for (auto& deletes : requests.deletes) {
    RETURN_IF_ERROR(pdpi::StableSortUpdates(
        ir_p4info, *deletes.mutable_updates(), /*reverse_ordering=*/true));
  }

  RETURN_IF_ERROR(VerifyP4WriteRequestSizes(
      requests, num_batches, batch_size * 2, /*modify_supported=*/false));
  return requests;
}

absl::StatusOr<P4WriteRequests> ComputeVlanWriteRequests(
    absl::BitGen& bitgen, const MulticastEntryInfo& entries,
    const pdpi::IrP4Info& ir_p4info, uint32_t number_batches,
    uint32_t batch_size) {
  ASSIGN_OR_RETURN(auto vlans,
                   RandomSetOfUniqueValues<int32_t>(
                       bitgen, /*min_value=*/2,
                       /*max_value=*/0x0FFF, number_batches * batch_size));

  P4WriteRequests requests;
  for (const auto& vlan : vlans) {
    if (requests.inserts.empty() ||
        requests.inserts.back().updates_size() == batch_size) {
      requests.inserts.push_back(p4::v1::WriteRequest{});
      requests.modifies.push_back(p4::v1::WriteRequest{});
      requests.deletes.push_back(p4::v1::WriteRequest{});
    }
    ASSIGN_OR_RETURN(
        *requests.inserts.back().add_updates(),
        pins::VlanTableUpdate(ir_p4info, p4::v1::Update::INSERT, vlan));
    ASSIGN_OR_RETURN(
        *requests.deletes.back().add_updates(),
        pins::VlanTableUpdate(ir_p4info, p4::v1::Update::DELETE, vlan));
  }

  RETURN_IF_ERROR(VerifyP4WriteRequestSizes(
      requests, number_batches, batch_size, /*modify_supported=*/false));
  return requests;
}

absl::StatusOr<P4WriteRequests> ComputeVlanMemberWriteRequests(
    absl::BitGen& bitgen, const MulticastEntryInfo& entries,
    const pdpi::IrP4Info& ir_p4info, uint32_t number_batches,
    uint32_t batch_size) {
  if (entries.port_ids.empty()) {
    return absl::InvalidArgumentError(
        "Port IDs need to be created before vlan members");
  }

  if ((number_batches * batch_size) >
      entries.port_ids.size() * entries.vlans.size()) {
    return absl::InvalidArgumentError(absl::StrCat(
        "The batch size * number of batches (", number_batches * batch_size,
        ") must be less than the max vlan menbers allowed: ",
        entries.port_ids.size() * entries.vlans.size()));
  }

  P4WriteRequests requests;
  int count = 0;
  for (const auto& vlan : entries.vlans) {
    for (const auto& port_id : entries.port_ids) {
      if (requests.inserts.empty() ||
          requests.inserts.back().updates_size() == batch_size) {
        requests.inserts.push_back(p4::v1::WriteRequest{});
        requests.modifies.push_back(p4::v1::WriteRequest{});
        requests.deletes.push_back(p4::v1::WriteRequest{});
      }
      bool tag = absl::Bernoulli(bitgen, 0.5);
      ASSIGN_OR_RETURN(
          *requests.inserts.back().add_updates(),
          pins::VlanMemberTableUpdate(ir_p4info, p4::v1::Update::INSERT,
                                      port_id, vlan, tag));
      ASSIGN_OR_RETURN(
          *requests.deletes.back().add_updates(),
          pins::VlanMemberTableUpdate(ir_p4info, p4::v1::Update::DELETE,
                                      port_id, vlan, tag));
      if (++count >= (number_batches * batch_size)) {
        break;
      }
    }
    if (count >= (number_batches * batch_size)) {
      break;
    }
  }

  RETURN_IF_ERROR(VerifyP4WriteRequestSizes(
      requests, number_batches, batch_size, /*modify_supported=*/false));
  return requests;
}

absl::StatusOr<P4WriteRequests> ComputeIpMulticastIntfWriteRequests(
    absl::BitGen& bitgen, const MulticastEntryInfo& entries,
    const pdpi::IrP4Info& ir_p4info, uint32_t number_batches,
    uint32_t batch_size, bool is_ip_mcast) {
  if (entries.port_ids.empty()) {
    return absl::InvalidArgumentError(
        "Port IDs need to be created before RIFs");
  }
  if (is_ip_mcast && entries.vlans.empty()) {
    return absl::InvalidArgumentError("Vlan need to be created before RIFs");
  }
  if ((number_batches * batch_size) > kMaxVlans) {
    return absl::InvalidArgumentError(absl::StrCat(
        "The batch size * number of batches (", number_batches * batch_size,
        ") must be less than the max vlan allowed: ", kMaxVlans));
  }

  ASSIGN_OR_RETURN(auto addresses, RandomSetOfUniqueValues<int64_t>(
                                       bitgen, /*min_value=*/0,
                                       /*max_value=*/0x00'FF'FF'FF'FF'FF,
                                       number_batches * batch_size));
  ASSIGN_OR_RETURN(auto instances,
                   RandomSetOfUniqueValues<int32_t>(
                       bitgen, /*min_value=*/0,
                       /*max_value=*/0xffff, number_batches * batch_size));
  absl::btree_set<int32_t> vlan_indexes;
  if (is_ip_mcast) {
    ASSIGN_OR_RETURN(vlan_indexes, RandomSetOfUniqueValues<int32_t>(
                                       bitgen, /*min_value=*/0,
                                       /*max_value=*/entries.vlans.size(),
                                       number_batches * batch_size));
  }

  auto instances_it = instances.begin();
  auto vlan_indexes_it = vlan_indexes.begin();
  P4WriteRequests requests;
  for (const auto& address : addresses) {
    if (requests.inserts.empty() ||
        requests.inserts.back().updates_size() == batch_size) {
      requests.inserts.push_back(p4::v1::WriteRequest{});
      requests.modifies.push_back(p4::v1::WriteRequest{});
      requests.deletes.push_back(p4::v1::WriteRequest{});
    }
    netaddr::MacAddress mac(0x10'00'00'00'00'00 + address);
    int instance = *instances_it++;
    std::string port_name = absl::StrCat(entries.port_ids[absl::Uniform<size_t>(
        bitgen, 0, entries.port_ids.size())]);
    int32_t vlan = 2;
    if (is_ip_mcast) {
      vlan = entries.vlans[*vlan_indexes_it++];
    }
    pins::MulticastReplica replica = pins::MulticastReplica(
        port_name, instance, mac.ToString(), vlan, is_ip_mcast);
    ASSIGN_OR_RETURN(*requests.inserts.back().add_updates(),
                     pins::MulticastRouterInterfaceTableUpdate(
                         ir_p4info, p4::v1::Update::INSERT, replica));
    ASSIGN_OR_RETURN(*requests.deletes.back().add_updates(),
                     pins::MulticastRouterInterfaceTableUpdate(
                         ir_p4info, p4::v1::Update::DELETE, replica));
  }

  RETURN_IF_ERROR(VerifyP4WriteRequestSizes(
      requests, number_batches, batch_size, /*modify_supported=*/false));
  return requests;
}

absl::StatusOr<P4WriteRequests> ComputeIpMulticastWriteRequests(
    absl::BitGen& bitgen, const MulticastEntryInfo& entries,
    const pdpi::IrP4Info& ir_p4info, uint32_t number_batches,
    uint32_t batch_size) {
  if ((number_batches * batch_size) > kMaxIpMulticastGroups) {
    return absl::InvalidArgumentError(absl::StrCat(
        "The batch size * number of batches (", number_batches * batch_size,
        ") must be less than the max IP multicast groups allowed: ",
        kMaxIpMulticastGroups));
  }

  ASSIGN_OR_RETURN(std::vector<std::string> rifs, GetKeys(entries.rifs_by_name),
                   _ << "RIFs need to be created before multicast groups");

  int32_t number_multicast_members_per_group =
      absl::GetFlag(FLAGS_multicast_members_per_group);

  if (number_multicast_members_per_group > entries.replicas.size()) {
    return absl::InvalidArgumentError(absl::StrCat(
        "The number of multicast members per group (",
        number_multicast_members_per_group,
        ") must be less than or equal to the number of RIFs created (",
        entries.replicas.size(), ")"));
  }

  ASSIGN_OR_RETURN(auto multicast_group_ids,
                   RandomSetOfUniqueValues<uint16_t>(
                       bitgen, /*min_value=*/1, /*max_value=*/0xFFFF,
                       number_batches * batch_size));

  P4WriteRequests requests;
  for (const uint16_t group_id : multicast_group_ids) {
    if (requests.inserts.empty() ||
        requests.inserts.back().updates_size() == batch_size) {
      requests.inserts.push_back(p4::v1::WriteRequest{});
      requests.modifies.push_back(p4::v1::WriteRequest{});
      requests.deletes.push_back(p4::v1::WriteRequest{});
    }
    std::vector<pins::MulticastReplica> replicas_to_use;
    ASSIGN_OR_RETURN(
        auto replica_indexes,
        RandomSetOfUniqueValues<int>(bitgen, /*min_value=*/0,
                                     /*max_value=*/entries.replicas.size() - 1,
                                     number_multicast_members_per_group));
    for (const int replica_index : replica_indexes) {
      replicas_to_use.push_back(entries.replicas[replica_index]);
    }

    // The initial INSERT request.
    absl::Span<pins::MulticastReplica> replicas_span{replicas_to_use};
    ASSIGN_OR_RETURN(
        *requests.inserts.back().add_updates(),
        pins::MulticastGroupUpdate(ir_p4info, p4::v1::Update::INSERT, group_id,
                                    replicas_span));

    // MODIFY replicas to use.
    std::vector<pins::MulticastReplica> replicas_to_use_modify;
    ASSIGN_OR_RETURN(
        auto replica_indexes_modify,
        RandomSetOfUniqueValues<int>(bitgen, /*min_value=*/0,
                                     /*max_value=*/entries.replicas.size() - 1,
                                     number_multicast_members_per_group));
    for (const int replica_index_modify : replica_indexes_modify) {
      replicas_to_use_modify.push_back(entries.replicas[replica_index_modify]);
    }

    absl::Span<pins::MulticastReplica> replicas_modify_span{
        replicas_to_use_modify};
    ASSIGN_OR_RETURN(
        *requests.modifies.back().add_updates(),
        pins::MulticastGroupUpdate(ir_p4info, p4::v1::Update::MODIFY, group_id,
                                    replicas_modify_span));

    // DELETE the entry.
    ASSIGN_OR_RETURN(
        *requests.deletes.back().add_updates(),
        pins::MulticastGroupUpdate(ir_p4info, p4::v1::Update::DELETE, group_id,
                                    replicas_modify_span));
  }

  RETURN_IF_ERROR(
      VerifyP4WriteRequestSizes(requests, number_batches, batch_size));
  return requests;
}

absl::StatusOr<P4WriteRequests> ComputeIv4MulticastRouteWriteRequests(
    absl::BitGen& bitgen, const RouteEntryInfo& routes,
    const MulticastEntryInfo& entries, const pdpi::IrP4Info& ir_p4info,
    uint32_t number_batches, uint32_t batch_size) {
  ASSIGN_OR_RETURN(std::vector<std::string> vrfs, GetKeys(routes.vrfs_by_name),
                   _ << "VRFs need to be created before IPv4 multicast routes");
  ASSIGN_OR_RETURN(auto addresses, RandomSetOfUniqueValues<int32_t>(
                                       bitgen, /*min_value=*/0xE0'00'00'00,
                                       /*max_value=*/0xEF'FF'FF'FF,
                                       number_batches * batch_size));

  P4WriteRequests requests;
  for (const int32_t address : addresses) {
    if (requests.inserts.empty() ||
        requests.inserts.back().updates_size() == batch_size) {
      requests.inserts.push_back(p4::v1::WriteRequest{});
      requests.modifies.push_back(p4::v1::WriteRequest{});
      requests.deletes.push_back(p4::v1::WriteRequest{});
    }
    std::string vrf = vrfs[absl::Uniform<size_t>(bitgen, 0, vrfs.size())];
    int32_t mcast_group_id = entries.mcast_groups[absl::Uniform<size_t>(
        bitgen, 0, entries.mcast_groups.size())];
    netaddr::Ipv4Address ip(address);
    ASSIGN_OR_RETURN(
        *requests.inserts.back().add_updates(),
        pins::Ipv4MulticastRouteUpdate(ir_p4info, p4::v1::Update::INSERT, vrf,
                                       ip.ToString(), mcast_group_id));

    mcast_group_id = entries.mcast_groups[absl::Uniform<size_t>(
        bitgen, 0, entries.mcast_groups.size())];
    ASSIGN_OR_RETURN(
        *requests.modifies.back().add_updates(),
        pins::Ipv4MulticastRouteUpdate(ir_p4info, p4::v1::Update::MODIFY, vrf,
                                       ip.ToString(), mcast_group_id));

    ASSIGN_OR_RETURN(
        *requests.deletes.back().add_updates(),
        pins::Ipv4MulticastRouteUpdate(ir_p4info, p4::v1::Update::DELETE, vrf,
                                       ip.ToString(), mcast_group_id));
  }

  RETURN_IF_ERROR(
      VerifyP4WriteRequestSizes(requests, number_batches, batch_size));
  return requests;
}

absl::StatusOr<P4WriteRequests> ComputeIv6MulticastRouteWriteRequests(
    absl::BitGen& bitgen, const RouteEntryInfo& routes,
    const MulticastEntryInfo& entries, const pdpi::IrP4Info& ir_p4info,
    uint32_t number_batches, uint32_t batch_size) {
  ASSIGN_OR_RETURN(std::vector<std::string> vrfs, GetKeys(routes.vrfs_by_name),
                   _ << "VRFs need to be created before IPv6 multicast routes");
  ASSIGN_OR_RETURN(
      auto addresses,
      RandomSetOfUniqueValues<int64_t>(
          bitgen, /*min_value=*/0xFF00'0000'0000'0000,
          /*max_value=*/0xFFFF'FFFF'FFFF'FFFF, number_batches * batch_size));

  P4WriteRequests requests;
  for (const int64_t address : addresses) {
    if (requests.inserts.empty() ||
        requests.inserts.back().updates_size() == batch_size) {
      requests.inserts.push_back(p4::v1::WriteRequest{});
      requests.modifies.push_back(p4::v1::WriteRequest{});
      requests.deletes.push_back(p4::v1::WriteRequest{});
    }
    std::string vrf = vrfs[absl::Uniform<size_t>(bitgen, 0, vrfs.size())];
    int32_t mcast_group_id = entries.mcast_groups[absl::Uniform<size_t>(
        bitgen, 0, entries.mcast_groups.size())];
    netaddr::Ipv6Address ip(absl::MakeUint128(address, /*low=*/0));
    ASSIGN_OR_RETURN(
        *requests.inserts.back().add_updates(),
        pins::Ipv6MulticastRouteUpdate(ir_p4info, p4::v1::Update::INSERT, vrf,
                                       ip.ToString(), mcast_group_id));

    mcast_group_id = entries.mcast_groups[absl::Uniform<size_t>(
        bitgen, 0, entries.mcast_groups.size())];
    ASSIGN_OR_RETURN(
        *requests.modifies.back().add_updates(),
        pins::Ipv6MulticastRouteUpdate(ir_p4info, p4::v1::Update::MODIFY, vrf,
                                       ip.ToString(), mcast_group_id));

    ASSIGN_OR_RETURN(
        *requests.deletes.back().add_updates(),
        pins::Ipv6MulticastRouteUpdate(ir_p4info, p4::v1::Update::DELETE, vrf,
                                       ip.ToString(), mcast_group_id));
  }

  RETURN_IF_ERROR(
      VerifyP4WriteRequestSizes(requests, number_batches, batch_size));
  return requests;
}

TEST_F(P4rtRouteTest, MeasureWriteLatency) {
  int32_t number_of_batches = absl::GetFlag(FLAGS_number_batches);
  int32_t requests_per_batch = absl::GetFlag(FLAGS_batch_size);
  std::string available_port_ids = absl::GetFlag(FLAGS_port_ids);
  int32_t number_of_vrfs = absl::GetFlag(FLAGS_vrfs);
  int32_t number_of_rifs = absl::GetFlag(FLAGS_rifs);
  int32_t number_of_nexthops = absl::GetFlag(FLAGS_next_hops);
  int32_t number_of_encaps = absl::GetFlag(FLAGS_encaps);

  // Randomly generate the routes that will be used by these tests.
  absl::BitGen bitgen(GetSeedSeq());
  RouteEntryInfo routes;
  MulticastEntryInfo entries;

  bool test_vlan = absl::GetFlag(FLAGS_run_vlan);
  bool test_vlan_member = absl::GetFlag(FLAGS_run_vlan_member);
  bool test_ip_mcast_ritf = absl::GetFlag(FLAGS_run_ip_mcast_ritf);
  bool test_l2_mcast_ritf = absl::GetFlag(FLAGS_run_l2_mcast_ritf);
  bool test_ip_multicast = absl::GetFlag(FLAGS_run_ip_multicast);
  bool test_l2_multicast = absl::GetFlag(FLAGS_run_l2_multicast);
  bool test_ipv4_multicast = absl::GetFlag(FLAGS_run_ipv4_mcast_routes);
  bool test_ipv6_multicast = absl::GetFlag(FLAGS_run_ipv6_mcast_routes);

  ASSERT_OK_AND_ASSIGN(routes.port_ids, ParseIds(available_port_ids));
  entries.port_ids = routes.port_ids;
  std::vector<p4::v1::WriteRequest> premeasurement_requests;

  if (test_vlan || test_l2_mcast_ritf) {
    // No pre-measurement.
  } else if (test_vlan_member) {
    // Create vlans.
    ASSERT_OK(GenerateRandomVlans(bitgen, entries, ir_p4info_, kMaxVlans));
    AppendUpdatesToWriteRequest(premeasurement_requests.emplace_back(),
                                entries.vlans_by_name);

  } else if (test_ip_mcast_ritf) {
    // Create vlans and vlan members.
    ASSERT_OK(
        GenerateRandomVlansAndMembers(bitgen, entries, ir_p4info_, kMaxVlans));
    AppendUpdatesToWriteRequest(premeasurement_requests.emplace_back(),
                                entries.vlans_by_name);
    AppendUpdatesToWriteRequest(premeasurement_requests.emplace_back(),
                                entries.vlan_members_by_name);
  } else if (test_ip_multicast || test_l2_multicast) {
    if (test_ip_multicast) {
      // Create vlans and vlan members.
      ASSERT_OK(GenerateRandomVlansAndMembers(bitgen, entries, ir_p4info_,
                                              kMaxVlans));
      AppendUpdatesToWriteRequest(premeasurement_requests.emplace_back(),
                                  entries.vlans_by_name);
      AppendUpdatesToWriteRequest(premeasurement_requests.emplace_back(),
                                  entries.vlan_members_by_name);
    }
    ASSERT_OK(GenerateRandomMulticastRIFs(bitgen, entries, ir_p4info_,
                                          test_ip_multicast, number_of_rifs));
    AppendUpdatesToWriteRequest(premeasurement_requests.emplace_back(),
                                entries.rifs_by_name);
  } else if (test_ipv4_multicast || test_ipv6_multicast) {
    ASSERT_OK(
        GenerateRandomVlansAndMembers(bitgen, entries, ir_p4info_, kMaxVlans));
    ASSERT_OK(GenerateRandomMulticastRIFs(bitgen, entries, ir_p4info_,
                                          /*is_ip_mcast=*/true,
                                          number_of_rifs));
    ASSERT_OK(GenerateRandomMulticastGroups(bitgen, entries, ir_p4info_,
                                            kMaxIpMulticastGroups));
    ASSERT_OK(GenerateRandomVrfs(bitgen, routes, ir_p4info_, number_of_vrfs));
    AppendUpdatesToWriteRequest(premeasurement_requests.emplace_back(),
                                entries.vlans_by_name);
    AppendUpdatesToWriteRequest(premeasurement_requests.emplace_back(),
                                entries.vlan_members_by_name);
    AppendUpdatesToWriteRequest(premeasurement_requests.emplace_back(),
                                entries.rifs_by_name);
    AppendUpdatesToWriteRequest(premeasurement_requests.emplace_back(),
                                entries.mcast_groups_by_name);
    AppendUpdatesToWriteRequest(premeasurement_requests.emplace_back(),
                                routes.vrfs_by_name);
  } else {
    ASSERT_OK(GenerateRandomRIFs(bitgen, routes, ir_p4info_, number_of_rifs));
    ASSERT_OK(GenerateRandomVrfs(bitgen, routes, ir_p4info_, number_of_vrfs));
    // Tunnel nexthops are created differently later.
    if (!absl::GetFlag(FLAGS_run_encap)) {
      ASSERT_OK(GenerateRandomNextHops(bitgen, routes, ir_p4info_,
                                       number_of_nexthops));
    }

    AppendUpdatesToWriteRequest(premeasurement_requests.emplace_back(),
                                routes.vrfs_by_name);
    AppendUpdatesToWriteRequest(premeasurement_requests.emplace_back(),
                                routes.router_interfaces_by_name);
    AppendUpdatesToWriteRequest(premeasurement_requests.emplace_back(),
                                routes.neighbors_by_name);
    AppendUpdatesToWriteRequest(premeasurement_requests.emplace_back(),
                                routes.next_hops_by_name);
  }

  // Install the pre-measurement entries that are needed.
  UpdateRequestMetadata(premeasurement_requests);
  ASSERT_OK_AND_ASSIGN(absl::Duration premeasurement_time,
                       SendBatchRequest(premeasurement_requests));

  if (absl::GetFlag(FLAGS_run_ipv4)) {
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

    // Write the results to stdout so that the callers can parse the output.
    int64_t total_entries = number_of_batches * requests_per_batch;
    std::cout << absl::StreamFormat(
        "ipv4_requests=%d ipv4_entry_total=%lld "
        "ipv4_insert_time=%lld(msecs) ipv4_modify_time=%lld(msecs) ",
        number_of_batches, total_entries,
        absl::ToInt64Milliseconds(insert_time),
        absl::ToInt64Milliseconds(modify_time));
    if (absl::GetFlag(FLAGS_cleanup)) {
      ASSERT_OK_AND_ASSIGN(absl::Duration delete_time,
                           SendBatchRequest(requests.deletes));
      std::cout << absl::StreamFormat("ipv4_delete_time=%lld(msecs) ",
                                      absl::ToInt64Milliseconds(delete_time));
    }
    std::cout << std::endl;

    // TODO: remove once we migrate the Perfkit dashboard to the
    // new tags.
    std::cout << "Successfully wrote IpTable entries to the switch, time: "
              << ToInt64Milliseconds(insert_time) << "(msecs)" << std::endl;
  }

  if (absl::GetFlag(FLAGS_run_ipv6)) {
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

    // Write the results to stdout so that the callers can parse the output.
    int64_t total_entries = number_of_batches * requests_per_batch;
    std::cout << absl::StreamFormat(
        "ipv6_requests=%d ipv6_entry_total=%lld "
        "ipv6_insert_time=%lld(msecs) ipv6_modify_time=%lld(msecs) ",
        number_of_batches, total_entries,
        absl::ToInt64Milliseconds(insert_time),
        absl::ToInt64Milliseconds(modify_time));
    if (absl::GetFlag(FLAGS_cleanup)) {
      ASSERT_OK_AND_ASSIGN(absl::Duration delete_time,
                           SendBatchRequest(requests.deletes));
      std::cout << absl::StreamFormat("ipv6_delete_time=%lld(msecs) ",
                                      absl::ToInt64Milliseconds(delete_time));
    }
    std::cout << std::endl;
  }

  int members_per_group = absl::GetFlag(FLAGS_wcmp_members_per_group);
  int total_group_weight = absl::GetFlag(FLAGS_wcmp_total_group_weight);
  if (absl::GetFlag(FLAGS_run_wcmp)) {
    // Pre-compute all the WCMP requests so they can be sent as quickly as
    // possible to the switch under test.
    ASSERT_OK_AND_ASSIGN(
        P4WriteRequests requests,
        ComputeWcmpWriteRequests(
            bitgen, routes, ir_p4info_, number_of_batches, requests_per_batch,
            members_per_group, /*randomize_weights=*/true, total_group_weight));
    UpdateRequestMetadata(requests);
    ASSERT_OK_AND_ASSIGN(absl::Duration insert_time,
                         SendBatchRequest(requests.inserts));
    ASSERT_OK_AND_ASSIGN(absl::Duration modify_time,
                         SendBatchRequest(requests.modifies));

    // Write the results to stdout so that callers can parse the output.
    int64_t total_groups = number_of_batches * requests_per_batch;
    int64_t total_members = total_groups * members_per_group;
    int64_t total_weight = total_groups * total_group_weight;
    std::cout << absl::StreamFormat(
        "wcmp_requests=%d wcmp_groups_total=%lld "
        "wcmp_members_total=%lld wcmp_weight_total=%lld "
        "wcmp_insert_time=%lld(msecs) wcmp_modify_time=%lld(msecs) ",
        number_of_batches, total_groups, total_members, total_weight,
        absl::ToInt64Milliseconds(insert_time),
        absl::ToInt64Milliseconds(modify_time));
    if (absl::GetFlag(FLAGS_cleanup)) {
      ASSERT_OK_AND_ASSIGN(absl::Duration delete_time,
                           SendBatchRequest(requests.deletes));
      std::cout << absl::StreamFormat("wcmp_delete_time=%lld(msecs) ",
                                      absl::ToInt64Milliseconds(delete_time));
    }
    std::cout << absl::StreamFormat(
        "ip_multicast_init_time=%lld(msecs) ",
        absl::ToInt64Milliseconds(premeasurement_time));
    std::cout << std::endl;
  }

  if (absl::GetFlag(FLAGS_run_encap)) {
    int total_tunnels =
        number_of_batches * requests_per_batch * members_per_group;

    ASSERT_OK_AND_ASSIGN(
        P4WriteRequests encap_neighbor_requests,
        ComputeEncapNeighbors(bitgen, routes, ir_p4info_, number_of_batches,
                              number_of_encaps));
    UpdateRequestMetadata(encap_neighbor_requests);
    ASSERT_OK_AND_ASSIGN(absl::Duration encap_neighbor_insert_time,
                         SendBatchRequest(encap_neighbor_requests.inserts));

    // Pre-compute all the Tunnel encap requests so they can be sent as quickly
    // as possible to the switch under test.
    ASSERT_OK_AND_ASSIGN(
        P4WriteRequests encap_requests,
        ComputeEncapWriteRequests(bitgen, routes, ir_p4info_, number_of_batches,
                                  number_of_encaps));
    UpdateRequestMetadata(encap_requests);
    ASSERT_OK_AND_ASSIGN(absl::Duration encap_insert_time,
                         SendBatchRequest(encap_requests.inserts));

    ASSERT_OK_AND_ASSIGN(P4WriteRequests wcmp_requests,
                         ComputeWcmpWriteRequests(
                             bitgen, routes, ir_p4info_, number_of_batches,
                             requests_per_batch, members_per_group,
                             /*randomize_weights=*/false, total_group_weight));
    UpdateRequestMetadata(wcmp_requests);
    ASSERT_OK_AND_ASSIGN(absl::Duration wcmp_insert_time,
                         SendBatchRequest(wcmp_requests.inserts));

    int64_t total_groups = number_of_batches * requests_per_batch;
    std::cout << absl::StreamFormat(
        "encap_entry_total=%d wcmp_total_groups=%lld "
        "encap_insert_time=%lld(msecs) wcmp_insert_time=%lld(msecs) ",
        total_tunnels, total_groups,
        absl::ToInt64Milliseconds(encap_insert_time) +
            absl::ToInt64Milliseconds(encap_neighbor_insert_time),
        absl::ToInt64Milliseconds(wcmp_insert_time));
    if (absl::GetFlag(FLAGS_cleanup)) {
      ASSERT_OK_AND_ASSIGN(absl::Duration wcmp_delete_time,
                           SendBatchRequest(wcmp_requests.deletes));

      ASSERT_OK_AND_ASSIGN(absl::Duration encap_delete_time,
                           SendBatchRequest(encap_requests.deletes));

      ASSERT_OK_AND_ASSIGN(absl::Duration encap_neighbor_delete_time,
                           SendBatchRequest(encap_neighbor_requests.deletes));
      // Write the results to stdout so that callers can parse the output.
      std::cout << absl::StreamFormat(
          "encap_delete_time=%lld(msecs) wcmp_delete_time=%lld(msecs) ",
          absl::ToInt64Milliseconds(encap_delete_time) +
              absl::ToInt64Milliseconds(encap_neighbor_delete_time),
          absl::ToInt64Milliseconds(wcmp_delete_time));
    }
    std::cout << std::endl;
  }

  if (test_vlan) {
    ASSERT_OK_AND_ASSIGN(
        P4WriteRequests requests,
        ComputeVlanWriteRequests(bitgen, entries, ir_p4info_, number_of_batches,
                                 requests_per_batch));
    UpdateRequestMetadata(requests);
    ASSERT_OK_AND_ASSIGN(absl::Duration insert_time,
                         SendBatchRequest(requests.inserts));

    // Write the results to stdout so that the callers can parse the output.
    int64_t total_entries = number_of_batches * requests_per_batch;
    std::cout << absl::StreamFormat(
        "vlan_requests=%d vlan_entry_total=%lld "
        "vlan_insert_time=%lld(msecs) ",
        number_of_batches, total_entries,
        absl::ToInt64Milliseconds(insert_time));
    if (absl::GetFlag(FLAGS_cleanup)) {
      ASSERT_OK_AND_ASSIGN(absl::Duration delete_time,
                           SendBatchRequest(requests.deletes));
      std::cout << absl::StreamFormat("vlan_delete_time=%lld(msecs) ",
                                      absl::ToInt64Milliseconds(delete_time));
    }
    std::cout << std::endl;
  }

  if (test_vlan_member) {
    ASSERT_OK_AND_ASSIGN(
        P4WriteRequests requests,
        ComputeVlanMemberWriteRequests(bitgen, entries, ir_p4info_,
                                       number_of_batches, requests_per_batch));
    UpdateRequestMetadata(requests);
    ASSERT_OK_AND_ASSIGN(absl::Duration insert_time,
                         SendBatchRequest(requests.inserts));

    // Write the results to stdout so that the callers can parse the output.
    int64_t total_entries = number_of_batches * requests_per_batch;
    std::cout << absl::StreamFormat(
        "vlan_member_requests=%d vlan_member_entry_total=%lld "
        "vlan_member_insert_time=%lld(msecs) ",
        number_of_batches, total_entries,
        absl::ToInt64Milliseconds(insert_time));
    if (absl::GetFlag(FLAGS_cleanup)) {
      ASSERT_OK_AND_ASSIGN(absl::Duration delete_time,
                           SendBatchRequest(requests.deletes));
      std::cout << absl::StreamFormat("vlan_member_delete_time=%lld(msecs) ",
                                      absl::ToInt64Milliseconds(delete_time));
    }
    std::cout << std::endl;
  }

  if (test_ip_mcast_ritf || test_l2_mcast_ritf) {
    ASSERT_OK_AND_ASSIGN(P4WriteRequests requests,
                         ComputeIpMulticastIntfWriteRequests(
                             bitgen, entries, ir_p4info_, number_of_batches,
                             requests_per_batch, test_ip_mcast_ritf));
    UpdateRequestMetadata(requests);
    ASSERT_OK_AND_ASSIGN(absl::Duration insert_time,
                         SendBatchRequest(requests.inserts));

    // Write the results to stdout so that the callers can parse the output.
    auto test_str = test_ip_mcast_ritf ? "ip_mcast_ritf" : "l2_mcast_ritf";
    int64_t total_entries = number_of_batches * requests_per_batch;
    std::cout << absl::StreamFormat(
        "%s_requests=%d %s_entry_total=%lld "
        "%s_insert_time=%lld(msecs) ",
        test_str, number_of_batches, test_str, total_entries, test_str,
        absl::ToInt64Milliseconds(insert_time));
    if (absl::GetFlag(FLAGS_cleanup)) {
      ASSERT_OK_AND_ASSIGN(absl::Duration delete_time,
                           SendBatchRequest(requests.deletes));
      std::cout << absl::StreamFormat("%s_delete_time=%lld(msecs) ", test_str,
                                      absl::ToInt64Milliseconds(delete_time));
    }
    std::cout << std::endl;
  }

  if (test_ip_multicast || test_l2_multicast) {
    // Pre-compute all the multicast group requests so they can be sent as
    // quickly as possible to the switch under test.
    ASSERT_OK_AND_ASSIGN(
        P4WriteRequests requests,
        ComputeIpMulticastWriteRequests(bitgen, entries, ir_p4info_,
                                        number_of_batches, requests_per_batch));
    UpdateRequestMetadata(requests);
    ASSERT_OK_AND_ASSIGN(absl::Duration insert_time,
                         SendBatchRequest(requests.inserts));
    ASSERT_OK_AND_ASSIGN(absl::Duration modify_time,
                         SendBatchRequest(requests.modifies));

    // Write the results to stdout so that the callers can parse the output.
    int64_t total_entries = number_of_batches * requests_per_batch;
    std::string test_str = test_ip_multicast ? "ip_multicast" : "l2_multicast";
    std::cout << absl::StreamFormat(
        "%s_requests=%d %s_entry_total=%lld "
        "%s_insert_time=%lld(msecs) "
        "%s_modify_time=%lld(msecs) ",
        test_str, number_of_batches, test_str, total_entries, test_str,
        absl::ToInt64Milliseconds(insert_time), test_str,
        absl::ToInt64Milliseconds(modify_time));
    if (absl::GetFlag(FLAGS_cleanup)) {
      ASSERT_OK_AND_ASSIGN(absl::Duration delete_time,
                           SendBatchRequest(requests.deletes));
      std::cout << absl::StreamFormat("%s_delete_time=%lld(msecs) ", test_str,
                                      absl::ToInt64Milliseconds(delete_time));
    }
    std::cout << absl::StreamFormat(
        "%s_init_time=%lld(msecs) ", test_str,
        absl::ToInt64Milliseconds(premeasurement_time));
    std::cout << std::endl;
  }

  if (test_ipv4_multicast) {
    ASSERT_OK_AND_ASSIGN(P4WriteRequests requests,
                         ComputeIv4MulticastRouteWriteRequests(
                             bitgen, routes, entries, ir_p4info_,
                             number_of_batches, requests_per_batch));
    UpdateRequestMetadata(requests);
    ASSERT_OK_AND_ASSIGN(absl::Duration insert_time,
                         SendBatchRequest(requests.inserts));
    ASSERT_OK_AND_ASSIGN(absl::Duration modify_time,
                         SendBatchRequest(requests.modifies));

    // Write the results to stdout so that the callers can parse the output.
    int64_t total_entries = number_of_batches * requests_per_batch;
    std::cout << absl::StreamFormat(
        "ipv4_mcast_route_requests=%d ipv4_mcast_route_entry_total=%lld "
        "ipv4_mcast_route_insert_time=%lld(msecs) "
        "ipv4_mcast_route_modify_time=%lld(msecs) ",
        number_of_batches, total_entries,
        absl::ToInt64Milliseconds(insert_time),
        absl::ToInt64Milliseconds(modify_time));
    if (absl::GetFlag(FLAGS_cleanup)) {
      ASSERT_OK_AND_ASSIGN(absl::Duration delete_time,
                           SendBatchRequest(requests.deletes));
      std::cout << absl::StreamFormat(
          "ipv4_mcast_route_delete_time=%lld(msecs) ",
          absl::ToInt64Milliseconds(delete_time));
    }
    std::cout << std::endl;
  }

  if (test_ipv6_multicast) {
    ASSERT_OK_AND_ASSIGN(P4WriteRequests requests,
                         ComputeIv6MulticastRouteWriteRequests(
                             bitgen, routes, entries, ir_p4info_,
                             number_of_batches, requests_per_batch));
    UpdateRequestMetadata(requests);
    ASSERT_OK_AND_ASSIGN(absl::Duration insert_time,
                         SendBatchRequest(requests.inserts));
    ASSERT_OK_AND_ASSIGN(absl::Duration modify_time,
                         SendBatchRequest(requests.modifies));

    // Write the results to stdout so that the callers can parse the output.
    int64_t total_entries = number_of_batches * requests_per_batch;
    std::cout << absl::StreamFormat(
        "ipv6_mcast_route_requests=%d ipv6_mcast_route_entry_total=%lld "
        "ipv6_mcast_route_insert_time=%lld(msecs) "
        "ipv6_mcast_route_modify_time=%lld(msecs) ",
        number_of_batches, total_entries,
        absl::ToInt64Milliseconds(insert_time),
        absl::ToInt64Milliseconds(modify_time));
    if (absl::GetFlag(FLAGS_cleanup)) {
      ASSERT_OK_AND_ASSIGN(absl::Duration delete_time,
                           SendBatchRequest(requests.deletes));
      std::cout << absl::StreamFormat(
          "ipv6_mcast_route_delete_time=%lld(msecs) ",
          absl::ToInt64Milliseconds(delete_time));
    }
    std::cout << std::endl;
  }
}

}  // namespace
}  // namespace p4rt_app

// Temporary fix to have performance tests run nightly until we find a way to
// bring p4rt_test_main.cc to p4rt_app specific tests alone.
GTEST_API_ int main(int argc, char** argv) {
  absl::ParseCommandLine(argc, argv);
  absl::InitializeLog();
  testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
