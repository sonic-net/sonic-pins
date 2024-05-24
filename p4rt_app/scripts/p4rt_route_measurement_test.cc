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
#include <cstdint>
#include <fstream>
#include <iostream>
#include <memory>
#include <random>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

#include "absl/numeric/int128.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
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
#include "p4_pdpi/netaddr/ipv4_address.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"

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

// A run will automatically generate `number_batches` write requests each with
// `batch_size` updates (i.e. number_batches x batch_size total flows). Runtime
// only includes the P4RT Write() time, and not the generation.
DEFINE_int32(number_batches, 10, "Number of batches");
DEFINE_int32(batch_size, 1000, "Number of entries in each batch");

namespace p4rt_app {
namespace {

static constexpr absl::string_view router_interface = R"pb(
  updates {
    type: INSERT
    entity {
      table_entry {
        table_id: 33554497
        match {
          field_id: 1
          exact { value: "1" }
        }
        action {
          action {
            action_id: 16777218
            params { param_id: 1 value: "1" }
            params { param_id: 2 value: "\000\002\003\004\005\005" }
          }
        }
      }
    }
  }
)pb";

static constexpr absl::string_view neighbor_entry = R"pb(
  updates {
    type: INSERT
    entity {
      table_entry {
        table_id: 33554496
        match {
          field_id: 1
          exact { value: "1" }
        }
        match {
          field_id: 2
          exact { value: "10.0.0.1" }
        }
        action {
          action {
            action_id: 16777217
            params { param_id: 1 value: "\000\032\021\027_\200" }
          }
        }
      }
    }
  }
)pb";

static constexpr absl::string_view nexthop_entry = R"pb(
  updates {
    type: INSERT
    entity {
      table_entry {
        table_id: 33554498
        match {
          field_id: 1
          exact { value: "8" }
        }
        action {
          action {
            action_id: 16777236
            params { param_id: 1 value: "1" }
            params { param_id: 2 value: "10.0.0.1" }
          }
        }
      }
    }
  }
)pb";

static constexpr absl::string_view vrf_entry = R"pb(
  updates {
    type: INSERT
    entity {
      table_entry {
        table_id: 33554506
        match {
          field_id: 1
          exact { value: "12" }
        }
        action { action { action_id: 24742814 } }
      }
    }
  }
)pb";

static constexpr absl::string_view ip4table_entry = R"pb(
  type: $0
  entity {
    table_entry {
      table_id: 33554500
      match {
        field_id: 1
        exact { value: "12" }
      }
      match {
        field_id: 2
        lpm { value: "" prefix_len: 32 }
      }
      action {
        action {
          action_id: 16777221
          params { param_id: 1 value: "8" }
        }
      }
    }
  }
)pb";

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

class P4rtRouteTest : public testing::Test {
 protected:
  void SetUp() override {
    ASSERT_OK_AND_ASSIGN(p4rt_session_, OpenP4RuntimeSession());
    ASSERT_OK_AND_ASSIGN(ir_p4info_,
                         GetExistingP4InfoOrSetDefault(
                             *p4rt_session_, sai::Instantiation::kMiddleblock));

    // Clear the current table entries, if any.
    ASSERT_OK(pdpi::ClearTableEntries(p4rt_session_.get()));

    // Create a default route for the IPv4 entries.
    ASSERT_OK(ProgramRequest(router_interface, p4::v1::Update::INSERT));
    ASSERT_OK(ProgramRequest(neighbor_entry, p4::v1::Update::INSERT));
    ASSERT_OK(ProgramRequest(nexthop_entry, p4::v1::Update::INSERT));
    ASSERT_OK(ProgramRequest(vrf_entry, p4::v1::Update::INSERT));
  }

  void TearDown() override {
    // Remove table entries that were created.
    if (p4rt_session_ != nullptr) {
      ASSERT_OK(pdpi::ClearTableEntries(p4rt_session_.get()));
    }
  }

  absl::Status ProgramRequest(absl::string_view request_str,
                              p4::v1::Update::Type type) {
    p4::v1::WriteRequest request;
    RETURN_IF_ERROR(
        gutil::ReadProtoFromString(std::string{request_str}, &request));
    request.mutable_updates(0)->set_type(type);
    RETURN_IF_ERROR(
        pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request))
        << "Failed to program the request: " << request.ShortDebugString();
    return absl::OkStatus();
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

absl::StatusOr<std::vector<p4::v1::WriteRequest>> ComputeWriteRequests(
    uint32_t number_batches, uint32_t batch_size, uint64_t device_id,
    p4::v1::Uint128 election_id, const std::string& role) {
  constexpr absl::string_view update_type = "INSERT";
  std::vector<p4::v1::WriteRequest> requests(number_batches);

  uint32_t ip_prefix = 0x14000000;
  uint32_t subnet0, subnet1, subnet2, subnet3;
  for (uint32_t i = 0; i < number_batches; i++) {
    // Set connection & switch IDs so the request will not be rejected by the
    // switch.
    requests[i].set_device_id(device_id);
    requests[i].set_role(role);
    *requests[i].mutable_election_id() = election_id;

    for (uint32_t j = 0; j < batch_size; j++) {
      subnet3 = ip_prefix & 0xff;
      subnet2 = (ip_prefix >> 8) & 0xff;
      subnet1 = (ip_prefix >> 16) & 0xff;
      subnet0 = (ip_prefix >> 24);
      const std::string ip_str =
          absl::Substitute("$0.$1.$2.$3", subnet0, subnet1, subnet2, subnet3);
      ASSIGN_OR_RETURN(const auto ip_address,
                       netaddr::Ipv4Address::OfString(ip_str));
      const auto ip_byte_str = ip_address.ToP4RuntimeByteString();
      auto* ptr = requests[i].add_updates();
      if (!google::protobuf::TextFormat::ParseFromString(
              absl::Substitute(ip4table_entry, update_type), ptr)) {
        return gutil::InvalidArgumentErrorBuilder()
               << "Could not parse text as P4 Update for Ip address: "
               << ip_byte_str;
      }
      ptr->mutable_entity()
          ->mutable_table_entry()
          ->mutable_match(1)
          ->mutable_lpm()
          ->set_value(ip_byte_str);
      ip_prefix++;
    }
  }

  return requests;
}

TEST_F(P4rtRouteTest, ProgramIp4RouteEntries) {
  int32_t number_of_batches = FLAGS_number_batches;
  int32_t requests_per_batch = FLAGS_batch_size;

  // Pre-compute all requests so they can be sent as quickly as possible to the
  // switch under test.
  ASSERT_OK_AND_ASSIGN(
      std::vector<p4::v1::WriteRequest> requests,
      ComputeWriteRequests(number_of_batches, requests_per_batch,
                           p4rt_session_->DeviceId(),
                           p4rt_session_->ElectionId(), p4rt_session_->Role()));
  ASSERT_OK_AND_ASSIGN(absl::Duration execution_time,
                       SendBatchRequest(requests));

  // Write to stdout so that callers can parse the output.
  std::cout << "Successfully wrote IpTable entries to the switch, time: "
            << ToInt64Milliseconds(execution_time) << "(msecs)" << std::endl;
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
