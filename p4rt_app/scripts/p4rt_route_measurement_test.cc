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
#include <memory>
#include <vector>

#include "absl/numeric/int128.h"
#include "absl/status/statusor.h"
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
#include "gutil/io.h"
#include "gutil/proto.h"
#include "gutil/proto_matchers.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/netaddr/ipv4_address.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "sai_p4/instantiations/google/sai_p4info.h"

DEFINE_int32(batch_size, 1000, "Number of entries in each batch");
DEFINE_int32(number_batches, 10, "Number of batches");
DEFINE_int64(election_id, -1, "Election id to be used");
DEFINE_bool(insecure, true, "Use insecure channel for connection.");
DEFINE_string(hostname, "", "Hostname of the server to connect.");
DEFINE_string(ca_cert_file, "", "CA certificate file");
DEFINE_string(server_key_file, "", "Server key file");
DEFINE_string(server_cert_file, "", "Server certificate file");
// server_address should have format of <IP_address>:9559 if not unix socket
DEFINE_string(server_address, "unix:/sock/p4rt.sock",
              "The address of the server to connect to");
DEFINE_uint64(p4rt_device_id, 1, "P4RT device ID");

namespace p4rt_app {
namespace {

using ::testing::IsEmpty;
using ::testing::Test;

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

class P4rtRouteTest : public Test {
 protected:
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

  void SetUp() override {
    std::unique_ptr<::p4::v1::P4Runtime::Stub> stub;

    LOG(INFO) << "Opening P4RT connection to: " << FLAGS_server_address;
    if (FLAGS_insecure) {
      stub = pdpi::CreateP4RuntimeStub(FLAGS_server_address,
                                       grpc::InsecureChannelCredentials());
    } else {
      ASSERT_THAT(FLAGS_hostname, Not(IsEmpty()))
          << "Hostname should be provided for secure connection.";
      ASSERT_THAT(FLAGS_ca_cert_file, Not(IsEmpty()))
          << "CA certificate file should be provided for secure connection.";
      ASSERT_THAT(FLAGS_server_key_file, Not(IsEmpty()))
          << "Server key file should be provided for secure connection.";
      ASSERT_THAT(FLAGS_server_cert_file, Not(IsEmpty()))
          << "Server certificate file should be provided for secure "
             "connection.";
      grpc::SslCredentialsOptions ssl_opts;
      ASSERT_OK_AND_ASSIGN(ssl_opts.pem_root_certs,
                           gutil::ReadFile(FLAGS_ca_cert_file));
      ASSERT_OK_AND_ASSIGN(ssl_opts.pem_private_key,
                           gutil::ReadFile(FLAGS_server_key_file));
      ASSERT_OK_AND_ASSIGN(ssl_opts.pem_cert_chain,
                           gutil::ReadFile(FLAGS_server_cert_file));
      grpc::ChannelArguments args = pdpi::GrpcChannelArgumentsForP4rt();
      args.SetString(GRPC_SSL_TARGET_NAME_OVERRIDE_ARG, FLAGS_hostname);
      stub = ::p4::v1::P4Runtime::NewStub(grpc::CreateCustomChannel(
          FLAGS_server_address, grpc::SslCredentials(ssl_opts), args));
    }
    absl::uint128 election_id = absl::MakeUint128(
        (FLAGS_election_id == -1 ? absl::ToUnixSeconds(absl::Now())
                                 : FLAGS_election_id),
        0);
    ASSERT_OK_AND_ASSIGN(
        p4rt_session_,
        pdpi::P4RuntimeSession::Create(
            std::move(stub), FLAGS_p4rt_device_id,
            pdpi::P4RuntimeSessionOptionalArgs{.election_id = election_id}));
    ASSERT_OK_AND_ASSIGN(p4::v1::GetForwardingPipelineConfigResponse response,
                         pdpi::GetForwardingPipelineConfig(
                             p4rt_session_.get(),
                             p4::v1::GetForwardingPipelineConfigRequest::ALL));
    // Push P4 Info Config, only if not present.
    if (!response.has_config()) {
      ASSERT_OK(pdpi::SetForwardingPipelineConfig(
          p4rt_session_.get(),
          p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
          sai::GetP4Info(sai::Instantiation::kMiddleblock)));
    }

    // Clear the current table entries, if any.
    ASSERT_OK(pdpi::ClearTableEntries(p4rt_session_.get()));
    // Create the dependancy objects for ROUTE_ENTRY.
    // Create Router Intf object.
    ASSERT_OK(ProgramRequest(router_interface, p4::v1::Update::INSERT));
    // Create neighbor object.
    ASSERT_OK(ProgramRequest(neighbor_entry, p4::v1::Update::INSERT));
    // Create nexthop table entry.
    ASSERT_OK(ProgramRequest(nexthop_entry, p4::v1::Update::INSERT));
    // Create the vrf used for the route entries.
    ASSERT_OK(ProgramRequest(vrf_entry, p4::v1::Update::INSERT));
  }

  void TearDown() override {
    if (p4rt_session_ == nullptr) return;

    // Remove table entries that were created.
    ASSERT_OK(pdpi::ClearTableEntries(p4rt_session_.get()));
  }

  absl::StatusOr<absl::Duration> SendBatchRequest(
      absl::string_view iptable_entry, absl::string_view update_type,
      uint32_t number_batches, uint32_t batch_size) {
    // Pre-compute all requests so they can be sent as quickly as possible to
    // the switch under test.
    uint32_t ip_prefix = 0x14000000;
    uint32_t subnet0, subnet1, subnet2, subnet3;
    std::vector<p4::v1::WriteRequest> requests(number_batches);
    for (uint32_t i = 0; i < number_batches; i++) {
      // Set connection & switch IDs so the request will not be rejected by the
      // switch.
      requests[i].set_device_id(p4rt_session_->DeviceId());
      requests[i].set_role(p4rt_session_->Role());
      *requests[i].mutable_election_id() = p4rt_session_->ElectionId();

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
                absl::Substitute(iptable_entry, update_type), ptr)) {
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

  const pdpi::IrP4Info& IrP4Info() const { return ir_p4info_; }

  std::unique_ptr<pdpi::P4RuntimeSession> p4rt_session_;
  pdpi::IrP4Info ir_p4info_ =
      sai::GetIrP4Info(sai::Instantiation::kMiddleblock);
};

TEST_F(P4rtRouteTest, ProgramIp4RouteEntries) {
  ASSERT_OK_AND_ASSIGN(
      absl::Duration execution_time,
      SendBatchRequest(ip4table_entry, "INSERT", FLAGS_number_batches,
                       FLAGS_batch_size));

  // Send to stdout so that callers can parse the output.
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
