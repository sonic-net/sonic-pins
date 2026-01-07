// Copyright 2022 Google LLC
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
#include <cstdint>
#include <iostream>
#include <string>

#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "absl/log/initialize.h"
#include "absl/log/log.h"
#include "absl/numeric/int128.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_format.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "google/protobuf/text_format.h"
#include "grpcpp/client_context.h"
#include "grpcpp/grpcpp.h"
#include "grpcpp/security/credentials.h"
#include "gutil/gutil/io.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/status.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"

ABSL_FLAG(int32_t, number_iterations, 10, "Number of iterations");
ABSL_FLAG(int64_t, election_id, -1, "Election id to be used");
ABSL_FLAG(bool, error_if_not_primary, true,
          "Exit with error if not primary connection.");
ABSL_FLAG(bool, insecure, true, "Use insecure channel for connection.");
ABSL_FLAG(bool, backup_session, false, "Connection is backup.");
ABSL_FLAG(std::string, hostname, "", "Hostname of the server to connect.");
ABSL_FLAG(std::string, ca_cert_file, "", "CA certificate file");
ABSL_FLAG(std::string, server_key_file, "", "Server key file");
ABSL_FLAG(std::string, server_cert_file, "", "Server certificate file");
// server_address should have format of <IP_address>:9559 if not unix socket
ABSL_FLAG(std::string, server_address, "unix:/sock/p4rt.sock",
          "The address of the server to connect to");
ABSL_FLAG(int32_t, min_silent_time, 0, "Min silent time in second");
ABSL_FLAG(int32_t, max_silent_time, 0, "Max silent time in second");
ABSL_FLAG(int32_t, delta_silent_time, 0, "Delta silent time in second");
ABSL_FLAG(int64_t, device_id, 183807201, "Device ID");

namespace p4rt_app {
namespace {

absl::StatusOr<p4::v1::Update> RouterInterfaceTableUpdate(
    const pdpi::IrP4Info& ir_p4_info, p4::v1::Update::Type type,
    absl::string_view router_interface_id, absl::string_view port,
    absl::string_view src_mac) {
  pdpi::IrUpdate ir_update;
  RETURN_IF_ERROR(gutil::ReadProtoFromString(
      absl::Substitute(R"pb(
                         type: $0
                         entity {
                           table_entry {
                             table_name: "router_interface_table"
                             matches {
                               name: "router_interface_id"
                               exact { str: "$1" }
                             }
                             action {
                               name: "set_port_and_src_mac"
                               params {
                                 name: "port"
                                 value { str: "$2" }
                               }
                               params {
                                 name: "src_mac"
                                 value { mac: "$3" }
                               }
                             }
                           }
                         }
                       )pb",
                       type, router_interface_id, port, src_mac),
      &ir_update))
      << "invalid pdpi::IrUpdate string.";
  return pdpi::IrUpdateToPi(ir_p4_info, ir_update);
}

absl::Status Main() {
  std::cout << "Opening P4RT connection to: "
            << absl::GetFlag(FLAGS_server_address) << std::endl;
  std::unique_ptr<::p4::v1::P4Runtime::Stub> stub;
  if (absl::GetFlag(FLAGS_insecure)) {
    stub = pdpi::CreateP4RuntimeStub(absl::GetFlag(FLAGS_server_address),
                                     grpc::InsecureChannelCredentials());
  } else {
    grpc::SslCredentialsOptions ssl_opts;
    ASSIGN_OR_RETURN(ssl_opts.pem_root_certs,
                     gutil::ReadFile(absl::GetFlag(FLAGS_ca_cert_file)));
    ASSIGN_OR_RETURN(ssl_opts.pem_private_key,
                     gutil::ReadFile(absl::GetFlag(FLAGS_server_key_file)));
    ASSIGN_OR_RETURN(ssl_opts.pem_cert_chain,
                     gutil::ReadFile(absl::GetFlag(FLAGS_server_cert_file)));
    grpc::ChannelArguments args = pdpi::GrpcChannelArgumentsForP4rt();
    args.SetString(GRPC_SSL_TARGET_NAME_OVERRIDE_ARG,
                   absl::GetFlag(FLAGS_hostname));
    stub = ::p4::v1::P4Runtime::NewStub(
        grpc::CreateCustomChannel(absl::GetFlag(FLAGS_server_address),
                                  grpc::SslCredentials(ssl_opts), args));
  }
  absl::uint128 election_id =
      absl::MakeUint128((absl::GetFlag(FLAGS_election_id) == -1
                             ? absl::ToUnixSeconds(absl::Now())
                             : absl::GetFlag(FLAGS_election_id)),
                        0);

  std::unique_ptr<pdpi::P4RuntimeSession> p4rt_session;
  ASSIGN_OR_RETURN(
      p4rt_session,
      pdpi::P4RuntimeSession::Create(
          std::move(stub), (uint32_t)absl::GetFlag(FLAGS_device_id),
          pdpi::P4RuntimeSessionOptionalArgs{.election_id = election_id},
          absl::GetFlag(FLAGS_error_if_not_primary)));
  ASSIGN_OR_RETURN(
      p4::v1::GetForwardingPipelineConfigResponse response,
      pdpi::GetForwardingPipelineConfig(
          p4rt_session.get(), p4::v1::GetForwardingPipelineConfigRequest::ALL));
  // Push P4 Info Config, only if not present.
  p4::config::v1::P4Info p4info;
  if (response.has_config()) {
    p4info = response.config().p4info();
  } else {
    p4info = sai::GetP4Info(sai::Instantiation::kTor);
    RETURN_IF_ERROR(pdpi::SetMetadataAndSetForwardingPipelineConfig(
        p4rt_session.get(),
        p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
        p4info));
  }

  ASSIGN_OR_RETURN(auto ir_p4info, pdpi::CreateIrP4Info(p4info));

  bool is_backup_session = absl::GetFlag(FLAGS_backup_session);
  uint32_t min_silent_time = absl::GetFlag(FLAGS_min_silent_time);
  uint32_t silent_time = min_silent_time;
  for (int i = 0; i < absl::GetFlag(FLAGS_number_iterations); i++) {
    if (!is_backup_session) {
      p4::v1::WriteRequest write_request;

      // Create and delete a router interface to mimic p4rt packets.
      ASSIGN_OR_RETURN(*write_request.add_updates(),
                       p4rt_app::RouterInterfaceTableUpdate(
                           ir_p4info, p4::v1::Update::INSERT, "router-intf-1",
                           "1", "00:02:03:04:05:06"));
      auto status = pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session.get(),
                                                           write_request);
      if (status.ok()) {
        std::cout << "SendWriteRequest successful iteration " << i << std::endl;
      } else {
        std::cout << "SendWriteRequest failed iteration " << i << std::endl;
      }

      write_request.Clear();
      ASSIGN_OR_RETURN(*write_request.add_updates(),
                       p4rt_app::RouterInterfaceTableUpdate(
                           ir_p4info, p4::v1::Update::DELETE, "router-intf-1",
                           "1", "00:02:03:04:05:06"));
      RETURN_IF_ERROR(pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session.get(),
                                                             write_request));
    }

    // Below is to introduce some silent time between iterations, if needed
    if (silent_time > 0) {
      absl::SleepFor(absl::Seconds(silent_time));
      silent_time += absl::GetFlag(FLAGS_delta_silent_time);
      if (silent_time > absl::GetFlag(FLAGS_max_silent_time)) {
        silent_time = min_silent_time;  // wrap around
      }
    }
  }

  if (!is_backup_session) {
    RETURN_IF_ERROR(pdpi::ClearTableEntries(p4rt_session.get()));
  }

  return absl::OkStatus();
}

}  // namespace
}  // namespace p4rt_app

int main(int argc, char** argv) {
  absl::InitializeLog();
  absl::ParseCommandLine(argc, argv);

  absl::Status status = p4rt_app::Main();
  if (!status.ok()) {
    std::cout << "Completed with error: " << status.ToString() << std::endl;
    return status.raw_code();
  }

  std::cout << "Completed successfully." << std::endl;
  return 0;
}
