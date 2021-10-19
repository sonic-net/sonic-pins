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

#include <fstream>
#include <memory>
#include <sstream>
#include <stdexcept>
#include <string>

#include "absl/flags/parse.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "gflags/gflags.h"
#include "glog/logging.h"
#include "google/protobuf/descriptor.h"
#include "google/protobuf/text_format.h"
#include "grpcpp/security/server_credentials.h"
#include "grpcpp/security/tls_certificate_provider.h"
#include "grpcpp/security/tls_credentials_options.h"
#include "grpcpp/server.h"
#include "grpcpp/server_builder.h"
#include "gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4rt_app/p4runtime/p4runtime_impl.h"
#include "p4rt_app/sonic/adapters/system_call_adapter.h"
#include "p4rt_app/sonic/packetio_impl.h"
#include "swss/consumernotifier.h"
#include "swss/dbconnector.h"
#include "swss/producerstatetable.h"
#include "swss/schema.h"

using ::grpc::Server;
using ::grpc::ServerBuilder;
using ::grpc::ServerCredentials;

DEFINE_bool(use_genetlink, false,
            "Enable Generic Netlink model for Packet Receive");
DEFINE_bool(use_port_ids, false,
            "Controller will use Port ID values configured over gNMI instead "
            "of the SONiC interface names.");
DEFINE_int32(p4rt_grpc_port, 9559, "gRPC port for the P4Runtime Server");

int main(int argc, char** argv) {
  constexpr char kRedisDbHost[] = "localhost";
  constexpr int kRedisDbPort = 6379;

  google::InitGoogleLogging(argv[0]);
  gflags::ParseCommandLineFlags(&argc, &argv, true);

  // Open a database connection into the SONiC AppDb.
  auto sonic_app_db =
      absl::make_unique<swss::DBConnector>(APPL_DB, kRedisDbHost, kRedisDbPort,
                                           /*timeout=*/0);

  // Open a database connection into the SONiC StateDb.
  auto sonic_state_db = absl::make_unique<swss::DBConnector>(
      APPL_STATE_DB, kRedisDbHost, kRedisDbPort,
      /*timeout=*/0);

  // Open a database connection into the SONiC CountersDb
  auto sonic_counters_db = absl::make_unique<swss::DBConnector>(
      COUNTERS_DB, kRedisDbHost, kRedisDbPort,
      /*timeout=*/0);

  // Create interfaces to interact with the AppDb P4RT table.
  auto app_db_table_p4rt =
      absl::make_unique<swss::ProducerStateTable>(sonic_app_db.get(), "P4RT");
  auto notification_channel_p4rt = absl::make_unique<swss::ConsumerNotifier>(
      "APPL_DB_P4RT_RESPONSE_CHANNEL", sonic_app_db.get());

  // Create interfaces to interact with the AppDb VRF table.
  auto app_db_table_vrf = absl::make_unique<swss::ProducerStateTable>(
      sonic_app_db.get(), "VRF_TABLE");
  auto notification_channel_vrf = absl::make_unique<swss::ConsumerNotifier>(
      "APPL_DB_VRF_TABLE_RESPONSE_CHANNEL", sonic_app_db.get());

  // Wait for PortInitDone to be done.
  p4rt_app::sonic::WaitForPortInitDone(*sonic_app_db);

  // Create PacketIoImpl that will auto discover the ports.
  auto packetio_impl_or = p4rt_app::sonic::PacketIoImpl::CreatePacketIoImpl();
  if (!packetio_impl_or.ok()) {
    LOG(ERROR) << "Couldnt discover Packet I/O ports, error: "
               << packetio_impl_or.status();
    return -1;
  }

  // Create the P4RT server.
  p4rt_app::P4RuntimeImpl p4runtime_server(
      std::move(sonic_app_db), std::move(sonic_state_db),
      std::move(sonic_counters_db), std::move(app_db_table_p4rt),
      std::move(notification_channel_p4rt), std::move(app_db_table_vrf),
      std::move(notification_channel_vrf), std::move(*packetio_impl_or),
      FLAGS_use_genetlink, FLAGS_use_port_ids);

  // Start a P4 runtime server
  ServerBuilder builder;
  std::string server_addr = absl::StrCat("[::]:", FLAGS_p4rt_grpc_port);
  builder.AddListeningPort(server_addr, grpc::InsecureServerCredentials());
  builder.RegisterService(&p4runtime_server);

  std::unique_ptr<Server> server(builder.BuildAndStart());
  LOG(INFO) << "Server listening on " << server_addr << ".";
  server->Wait();

  return 0;
}
