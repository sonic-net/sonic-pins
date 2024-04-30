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
#include "p4rt_app/tests/lib/p4runtime_grpc_service.h"

#include <memory>
#include <string>
#include <utility>

#include "absl/memory/memory.h"
#include "absl/random/distributions.h"
#include "absl/random/random.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "glog/logging.h"
#include "grpcpp/security/server_credentials.h"
#include "grpcpp/server.h"
#include "grpcpp/server_builder.h"
#include "gutil/status_matchers.h"
#include "p4rt_app/p4runtime/p4runtime_impl.h"
#include "p4rt_app/sonic/adapters/fake_consumer_notifier_adapter.h"
#include "p4rt_app/sonic/adapters/fake_notification_producer_adapter.h"
#include "p4rt_app/sonic/adapters/fake_producer_state_table_adapter.h"
#include "p4rt_app/sonic/adapters/fake_sonic_db_table.h"
#include "p4rt_app/sonic/adapters/fake_table_adapter.h"
#include "p4rt_app/sonic/fake_packetio_interface.h"
#include "p4rt_app/sonic/redis_connections.h"
#include "swss/consumerstatetable.h"
#include "swss/dbconnector.h"
#include "swss/notificationproducer.h"

namespace p4rt_app {
namespace test_lib {

P4RuntimeGrpcService::P4RuntimeGrpcService(const P4RuntimeImplOptions& options)
    : fake_p4rt_state_table_("AppStateDb:P4RT_TABLE"),
      fake_vrf_state_table_("AppStateDb:VRF_TABLE"),
      fake_hash_state_table_("AppStateDb:HASH_TABLE"),
      fake_switch_state_table_("AppStateDb:SWITCH_TABLE"),
      fake_p4rt_table_("AppDb:P4RT_TABLE", &fake_p4rt_state_table_),
      fake_vrf_table_("AppDb:VRF_TABLE", &fake_vrf_state_table_),
      fake_hash_table_("AppDb:HASH_TABLE", &fake_hash_state_table_),
      fake_switch_table_("AppDb:SWITCH_TABLE", &fake_switch_state_table_) {
  LOG(INFO) << "Starting the P4 runtime gRPC service.";
  const std::string kP4rtTableName = "P4RT_TABLE";
  const std::string kPortTableName = "PORT_TABLE";
  const std::string kVrfTableName = "VRF_TABLE";
  const std::string kHashTableName = "HASH_TABLE";
  const std::string kSwitchTableName = "SWITCH_TABLE";

  // Choose a random gRPC port. While not strictly necessary each test brings up
  // a new gRPC service, and randomly choosing a TCP port will minimize issues.
  absl::BitGen gen;
  grpc_port_ = absl::Uniform<int>(gen, 49152, 65535);

  // Create interfaces to access P4RT_TABLE entries.
  sonic::P4rtTable p4rt_table{
      .notification_producer =
          std::make_unique<sonic::FakeNotificationProducerAdapter>(
              &fake_p4rt_table_),
      .notifier = absl::make_unique<sonic::FakeConsumerNotifierAdapter>(
          &fake_p4rt_table_),
      .app_state_db = absl::make_unique<sonic::FakeTableAdapter>(
          &fake_p4rt_state_table_, kP4rtTableName),
      .counter_db = absl::make_unique<sonic::FakeTableAdapter>(
          &fake_p4rt_counters_table_, kP4rtTableName),
  };

  // Create interfaces to access VRF_TABLE entries.
  sonic::VrfTable vrf_table{
      .producer_state = std::make_unique<sonic::FakeProducerStateTableAdapter>(
          &fake_vrf_table_),
      .notifier = absl::make_unique<sonic::FakeConsumerNotifierAdapter>(
          &fake_vrf_table_),
      .app_db = absl::make_unique<sonic::FakeTableAdapter>(&fake_vrf_table_, kVrfTableName),
      .app_state_db =
          absl::make_unique<sonic::FakeTableAdapter>(&fake_vrf_state_table_, kVrfTableName),
  };

  // Create interfaces to access HASH_TABLE entries.
  sonic::HashTable hash_table{
      .producer_state = std::make_unique<sonic::FakeProducerStateTableAdapter>(
          &fake_hash_table_),
      .notifier = absl::make_unique<sonic::FakeConsumerNotifierAdapter>(
          &fake_hash_table_),
      .app_db = absl::make_unique<sonic::FakeTableAdapter>(&fake_hash_table_, kHashTableName),
      .app_state_db =
          absl::make_unique<sonic::FakeTableAdapter>(&fake_hash_state_table_, kHashTableName),
  };

  // Create interfaces to access SWITCH_TABLE entries.
  sonic::SwitchTable switch_table{
      .producer_state = std::make_unique<sonic::FakeProducerStateTableAdapter>(
          &fake_switch_table_),
      .notifier = absl::make_unique<sonic::FakeConsumerNotifierAdapter>(
          &fake_switch_table_),
      .app_db = absl::make_unique<sonic::FakeTableAdapter>(&fake_switch_table_, kSwitchTableName),
      .app_state_db =
          absl::make_unique<sonic::FakeTableAdapter>(&fake_switch_state_table_, kSwitchTableName),
  };

  // Create FakePacketIoInterface and save the pointer.
  auto fake_packetio_interface =
      absl::make_unique<sonic::FakePacketIoInterface>();
  fake_packetio_interface_ = fake_packetio_interface.get();

  // Create the P4RT server.
  p4runtime_server_ = absl::make_unique<P4RuntimeImpl>(
      std::move(p4rt_table), std::move(vrf_table), std::move(hash_table),
      std::move(switch_table), std::move(fake_packetio_interface),
      options);

  // Component tests will use an insecure connection for the service.
  std::string server_address = absl::StrCat("localhost:", GrpcPort());
  std::shared_ptr<grpc::ServerCredentials> creds =
      grpc::InsecureServerCredentials();

  // Finally start the gRPC service.
  grpc::ServerBuilder builder;
  builder.AddListeningPort(server_address, creds);
  builder.RegisterService(p4runtime_server_.get());
  std::unique_ptr<grpc::Server> server(builder.BuildAndStart());

  LOG(INFO) << "Server listening on " << server_address;
  server_ = std::move(server);
}

P4RuntimeGrpcService::~P4RuntimeGrpcService() {
  LOG(INFO) << "Stopping the P4 runtime gRPC service.";
  if (server_) server_->Shutdown();
}

int P4RuntimeGrpcService::GrpcPort() const { return grpc_port_; }

absl::Status P4RuntimeGrpcService::VerifyState() {
  return p4runtime_server_->VerifyState();
}

sonic::FakeSonicDbTable& P4RuntimeGrpcService::GetP4rtAppDbTable() {
  return fake_p4rt_table_;
}

sonic::FakeSonicDbTable& P4RuntimeGrpcService::GetVrfAppDbTable() {
  return fake_vrf_table_;
}

sonic::FakeSonicDbTable& P4RuntimeGrpcService::GetHashAppDbTable() {
  return fake_hash_table_;
}

sonic::FakeSonicDbTable& P4RuntimeGrpcService::GetSwitchAppDbTable() {
  return fake_switch_table_;
}

sonic::FakeSonicDbTable& P4RuntimeGrpcService::GetPortAppDbTable() {
  return fake_port_table_;
}

sonic::FakeSonicDbTable& P4RuntimeGrpcService::GetP4rtAppStateDbTable() {
  return fake_p4rt_state_table_;
}

sonic::FakeSonicDbTable& P4RuntimeGrpcService::GetVrfAppStateDbTable() {
  return fake_vrf_state_table_;
}

sonic::FakeSonicDbTable& P4RuntimeGrpcService::GetHashAppStateDbTable() {
  return fake_hash_state_table_;
}

sonic::FakeSonicDbTable& P4RuntimeGrpcService::GetSwitchAppStateDbTable() {
  return fake_switch_state_table_;
}

sonic::FakeSonicDbTable& P4RuntimeGrpcService::GetP4rtCountersDbTable() {
  return fake_p4rt_counters_table_;
}

sonic::FakeSonicDbTable& P4RuntimeGrpcService::GetP4rtStateDbTable() {
  return fake_p4rt_state_table_;
}

sonic::FakePacketIoInterface& P4RuntimeGrpcService::GetFakePacketIoInterface() {
  return *fake_packetio_interface_;
}

P4RuntimeImpl& P4RuntimeGrpcService::GetP4rtServer() {
  return *p4runtime_server_;
}

}  // namespace test_lib
}  // namespace p4rt_app
