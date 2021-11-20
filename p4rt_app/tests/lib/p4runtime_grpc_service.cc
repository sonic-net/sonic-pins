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
#include "absl/strings/str_cat.h"
#include "glog/logging.h"
#include "grpcpp/security/server_credentials.h"
#include "grpcpp/server.h"
#include "grpcpp/server_builder.h"
#include "gutil/status_matchers.h"
#include "p4rt_app/p4runtime/p4runtime_impl.h"
#include "p4rt_app/sonic/adapters/fake_consumer_notifier_adapter.h"
#include "p4rt_app/sonic/adapters/fake_db_connector_adapter.h"
#include "p4rt_app/sonic/adapters/fake_producer_state_table_adapter.h"
#include "p4rt_app/sonic/fake_packetio_interface.h"

namespace p4rt_app {
namespace test_lib {

P4RuntimeGrpcService::P4RuntimeGrpcService(
    const P4RuntimeGrpcServiceOptions& options) {
  LOG(INFO) << "Starting the P4 runtime gRPC service.";
  const std::string kP4rtTableName = APP_P4RT_TABLE_NAME;
  const std::string kPortTableName = APP_PORT_TABLE_NAME;
  const std::string kCountersTableName = COUNTERS_TABLE;

  // Connect SONiC AppDB tables with their equivelant AppStateDB tables.
  fake_p4rt_table_ = sonic::FakeSonicDbTable(&fake_p4rt_state_table_);

  // Create AppDb interfaces used by the P4RT App.
  auto fake_app_db_client = absl::make_unique<sonic::FakeDBConnectorAdapter>();
  fake_app_db_client->AddSonicDbTable(kP4rtTableName, &fake_p4rt_table_);
  fake_app_db_client->AddSonicDbTable(kPortTableName, &fake_port_table_);

  // P4RT table.
  auto fake_app_db_table_p4rt =
      absl::make_unique<sonic::FakeProducerStateTableAdapter>(
          kP4rtTableName, &fake_p4rt_table_);
  auto fake_notify_p4rt =
      absl::make_unique<sonic::FakeConsumerNotifierAdapter>(&fake_p4rt_table_);

  // Create StateDb interfaces used by the P4RT App.
  auto fake_state_db_client =
      absl::make_unique<sonic::FakeDBConnectorAdapter>();
  fake_state_db_client->AddSonicDbTable(kP4rtTableName,
                                        &fake_p4rt_state_table_);

  // Create CounterDb interfaces used by the P4RT App.
  auto fake_counter_db_client =
      absl::make_unique<sonic::FakeDBConnectorAdapter>();
  fake_counter_db_client->AddSonicDbTable(kCountersTableName,
                                          &fake_p4rt_counters_table_);

  // Create FakePacketIoInterface and save the pointer.
  auto fake_packetio_interface =
      absl::make_unique<sonic::FakePacketIoInterface>();
  fake_packetio_interface_ = fake_packetio_interface.get();

  // Create the P4RT server.
  p4runtime_server_ = absl::make_unique<P4RuntimeImpl>(
      std::move(fake_app_db_client), std::move(fake_state_db_client),
      std::move(fake_counter_db_client), std::move(fake_app_db_table_p4rt),
      std::move(fake_notify_p4rt), std::move(fake_packetio_interface),
      options.use_genetlink, options.translate_port_ids);

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

int P4RuntimeGrpcService::GrpcPort() const { return 9999; }

sonic::FakeSonicDbTable& P4RuntimeGrpcService::GetP4rtAppDbTable() {
  return fake_p4rt_table_;
}

sonic::FakeSonicDbTable& P4RuntimeGrpcService::GetPortAppDbTable() {
  return fake_port_table_;
}

sonic::FakeSonicDbTable& P4RuntimeGrpcService::GetP4rtCountersDbTable() {
  return fake_p4rt_counters_table_;
}

sonic::FakePacketIoInterface& P4RuntimeGrpcService::GetFakePacketIoInterface() {
  return *fake_packetio_interface_;
}

}  // namespace test_lib
}  // namespace p4rt_app
