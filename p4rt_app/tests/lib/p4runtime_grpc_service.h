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
#ifndef GOOGLE_P4RT_APP_TESTS_LIB_P4RUNTIME_GRPC_SERVICE_H_
#define GOOGLE_P4RT_APP_TESTS_LIB_P4RUNTIME_GRPC_SERVICE_H_

#include <memory>

#include "absl/status/status.h"
#include "grpcpp/server.h"
#include "grpcpp/server_builder.h"
#include "p4rt_app/p4runtime/p4runtime_impl.h"
#include "p4rt_app/sonic/adapters/fake_sonic_db_table.h"
#include "p4rt_app/sonic/fake_packetio_interface.h"

namespace p4rt_app {
namespace test_lib {

class P4RuntimeGrpcService {
 public:
  explicit P4RuntimeGrpcService(const P4RuntimeImplOptions& options);
  ~P4RuntimeGrpcService();

  int GrpcPort() const;

  // Accessors for AppDb tables.
  sonic::FakeSonicDbTable& GetP4rtAppDbTable();
  sonic::FakeSonicDbTable& GetPortAppDbTable();

  // Accessors for AppStateDb tables.
  sonic::FakeSonicDbTable& GetP4rtAppStateDbTable();

  // Accessors for CounterDb tables.
  sonic::FakeSonicDbTable& GetP4rtCountersDbTable();

  // Accessor for PacketIO interface.
  sonic::FakePacketIoInterface& GetFakePacketIoInterface();

  // Accessor for the P4RT server.
  P4RuntimeImpl& GetP4rtServer();

 private:
  // The TCP port used to  open the P4RT App service. It is choosen randomly in
  // the ctor, and shouldn't be modified otherwise.
  int grpc_port_;

  // Faked StateDb tables.
  sonic::FakeSonicDbTable fake_p4rt_state_table_;

  // Faked AppDb tables.
  sonic::FakeSonicDbTable fake_p4rt_table_;
  sonic::FakeSonicDbTable fake_port_table_;

  // Faked CountersDb tables.
  sonic::FakeSonicDbTable fake_p4rt_counters_table_;

  // Faked PacketIO interface.
  sonic::FakePacketIoInterface* fake_packetio_interface_;  // No ownership.

  // gRPC server faking the P4RT App for testing.
  std::unique_ptr<grpc::Server> server_;
  std::unique_ptr<P4RuntimeImpl> p4runtime_server_;
};

}  // namespace test_lib
}  // namespace p4rt_app

#endif  // GOOGLE_P4RT_APP_TESTS_LIB_P4RUNTIME_GRPC_SERVICE_H_
