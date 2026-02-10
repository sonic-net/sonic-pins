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
#ifndef PINS_P4RT_APP_TESTS_LIB_P4RUNTIME_GRPC_SERVICE_H_
#define PINS_P4RT_APP_TESTS_LIB_P4RUNTIME_GRPC_SERVICE_H_

#include <memory>

#include "grpcpp/server.h"
#include "p4rt_app/p4runtime/p4runtime_impl.h"
#include "p4rt_app/sonic/adapters/fake_sonic_db_table.h"
#include "p4rt_app/sonic/adapters/fake_table_adapter.h"
#include "p4rt_app/sonic/adapters/fake_warm_boot_state_adapter.h"
#include "p4rt_app/sonic/fake_packetio_interface.h"
#include "p4rt_app/utils/warm_restart_utility.h"
// TODO(PINS):
//  #include "swss/fakes/fake_component_state_helper.h"
//  #include "swss/fakes/fake_system_state_helper.h"

namespace p4rt_app {
namespace test_lib {

class P4RuntimeGrpcService {
 public:
  explicit P4RuntimeGrpcService(const P4RuntimeImplOptions &options);
  ~P4RuntimeGrpcService();

  absl::Status VerifyState();

  int GrpcPort() const;

  // Accessors for AppDb tables.
  sonic::FakeSonicDbTable &GetP4rtAppDbTable();
  sonic::FakeSonicDbTable &GetVrfAppDbTable();
  sonic::FakeSonicDbTable& GetVlanAppDbTable();
  sonic::FakeSonicDbTable& GetVlanMemberAppDbTable();
  sonic::FakeSonicDbTable &GetHashAppDbTable();
  sonic::FakeSonicDbTable &GetSwitchAppDbTable();
  sonic::FakeSonicDbTable &GetPortAppDbTable();

  // Accessors for AppStateDb tables.
  sonic::FakeSonicDbTable &GetVrfAppStateDbTable();
  sonic::FakeSonicDbTable& GetVlanAppStateDbTable();
  sonic::FakeSonicDbTable& GetVlanMemberAppStateDbTable();
  sonic::FakeSonicDbTable &GetHashAppStateDbTable();
  sonic::FakeSonicDbTable &GetSwitchAppStateDbTable();
  sonic::FakeSonicDbTable &GetPortAppStateDbTable();

  // Accessors for CounterDb tables.
  sonic::FakeSonicDbTable &GetP4rtCountersDbTable();

  // Accessors for StateDb tables.
  sonic::FakeSonicDbTable &GetP4rtStateDbTable();
  sonic::FakeSonicDbTable &GetHostStatsStateDbTable();
  sonic::FakeSonicDbTable& GetSwitchCapabilityStateDbTable();

  // Accessor for WarmBootStateAdapter.
  sonic::FakeWarmBootStateAdapter *GetWarmBootStateAdapter();

  // Accessor for WarmBootStateAdapter for WarmRestartUtil.
  // This is only used for setting OA warm start state and wairForUnfreeze DB
  // entry for WarmRestartUtil.
  sonic::FakeWarmBootStateAdapter* GetWarmBootStateAdapterForUtilOnly();

  // Accessor for WarmRestartUtil.
  WarmRestartUtil& GetWarmRestartUtil();

  // Accessor for PacketIO interface.
  sonic::FakePacketIoInterface &GetFakePacketIoInterface();

  // TODO(PINS): To handle Fake Component State and Fake System State later.
  //  Accessors for application state management.
  /*swss::FakeComponentStateHelper& GetComponentStateHelper();
  swss::FakeSystemStateHelper& GetSystemStateHelper();*/

  // Sets switch capabilities table in the DB for the fake server.
  void SetSwitchCapabilitiesTableInDb(const sonic::SonicDbEntryList& values);

  // Accessor for the P4RT server.
  P4RuntimeImpl &GetP4rtServer();

  // Build P4RT server.
  std::unique_ptr<P4RuntimeImpl> BuildP4rtServer(
      const P4RuntimeImplOptions& options);

  // Reset P4RT server.
  void ResetP4rtServer(std::unique_ptr<P4RuntimeImpl> p4runtime_server);

 private:
  // The TCP port used to  open the P4RT App service. It is chosen randomly in
  // the ctor, and shouldn't be modified otherwise.
  int grpc_port_;

  // Faked AppStateDb tables.
  sonic::FakeSonicDbTable fake_p4rt_state_table_;
  sonic::FakeSonicDbTable fake_vrf_state_table_;
  sonic::FakeSonicDbTable fake_vlan_state_table_;
  sonic::FakeSonicDbTable fake_vlan_member_state_table_;
  sonic::FakeSonicDbTable fake_hash_state_table_;
  sonic::FakeSonicDbTable fake_switch_state_table_;
  sonic::FakeSonicDbTable fake_port_state_table_;

  // Faked AppDb tables.
  sonic::FakeSonicDbTable fake_p4rt_table_;
  sonic::FakeSonicDbTable fake_vrf_table_;
  sonic::FakeSonicDbTable fake_vlan_table_;
  sonic::FakeSonicDbTable fake_vlan_member_table_;
  sonic::FakeSonicDbTable fake_hash_table_;
  sonic::FakeSonicDbTable fake_switch_table_;
  sonic::FakeSonicDbTable fake_port_table_;

  // Faked CountersDb tables.
  sonic::FakeSonicDbTable fake_p4rt_counters_table_;

  // Faked StateDb tables.
  sonic::FakeSonicDbTable fake_host_stats_table_;
  sonic::FakeSonicDbTable fake_switch_capability_table_;

  // Fake ConfigDb tables.
  sonic::FakeSonicDbTable fake_config_db_port_table_;
  sonic::FakeSonicDbTable fake_config_db_cpu_port_table_;
  sonic::FakeSonicDbTable fake_config_db_port_channel_table_;
  sonic::FakeSonicDbTable fake_config_db_cpu_queue_table_;
  sonic::FakeSonicDbTable fake_config_db_node_cfg_table_;
  sonic::FakeSonicDbTable fake_config_db_send_to_ingress_port_table_;
  // Fake CONFIG DB tables adapters to query (key, port_id) pairs.
  sonic::FakeTableAdapter* fake_port_table_adapter_;
  sonic::FakeTableAdapter* fake_cpu_port_table_adapter_;
  sonic::FakeTableAdapter* fake_port_channel_table_adapter_;
  // Fake CONFIG DB table adapters to query CPU queues.
  sonic::FakeTableAdapter* fake_cpu_queue_table_adapter_;
  sonic::FakeWarmBootStateAdapter* fake_warm_boot_state_adapter_for_util_only_;

  // Fake WarmRestartUntil to help P4RT server warm reboot.
  std::unique_ptr<WarmRestartUtil> warm_restart_util_;

  // Faked warm-boot state.
  sonic::FakeWarmBootStateAdapter *fake_warm_boot_state_adapter_;

  // Faked PacketIO interface.
  sonic::FakePacketIoInterface *fake_packetio_interface_; // No ownership.

  // TODO(PINS):
  // Faked state state management.
  // swss::FakeComponentStateHelper fake_component_state_helper_;
  // swss::FakeSystemStateHelper fake_system_state_helper_;

  // Faked netdev port translation.
  // sonic::FakeIntfTranslator fake_netdev_translator_{/*enabled=*/true};

  // gRPC server faking the P4RT App for testing.
  std::unique_ptr<grpc::Server> server_;
  std::unique_ptr<P4RuntimeImpl> p4runtime_server_;
};

} // namespace test_lib
} // namespace p4rt_app

#endif // PINS_P4RT_APP_TESTS_LIB_P4RUNTIME_GRPC_SERVICE_H_
