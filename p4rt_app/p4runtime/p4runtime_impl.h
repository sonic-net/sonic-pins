/*
 * Copyright 2020 Google LLC
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
#ifndef PINS_P4RT_APP_P4RUNTIME_P4RUNTIME_IMPL_H_
#define PINS_P4RT_APP_P4RUNTIME_P4RUNTIME_IMPL_H_

#include <cstdint>
#include <memory>
#include <ostream>
#include <string>
#include <thread>  // NOLINT
#include <utility>
#include <vector>

#include "absl/base/attributes.h"
#include "absl/base/thread_annotations.h"
#include "absl/container/btree_set.h"
#include "absl/container/flat_hash_map.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "absl/synchronization/mutex.h"
#include "absl/time/time.h"
#include "absl/types/optional.h"
#include "boost/bimap.hpp"
#include "grpcpp/server_context.h"
#include "grpcpp/support/status.h"
#include "grpcpp/support/sync_stream.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_constraints/backend/constraint_info.h"
#include "p4_infra/p4_pdpi/entity_keys.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4rt_app/p4runtime/p4info_reconcile.h"
#include "p4rt_app/p4runtime/queue_translator.h"
#include "p4rt_app/p4runtime/resource_utilization.h"
#include "p4rt_app/p4runtime/sdn_controller_manager.h"
#include "p4rt_app/sonic/adapters/warm_boot_state_adapter.h"
#include "p4rt_app/sonic/hashing.h"
#include "p4rt_app/sonic/packetio_interface.h"
#include "p4rt_app/sonic/redis_connections.h"
#include "p4rt_app/utils/event_data_tracker.h"
// TODO(PINS):
// #include "swss/component_state_helper_interface.h"
// #include "swss/intf_translator.h"
#include "swss/warm_restart.h"

namespace p4rt_app {

enum class QueueType { kCpu, kFrontPanel };
std::ostream& operator<<(std::ostream& os, QueueType qt);

struct P4RuntimeImplOptions {
  bool use_genetlink = false;
  bool translate_port_ids = true;
  bool is_freeze_mode = false;
  absl::optional<std::string> forwarding_config_full_path;
};

struct FlowProgrammingStatistics {
  // Total number of batch write requests sent to the switch. The value should
  // be equal to the number of time Write() is called.
  int write_batch_count;

  // Total number of indivindual updates sent to the switch. Because each
  // Write() can have multiple update (i.e. batched together) this value can
  // differ from the total number of times Write() is called.
  int write_requests_count;

  // Total time the switch spent handling Write() all requests. Note this
  // includes P4RT App parsing the data, sending it to the OA, waiting for a
  // response, and handling that response.
  absl::Duration write_time;

  // Time the longest request took to be handled. Notice that this does not take
  // into account batch size.
  absl::Duration max_write_time;

  // Total number of Read() calls handled by the switch.
  int read_request_count;

  // Total time the switch spent handing all Read() requests. Note that P4RT
  // reads everything it needs from the RedisDB layer, and the OA or other
  // layers are not involved in these requests.
  absl::Duration read_time;
};

class P4RuntimeImpl : public p4::v1::P4Runtime::Service {
public:
  P4RuntimeImpl(
      sonic::P4rtTable p4rt_table, sonic::VrfTable vrf_table,
      sonic::VlanTable vlan_table, sonic::VlanMemberTable vlan_member_table,
      sonic::HashTable hash_table, sonic::SwitchTable switch_table,
      sonic::PortTable port_table, sonic::HostStatsTable host_stats_table,
      std::unique_ptr<sonic::WarmBootStateAdapter> warm_boot_state_adapter,
      std::unique_ptr<sonic::PacketIoInterface> packetio_impl,
      // TODO(PINS): To add component_state, system_state and netdev_translator.
      /* swss::ComponentStateHelperInterface& component_state,
      swss::SystemStateHelperInterface& system_state,
      swss::IntfTranslator& netdev_translator, */
      const P4RuntimeImplOptions &p4rt_options);
  ~P4RuntimeImpl() override = default;

  // Determines the type of write request (e.g. table entry, direct counter
  // entry, etc.) then passes work off to a helper method. Requests will be
  // rejected if:
  //  * Request is not from the primary connection.
  //  * No config has been applied.
  //  * The last saved config has not been applied.
  //  * The switch is in a critical state.
  grpc::Status Write(grpc::ServerContext *context,
                     const p4::v1::WriteRequest *request,
                     p4::v1::WriteResponse *response) override
      ABSL_LOCKS_EXCLUDED(server_state_lock_);

  grpc::Status
  Read(grpc::ServerContext *context, const p4::v1::ReadRequest *request,
       grpc::ServerWriter<p4::v1::ReadResponse> *response_writer) override
      ABSL_LOCKS_EXCLUDED(server_state_lock_);

  grpc::Status SetForwardingPipelineConfig(
      grpc::ServerContext *context,
      const p4::v1::SetForwardingPipelineConfigRequest *request,
      p4::v1::SetForwardingPipelineConfigResponse *response) override
      ABSL_LOCKS_EXCLUDED(server_state_lock_);

  grpc::Status GetForwardingPipelineConfig(
      grpc::ServerContext *context,
      const p4::v1::GetForwardingPipelineConfigRequest *request,
      p4::v1::GetForwardingPipelineConfigResponse *response) override
      ABSL_LOCKS_EXCLUDED(server_state_lock_);

  grpc::Status StreamChannel(
      grpc::ServerContext *context,
      grpc::ServerReaderWriter<p4::v1::StreamMessageResponse,
                               p4::v1::StreamMessageRequest> *stream) override
      ABSL_LOCKS_EXCLUDED(server_state_lock_);

  // Updates the Device ID for the P4Runtime service if there is no active
  // connections.
  virtual absl::Status UpdateDeviceId(uint64_t device_id)
      ABSL_LOCKS_EXCLUDED(server_state_lock_);

  // Adds or removes a port from PacketIO.
  virtual absl::Status AddPacketIoPort(const std::string &port_name)
      ABSL_LOCKS_EXCLUDED(server_state_lock_);
  virtual absl::Status RemovePacketIoPort(const std::string &port_name)
      ABSL_LOCKS_EXCLUDED(server_state_lock_);

  // Responds with one of the following actions to port translation:
  // * Add the new port translation for unknown name & ID
  // * Update an existing {name, id} translation to the new ID
  // * No-Op if the {name, id} pairing already exists
  // * Reject if the ID is already in-use or if any input is empty ("").
  //
  // Consider existing port mappings: {"A", "1"}, {"B", "2"}
  // The result map is:
  // Port | <-----  Port ID  ------> |
  // Name |   "1"  |   "2"  |   "3"  |
  // =====|========|========|========|
  //  "A" | No-Op  | Reject | Update |
  // -----|--------|--------|--------|
  //  "B" | Reject | No-Op  | Update |
  // -----|--------|--------|--------|
  //  "C" | Reject | Reject |  Add   |
  // -----|--------|--------|--------|
  virtual absl::Status AddPortTranslation(const std::string& port_name,
                                          const std::string& port_id,
                                          bool update_dbs = true)
      ABSL_LOCKS_EXCLUDED(server_state_lock_);

  // Removes a port translation. Returns an error for an empty port name.
  // Triggers AppDb and AppStateDb updates even if the port translation does not
  // currently exist.
  virtual absl::Status RemovePortTranslation(const std::string &port_name)
      ABSL_LOCKS_EXCLUDED(server_state_lock_);

  // Verifies state for the P4RT App. These are checks like:
  //  * Do VRF_TABLE entries match in AppStateDb and AppDb.
  //  * Do HASH_TABLE entries match in AppStateDb and AppDb.
  //  * Do SWITCH_TABLE entries match in AppStateDb and AppDb.
  //
  // NOTE: We do not verify ownership of table entries today. Therefore, shared
  // tables (e.g. VRF_TABLE) could cause false positives.
  virtual absl::Status VerifyState() ABSL_LOCKS_EXCLUDED(server_state_lock_);

  std::string DumpPortTranslationDebugData();
  std::string DumpEntityCache();

  // Dump various debug data for the P4RT App, including:
  // * PacketIO counters.
  // * Port translation map.
  // * Queue translations maps.
  // * Internal cache.
  virtual absl::Status DumpDebugData(const std::string& path,
                                     const std::string& log_level)
      ABSL_LOCKS_EXCLUDED(server_state_lock_);

  // Returns performance statistics relating to the P4Runtime flow programming
  // API. Data will be reset to zero on reading(i.e. results are not
  // cumulative).
  absl::StatusOr<FlowProgrammingStatistics> GetFlowProgrammingStatistics()
      ABSL_LOCKS_EXCLUDED(server_state_lock_);

  // Assigns the CPU or FRONT_PANEL queue translator.
  virtual void AssignQueueTranslator(
      const QueueType queue_type, std::unique_ptr<QueueTranslator> translator)
      ABSL_LOCKS_EXCLUDED(server_state_lock_);

  sonic::PacketIoCounters GetPacketIoCounters()
      ABSL_LOCKS_EXCLUDED(server_state_lock_);

  // Rebuild software state after WarmBoot with APP DB
  // entries and cached p4info file.
  absl::Status RebuildSwStateAfterWarmboot(
      const std::vector<std::pair<std::string, std::string>>& port_ids,
      const std::vector<std::pair<std::string, std::string>>& cpu_queue_ids,
      const std::vector<std::pair<std::string, std::string>>&
          front_panel_queue_ids,
      const std::optional<int>& device_id)
      ABSL_LOCKS_EXCLUDED(server_state_lock_);

  grpc::Status GrabLockAndEnterCriticalState(absl::string_view message)
      ABSL_LOCKS_EXCLUDED(server_state_lock_);

  void GrabLockAndUpdateWarmBootState(swss::WarmStart::WarmStartState state)
      ABSL_LOCKS_EXCLUDED(server_state_lock_);

 protected:
  // Simple constructor that should only be used for testing purposes.
  P4RuntimeImpl(bool translate_port_ids)
      : translate_port_ids_(translate_port_ids) {}

private:
  P4RuntimeImpl(const P4RuntimeImpl &) = delete;
  P4RuntimeImpl &operator=(const P4RuntimeImpl &) = delete;

  // Get and process response from the notification channel, if on error,
  // restore the APPL_DB to the last good state. Uses, the key of the inserted
  // entry to match the response and restore if needed.
  pdpi::IrUpdateStatus GetAndProcessResponse(absl::string_view key);

  absl::Status HandlePacketOutRequest(const p4::v1::PacketOut &packet_out)
      ABSL_EXCLUSIVE_LOCKS_REQUIRED(server_state_lock_);

  // Verify, save and realize the given config. Today we DO NOT support clearing
  // any forwarding state, and we will return a failure if a config has already
  // been applied.
  //
  // Returns an error if the config is not provided of if the provided config
  // cannot be realized.
  grpc::Status VerifyAndCommitPipelineConfig(
      const p4::v1::SetForwardingPipelineConfigRequest &request)
      ABSL_EXCLUSIVE_LOCKS_REQUIRED(server_state_lock_);

  // Realize the last saved, but not yet committed config.
  //
  // Returns an error if a config is provided, if a config is already realized,
  // or if a no saved config is found.
  grpc::Status CommitPipelineConfig(
      const p4::v1::SetForwardingPipelineConfigRequest &request)
      ABSL_EXCLUSIVE_LOCKS_REQUIRED(server_state_lock_);

  // Verify, save and realize the given config. Today we DO NOT support changing
  // the P4Info in any way, and we will return a failure if we detect any
  // changes. However, new configs can be pushed multiple times so long as the
  // P4Info remains the same.
  //
  // Returns an error if the config is not provided, or if the existing
  // forwarding state cannot be preserved for the given config by the target.
  grpc::Status ReconcileAndCommitPipelineConfig(
      const p4::v1::SetForwardingPipelineConfigRequest& request,
      bool commit_to_hardware = true)
      ABSL_EXCLUSIVE_LOCKS_REQUIRED(server_state_lock_);

  // Tries to save the forwarding config to a file. If the
  // forwarding_config_full_path_ variable is not set it will return OK, but any
  // other issue with saving the config will return an error.
  grpc::Status
  SavePipelineConfig(const p4::v1::ForwardingPipelineConfig &config) const
      ABSL_EXCLUSIVE_LOCKS_REQUIRED(server_state_lock_);

  // Writes the necessary updates from the pipeline config into the AppDb
  // tables. These configurations (e.g. ACLs, hashing, etc.) are needed before
  // we can start accepting write requests.
  absl::Status ConfigureAppDbTables(const pdpi::IrP4Info &ir_p4info)
      ABSL_EXCLUSIVE_LOCKS_REQUIRED(server_state_lock_);

  grpc::Status TransitionHashConfig(
      const P4InfoReconcileTransition& transition,
      const absl::btree_set<sonic::HashPacketFieldConfig>&
          hash_packet_field_configs,
      const sonic::HashParamConfigs& hash_param_configs)
      ABSL_EXCLUSIVE_LOCKS_REQUIRED(server_state_lock_);

  // Defines the callback lambda function to be invoked for receive packets
  // and calls into the sonic::StartReceive to spawn the receiver thread.
  ABSL_MUST_USE_RESULT absl::StatusOr<std::thread>
  StartReceive(bool use_genetlink);

  void UpdateWarmBootState(swss::WarmStart::WarmStartState state);

  swss::WarmStart::WarmStartState GetWarmBootState();

  // Enter critical state and write component state to DB.
  // Caller should take server_state_lock_.
  grpc::Status EnterCriticalState(const std::string& message)
      ABSL_EXCLUSIVE_LOCKS_REQUIRED(server_state_lock_);

  // Mutex for constraining actions to access and modify server state.
  absl::Mutex server_state_lock_;

  // Interfaces which are used to update entries in the RedisDB tables.
  sonic::P4rtTable p4rt_table_ ABSL_GUARDED_BY(server_state_lock_);
  sonic::VrfTable vrf_table_ ABSL_GUARDED_BY(server_state_lock_);
  sonic::VlanTable vlan_table_ ABSL_GUARDED_BY(server_state_lock_);
  sonic::VlanMemberTable vlan_member_table_ ABSL_GUARDED_BY(server_state_lock_);
  sonic::HashTable hash_table_ ABSL_GUARDED_BY(server_state_lock_);
  sonic::SwitchTable switch_table_ ABSL_GUARDED_BY(server_state_lock_);
  sonic::PortTable port_table_ ABSL_GUARDED_BY(server_state_lock_);
  sonic::HostStatsTable host_stats_table_ ABSL_GUARDED_BY(server_state_lock_);
  const std::unique_ptr<sonic::WarmBootStateAdapter>
      warm_boot_state_adapter_ ABSL_GUARDED_BY(server_state_lock_);

  // P4RT can accept multiple connections to a single switch for redundancy.
  // When there is >1 connection the switch chooses a primary which is used for
  // PacketIO, and is the only connection allowed to write updates.
  //
  // It is possible for connections to be made for specific roles. In which case
  // one primary connection is allowed for each distinct role.
  std::unique_ptr<SdnControllerManager>
      controller_manager_ ABSL_GUARDED_BY(server_state_lock_);

  // SONiC uses name to reference ports (e.g. Ethernet4), but the controller can
  // be configured to send port IDs. The P4RT App takes responsibility for
  // translating between the two.
  //
  // boost::bimap<SONiC port name, controller ID>;
  boost::bimap<std::string, std::string>
      port_translation_map_ ABSL_GUARDED_BY(server_state_lock_);

  // A forwarding pipeline config with a P4Info protobuf will be set once a
  // controller connects to the switch. Only after we receive this config can
  // the P4RT service start processing write requests.
  absl::optional<p4::v1::ForwardingPipelineConfig>
      forwarding_pipeline_config_ ABSL_GUARDED_BY(server_state_lock_);

  // The ForwardingConfig can be saved to disk when it is pushed to the switch.
  // It can also be loaded from disk by sending a COMMIT request to the
  // SetForwardingPipelineConfig method.
  absl::optional<std::string>
      forwarding_config_full_path_ ABSL_GUARDED_BY(server_state_lock_);

  // Once we receive the P4Info we create a pdpi::IrP4Info object which allows
  // us to translate the PI requests into human-readable objects.
  absl::optional<pdpi::IrP4Info> ir_p4info_ ABSL_GUARDED_BY(server_state_lock_);

  // The P4Info can use annotations to specify table constraints for specific
  // tables. The P4RT service will reject any table entry requests that do not
  // meet these constraints.
  absl::optional<p4_constraints::ConstraintInfo> p4_constraint_info_;

  // PacketIoImplementation object.
  std::thread receive_thread_;
  std::unique_ptr<sonic::PacketIoInterface>
      packetio_impl_ ABSL_GUARDED_BY(server_state_lock_);

  /* TODO(PINS): To handle component_state, system_state and netdev_translator
  later.
  // When the switch is in critical state the P4RT service shuould not accept
  // write requests, but can still handle reads.
  swss::ComponentStateHelperInterface& component_state_
      ABSL_GUARDED_BY(server_state_lock_);
  swss::SystemStateHelperInterface& system_state_;

  // Some controllers may want to use port names that include the
  // slot/port/channel format (e.g. Ethernet1/1/1) which does not work for
  // Linux's netdev interfaces. This translator can be used to convert the names
  // into a valid Linux name (e.g. Ethernet1_1_1).
  swss::IntfTranslator& netdev_translator_ ABSL_GUARDED_BY(server_state_lock_);
*/

  // Some switch environments cannot rely on the SONiC port names, and can
  // instead choose to use port ID's configured through gNMI.
  const bool translate_port_ids_ ABSL_GUARDED_BY(server_state_lock_);

  // Reading a large number of entries from Redis is costly. To improve the
  // read performance we cache table entries in software.
  absl::flat_hash_map<pdpi::EntityKey, p4::v1::Entity>
      entity_cache_ ABSL_GUARDED_BY(server_state_lock_);

  // Monitoring resources in hardware can be difficult. For example in WCMP if a
  // port is down the lower layers will remove those path both freeing resources
  // and ensuring packets are not routed to a down port. To ensure we do not
  // overuse space we track resource usage in the P4RT layer.
  absl::flat_hash_map<std::string, ActionProfileResourceCapacity>
      capacity_by_action_profile_name_ ABSL_GUARDED_BY(server_state_lock_);

  // Utility to perform translations between CPU queue name and id.
  std::unique_ptr<QueueTranslator> cpu_queue_translator_
      ABSL_GUARDED_BY(server_state_lock_);
  // Utility to perform translations between FRONT_PANEL queue name and id.
  std::unique_ptr<QueueTranslator> front_panel_queue_translator_
      ABSL_GUARDED_BY(server_state_lock_);

  // Performance statistics for P4RT Write().
  EventDataTracker<int> write_batch_requests_
      ABSL_GUARDED_BY(server_state_lock_){EventDataTracker<int>(0)};
  EventDataTracker<int> write_total_requests_
      ABSL_GUARDED_BY(server_state_lock_){EventDataTracker<int>(0)};
  EventDataTracker<absl::Duration>
      write_execution_time_ ABSL_GUARDED_BY(server_state_lock_){
          EventDataTracker<absl::Duration>(absl::ZeroDuration())};

  // Performance statistics for P4RT Read().
  EventDataTracker<int> read_total_requests_
      ABSL_GUARDED_BY(server_state_lock_){EventDataTracker<int>(0)};
  EventDataTracker<absl::Duration>
      read_execution_time_ ABSL_GUARDED_BY(server_state_lock_){
          EventDataTracker<absl::Duration>(absl::ZeroDuration())};

  // PacketIO debug counters.
  sonic::PacketIoCounters packetio_counters_;

  // Flag to indicate whether P4RT is in warm-boot freeze process.
  bool is_freeze_mode_ ABSL_GUARDED_BY(server_state_lock_) = false;
};

} // namespace p4rt_app

#endif // PINS_P4RT_APP_P4RUNTIME_P4RUNTIME_IMPL_H_
