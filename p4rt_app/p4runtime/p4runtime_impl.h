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
#ifndef GOOGLE_P4RT_APP_P4RUNTIME_P4RUNTIME_IMPL_H_
#define GOOGLE_P4RT_APP_P4RUNTIME_P4RUNTIME_IMPL_H_

#include <cstdint>
#include <memory>
#include <string>
#include <vector>

#include "absl/base/thread_annotations.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/types/optional.h"
#include "boost/bimap.hpp"
#include "grpcpp/grpcpp.h"
#include "grpcpp/server_context.h"
#include "grpcpp/support/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_constraints/backend/constraint_info.h"
#include "p4_pdpi/ir.pb.h"
#include "p4rt_app/p4runtime/sdn_controller_manager.h"
#include "p4rt_app/sonic/packetio_interface.h"
#include "p4rt_app/sonic/redis_connections.h"

namespace p4rt_app {

struct P4RuntimeImplOptions {
  bool use_genetlink = false;
  bool translate_port_ids = true;
  absl::optional<std::string> forwarding_config_full_path;
};

class P4RuntimeImpl : public p4::v1::P4Runtime::Service {
 public:
  P4RuntimeImpl(sonic::P4rtTable p4rt_table,
                std::unique_ptr<sonic::PacketIoInterface> packetio_impl,
                const P4RuntimeImplOptions& p4rt_options);
  ~P4RuntimeImpl() override = default;

  // Determines the type of write request (e.g. table entry, direct counter
  // entry, etc.) then passes work off to a helper method. Requests will be
  // rejected if:
  //  * Request is not from the primary connection.
  //  * No config has been applied.
  //  * The last saved config has not been applied.
  //  * The switch is in a critical state.
  grpc::Status Write(grpc::ServerContext* context,
                     const p4::v1::WriteRequest* request,
                     p4::v1::WriteResponse* response) override
      ABSL_LOCKS_EXCLUDED(server_state_lock_);

  grpc::Status Read(
      grpc::ServerContext* context, const p4::v1::ReadRequest* request,
      grpc::ServerWriter<p4::v1::ReadResponse>* response_writer) override
      ABSL_LOCKS_EXCLUDED(server_state_lock_);

  grpc::Status SetForwardingPipelineConfig(
      grpc::ServerContext* context,
      const p4::v1::SetForwardingPipelineConfigRequest* request,
      p4::v1::SetForwardingPipelineConfigResponse* response) override
      ABSL_LOCKS_EXCLUDED(server_state_lock_);

  grpc::Status GetForwardingPipelineConfig(
      grpc::ServerContext* context,
      const p4::v1::GetForwardingPipelineConfigRequest* request,
      p4::v1::GetForwardingPipelineConfigResponse* response) override
      ABSL_LOCKS_EXCLUDED(server_state_lock_);

  grpc::Status StreamChannel(
      grpc::ServerContext* context,
      grpc::ServerReaderWriter<p4::v1::StreamMessageResponse,
                               p4::v1::StreamMessageRequest>* stream) override
      ABSL_LOCKS_EXCLUDED(server_state_lock_);

  // Updates the Device ID for the P4Runtime service if there is no active
  // connections.
  virtual absl::Status UpdateDeviceId(uint64_t device_id)
      ABSL_LOCKS_EXCLUDED(server_state_lock_);

  // Adds or removes a port from PacketIO.
  virtual absl::Status AddPacketIoPort(const std::string& port_name)
      ABSL_LOCKS_EXCLUDED(server_state_lock_);
  virtual absl::Status RemovePacketIoPort(const std::string& port_name)
      ABSL_LOCKS_EXCLUDED(server_state_lock_);

  // Add or remove a port name/ID translation. Duplicate name or ID values are
  // not allowed, and will be rejected. Order matters, so if a consumer needs to
  // swap ID values they should first remove the existing IDs then reinsert the
  // new values.
  virtual absl::Status AddPortTranslation(const std::string& port_name,
                                          const std::string& port_id)
      ABSL_LOCKS_EXCLUDED(server_state_lock_);
  virtual absl::Status RemovePortTranslation(const std::string& port_name)
      ABSL_LOCKS_EXCLUDED(server_state_lock_);

  // Verifies state for the P4RT App. These are checks like:
  //  * Do P4RT table entries match in AppStateDb and AppDb.
  //  * Do VRF_TABLE entries match in AppStateDb and AppDb.
  //  * Do HASH_TABLE entries match in AppStateDb and AppDb.
  //  * Do SWITCH_TABLE entries match in AppStateDb and AppDb.
  //
  // NOTE: We do not verify ownership of table entries today. Therefore, shared
  // tables (e.g. VRF_TABLE) could cause false positives.
  virtual absl::Status VerifyState() ABSL_LOCKS_EXCLUDED(server_state_lock_);

 protected:
  // Simple constructor that should only be used for testing purposes.
  P4RuntimeImpl(bool translate_port_ids)
      : translate_port_ids_(translate_port_ids) {}

 private:
  P4RuntimeImpl(const P4RuntimeImpl&) = delete;
  P4RuntimeImpl& operator=(const P4RuntimeImpl&) = delete;

  // Get and process response from the notification channel, if on error,
  // restore the APPL_DB to the last good state. Uses, the key of the inserted
  // entry to match the response and restore if needed.
  pdpi::IrUpdateStatus GetAndProcessResponse(absl::string_view key);

  absl::Status HandlePacketOutRequest(const p4::v1::PacketOut& packet_out)
      ABSL_EXCLUSIVE_LOCKS_REQUIRED(server_state_lock_);

  // Verify that the target can realize the given config. Will not modify the
  // forwarding state in the target.
  //
  // Returns an error if the config is not provided of if the provided config
  // cannot be realized.
  grpc::Status VerifyPipelineConfig(
      const p4::v1::SetForwardingPipelineConfigRequest& request) const;

  // Verify, save and realize the given config. Today we DO NOT support clearing
  // any forwarding state, and we will return a failure if a config has already
  // been applied.
  //
  // Returns an error if the config is not provided of if the provided config
  // cannot be realized.
  grpc::Status VerifyAndCommitPipelineConfig(
      const p4::v1::SetForwardingPipelineConfigRequest& request)
      ABSL_EXCLUSIVE_LOCKS_REQUIRED(server_state_lock_);

  // Realize the last saved, but not yet committed config.
  //
  // Returns an error if a config is provided, if a config is already realized,
  // or if a no saved config is found.
  grpc::Status CommitPipelineConfig(
      const p4::v1::SetForwardingPipelineConfigRequest& request)
      ABSL_EXCLUSIVE_LOCKS_REQUIRED(server_state_lock_);

  // Verify, save and realize the given config. Today we DO NOT support changing
  // the P4Info in any way, and we will return a failure if we detect any
  // changes. However, new configs can be pushed multiple times so long as the
  // P4Info remains the same.
  //
  // Returns an error if the config is not provided, or if the existing
  // forwarding state cannot be preserved for the given config by the target.
  grpc::Status ReconcileAndCommitPipelineConfig(
      const p4::v1::SetForwardingPipelineConfigRequest& request)
      ABSL_EXCLUSIVE_LOCKS_REQUIRED(server_state_lock_);

  // Tries to save the forwarding config to a file. If the
  // forwarding_config_full_path_ variable is not set it will return OK, but any
  // other issue with saving the config will return an error.
  grpc::Status SavePipelineConfig(
      const p4::v1::ForwardingPipelineConfig& config) const
      ABSL_EXCLUSIVE_LOCKS_REQUIRED(server_state_lock_);

  // Writes the necessary updates from the pipeline config into the AppDb
  // tables. These configurations (e.g. ACLs, hashing, etc.) are needed before
  // we can start accepting write requests.
  absl::Status ConfigureAppDbTables(const pdpi::IrP4Info& ir_p4info)
      ABSL_EXCLUSIVE_LOCKS_REQUIRED(server_state_lock_);

  // Defines the callback lambda function to be invoked for receive packets
  // and calls into the sonic::StartReceive to spawn the receiver thread.
  ABSL_MUST_USE_RESULT absl::StatusOr<std::thread> StartReceive(
      bool use_genetlink);

  // Mutex for constraining actions to access and modify server state.
  absl::Mutex server_state_lock_;

  // Interfaces which are used to update entries in the RedisDB tables.
  sonic::P4rtTable p4rt_table_ ABSL_GUARDED_BY(server_state_lock_);

  // P4RT can accept multiple connections to a single switch for redundancy.
  // When there is >1 connection the switch chooses a primary which is used for
  // PacketIO, and is the only connection allowed to write updates.
  //
  // It is possible for connections to be made for specific roles. In which case
  // one primary connection is allowed for each distinct role.
  std::unique_ptr<SdnControllerManager> controller_manager_
      ABSL_GUARDED_BY(server_state_lock_);

  // SONiC uses name to reference ports (e.g. Ethernet4), but the controller can
  // be configured to send port IDs. The P4RT App takes responsibility for
  // translating between the two.
  //
  // boost::bimap<SONiC port name, controller ID>;
  boost::bimap<std::string, std::string> port_translation_map_
      ABSL_GUARDED_BY(server_state_lock_);

  // A forwarding pipeline config with a P4Info protobuf will be set once a
  // controller connects to the swtich. Only after we receive this config can
  // the P4RT service start processing write requests.
  absl::optional<p4::v1::ForwardingPipelineConfig> forwarding_pipeline_config_
      ABSL_GUARDED_BY(server_state_lock_);

  // The ForwardingConfig can be saved to disk when it is pushed to the switch.
  // It can also be loaded from disk by sending a COMMIT request to the
  // SetForwardingPipelineConfig method.
  absl::optional<std::string> forwarding_config_full_path_
      ABSL_GUARDED_BY(server_state_lock_);

  // Once we receive the P4Info we create a pdpi::IrP4Info object which allows
  // us to translate the PI requests into human-readable objects.
  absl::optional<pdpi::IrP4Info> ir_p4info_ ABSL_GUARDED_BY(server_state_lock_);

  // The P4Info can use annotations to specify table constraints for specific
  // tables. The P4RT service will reject any table entry requests that do not
  // meet these constraints.
  absl::optional<p4_constraints::ConstraintInfo> p4_constraint_info_;

  // PacketIoImplementation object.
  std::thread receive_thread_;
  std::unique_ptr<sonic::PacketIoInterface> packetio_impl_
      ABSL_GUARDED_BY(server_state_lock_);

  // Some switch enviornments cannot rely on the SONiC port names, and can
  // instead choose to use port ID's configured through gNMI.
  const bool translate_port_ids_;
};

}  // namespace p4rt_app

#endif  // GOOGLE_P4RT_APP_P4RUNTIME_P4RUNTIME_IMPL_H_
