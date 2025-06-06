// Copyright 2024 Google LLC
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

#include "sai_p4/tools/auxiliary_entries_for_v1model_targets.h"

#include <string>

#include "absl/container/btree_set.h"
#include "absl/status/statusor.h"
#include "gutil/status.h"
#include "lib/gnmi/gnmi_helper.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "sai_p4/fixed/ids.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"

namespace sai {

p4::v1::Entity MakeV1modelPacketReplicationEngineEntryRequiredForPunts() {
  p4::v1::Entity entity;

  p4::v1::CloneSessionEntry& clone_session =
      *entity.mutable_packet_replication_engine_entry()
           ->mutable_clone_session_entry();
  clone_session.set_session_id(COPY_TO_CPU_SESSION_ID);
  p4::v1::Replica& replica = *clone_session.add_replicas();
  replica.set_egress_port(SAI_P4_CPU_PORT);
  replica.set_instance(SAI_P4_REPLICA_INSTANCE_PACKET_IN);

  return entity;
}

absl::StatusOr<pdpi::IrEntities> CreateV1ModelAuxiliaryTableEntries(
    gnmi::gNMI::StubInterface& gnmi_stub, pdpi::IrP4Info ir_p4info) {
  // Get the loopback mode map from the gNMI stub
  absl::btree_set<std::string> loopback_mode_port_set;
  ASSIGN_OR_RETURN(
      loopback_mode_port_set,
      pins_test::GetP4rtIdOfInterfacesInAsicMacLocalLoopbackMode(gnmi_stub));

  // Create IrEntities by using the gNMI loopback mode map to fill the loopback
  // table entries.
  pdpi::IrEntities ir_entities;
  for (const auto& loopback_mode_port : loopback_mode_port_set) {
    pdpi::IrEntity* ir_entity = ir_entities.add_entities();
    ir_entity->mutable_table_entry()->set_table_name(
        "egress_port_loopback_table");
    pdpi::IrMatch* match =
        ir_entity->mutable_table_entry()->mutable_matches()->Add();
    match->set_name("out_port");
    match->mutable_exact()->set_str(loopback_mode_port);
    ir_entity->mutable_table_entry()->mutable_action()->set_name(
        "egress_loopback");
  }

  return ir_entities;
}

}  // namespace sai
