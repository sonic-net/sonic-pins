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

#include "p4/v1/p4runtime.pb.h"
#include "sai_p4/fixed/ids.h"

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

}  // namespace sai
