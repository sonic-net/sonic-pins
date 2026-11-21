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

#include <memory>
#include <utility>

#include "absl/status/statusor.h"
#include "gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_infra/p4_runtime/p4_runtime_session.h"
#include "thinkit/switch.h"

namespace p4_runtime {

absl::StatusOr<std::unique_ptr<P4RuntimeSession>> P4RuntimeSession::Create(
    thinkit::Switch& thinkit_switch,
    const P4RuntimeSessionOptionalArgs& metadata, bool error_if_not_primary) {
  ASSIGN_OR_RETURN(auto stub, thinkit_switch.CreateP4RuntimeStub());
  return Create(std::move(stub), thinkit_switch.DeviceId(), metadata,
                error_if_not_primary);
}

absl::StatusOr<std::unique_ptr<P4RuntimeSession>>
P4RuntimeSession::CreateWithP4InfoAndClearTables(
    thinkit::Switch& thinkit_switch, const p4::config::v1::P4Info& p4info,
    const P4RuntimeSessionOptionalArgs& metadata) {
  ASSIGN_OR_RETURN(std::unique_ptr<P4RuntimeSession> session,
                   P4RuntimeSession::Create(thinkit_switch, metadata));
  RETURN_IF_ERROR(ClearEntities(*session));
  RETURN_IF_ERROR(SetMetadataAndSetForwardingPipelineConfig(
      session.get(),
      p4::v1::SetForwardingPipelineConfigRequest_Action_RECONCILE_AND_COMMIT,
      p4info));
  RETURN_IF_ERROR(CheckNoEntities(*session)).SetPrepend()
      << "cleared all entities and set a new forwarding pipeline config: ";
  return session;
}

}  // namespace p4_runtime
