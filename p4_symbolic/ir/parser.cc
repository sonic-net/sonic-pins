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

#include "p4_symbolic/ir/parser.h"

#include "absl/status/statusor.h"
#include "absl/types/span.h"
#include "gutil/gutil/status.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_symbolic/bmv2/bmv2.h"
#include "p4_symbolic/ir/ir.h"
#include "p4_symbolic/ir/table_entries.h"

namespace p4_symbolic::ir {

absl::StatusOr<Dataplane> ParseToIr(
    const p4::v1::ForwardingPipelineConfig &config,
    absl::Span<const p4::v1::Entity> entities) {
  ASSIGN_OR_RETURN(bmv2::P4Program bmv2,
                   bmv2::ParseBmv2JsonString(config.p4_device_config()),
                   _.SetPrepend() << "While trying to parse BMv2 JSON: ");
  ASSIGN_OR_RETURN(const pdpi::IrP4Info ir_p4info,
                   pdpi::CreateIrP4Info(config.p4info()));
  ASSIGN_OR_RETURN(P4Program program, Bmv2AndP4infoToIr(bmv2, ir_p4info));
  ASSIGN_OR_RETURN(TableEntries ir_entities,
                   ParseTableEntries(ir_p4info, entities));
  return Dataplane{program, ir_entities};
}

}  // namespace p4_symbolic::ir
