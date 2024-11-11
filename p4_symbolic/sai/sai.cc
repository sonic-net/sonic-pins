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

#include "p4_symbolic/sai/sai.h"

#include <memory>
#include <string>
#include <type_traits>
#include <vector>

#include "absl/status/statusor.h"
#include "gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_symbolic/parser.h"
#include "p4_symbolic/sai/parser.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_nonstandard_platforms.h"

namespace p4_symbolic {

namespace {

absl::StatusOr<symbolic::Dataplane> GetSaiDataplane(
    sai::Instantiation instantiation,
    const std::vector<p4::v1::TableEntry>& entries) {
  auto platform = sai::NonstandardPlatform::kP4Symbolic;
  std::string p4_config = sai::GetNonstandardP4Config(instantiation, platform);
  p4::config::v1::P4Info p4info =
      sai::GetNonstandardP4Info(instantiation, platform);
  ASSIGN_OR_RETURN(const pdpi::IrP4Info ir_p4info,
                   pdpi::CreateIrP4Info(p4info));
  return ParseToIr(p4_config, ir_p4info, entries);
}

}  // namespace

absl::StatusOr<std::unique_ptr<symbolic::SolverState>> EvaluateSaiPipeline(
    sai::Instantiation instantiation,
    const std::vector<p4::v1::TableEntry>& entries,
    const std::vector<int>& physical_ports) {
  ASSIGN_OR_RETURN(symbolic::Dataplane dataplane,
                   GetSaiDataplane(instantiation, entries));
  ASSIGN_OR_RETURN(std::unique_ptr<symbolic::SolverState> state,
                   symbolic::EvaluateP4Pipeline(dataplane, physical_ports));
  ASSIGN_OR_RETURN(std::vector<z3::expr> parser_constraints,
                   EvaluateSaiParser(state->context.ingress_headers));
  for (auto& constraint : parser_constraints) {
    state->solver->add(constraint);
  }
  return state;
}

}  // namespace p4_symbolic
