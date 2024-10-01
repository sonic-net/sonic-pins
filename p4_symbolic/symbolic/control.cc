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

// This file is responsible for evaluating a control construct in a P4
// program flow. A control construct could be a table match or a conditional
// leading to a table match.
//
// Check the header file for a detailed explanation.

#include "p4_symbolic/symbolic/control.h"

#include <vector>

#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "gutil/status.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_symbolic/symbolic/conditional.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "p4_symbolic/symbolic/table.h"

namespace p4_symbolic::symbolic::control {

absl::StatusOr<SymbolicTrace> EvaluateV1model(
    const Dataplane &data_plane, SymbolicPerPacketState *state,
    values::P4RuntimeTranslator *translator) {
  // Initial, empty trace.
  auto trace = SymbolicTrace{.dropped = Z3Context().bool_val(false)};

  // Extend trace by evaluating the v1model pipelines.
  std::vector<std::string> v1model_pipelines = {"ingress", "egress"};
  for (const auto &pipeline : v1model_pipelines) {
    ASSIGN_OR_RETURN(SymbolicTrace suffix_trace,
                     EvaluatePipeline(data_plane, pipeline, state, translator,
                                      !trace.dropped));

    // Extend existing trace with suffix.
    trace.dropped = suffix_trace.dropped;
    for (auto &[table, match] : suffix_trace.matched_entries) {
      if (trace.matched_entries.count(table) != 0) {
        return gutil::UnimplementedErrorBuilder()
               << "table '" << table << "' was executed in '" << pipeline
               << "' pipeline after already being executed in an earlier "
                  "pipeline; this is not supported by p4-symbolic";
      }
      trace.matched_entries.insert({table, match});
    }
  }

  return trace;
}

absl::StatusOr<SymbolicTrace> EvaluatePipeline(
    const Dataplane &data_plane, const std::string &pipeline_name,
    SymbolicPerPacketState *state, values::P4RuntimeTranslator *translator,
    const z3::expr &guard) {
  if (auto it = data_plane.program.pipeline().find(pipeline_name);
      it != data_plane.program.pipeline().end()) {
    return EvaluateControl(data_plane, it->second.initial_control(), state,
                           translator, guard);
  }
  return gutil::InvalidArgumentErrorBuilder()
         << "cannot evaluate unknown pipeline: '" << pipeline_name << "'";
}

absl::StatusOr<SymbolicTrace> EvaluateControl(
    const Dataplane &data_plane, const std::string &control_name,
    SymbolicPerPacketState *state, values::P4RuntimeTranslator *translator,
    const z3::expr &guard) {
  // Base case: we got to the end of the evaluation, no more controls!
  if (control_name.empty()) {
    return SymbolicTrace{{}, Z3Context().bool_val(false)};
  }

  // Find out what type of control we need to evaluate.
  if (data_plane.program.tables().count(control_name) == 1) {
    // Table: call EvaluateTable on table and its entries.
    const ir::Table &table = data_plane.program.tables().at(control_name);
    std::vector<pdpi::IrTableEntry> table_entries;
    if (data_plane.entries.count(control_name) == 1) {
      table_entries = data_plane.entries.at(control_name);
    }
    return table::EvaluateTable(data_plane, table, table_entries, state,
                                translator, guard);
  } else if (data_plane.program.conditionals().count(control_name) == 1) {
    // Conditional: let EvaluateConditional handle it.
    const ir::Conditional &conditional =
        data_plane.program.conditionals().at(control_name);
    return conditional::EvaluateConditional(data_plane, conditional, state,
                                            translator, guard);
  } else {
    // Something else: unsupported.
    return absl::UnimplementedError(
        absl::StrCat("Unsupported control \"", control_name,
                     "\" is neither a table nor a conditional"));
  }
}

}  // namespace p4_symbolic::symbolic::control
