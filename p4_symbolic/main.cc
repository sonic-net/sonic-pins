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

// Main file for finding P4 test packets symbolically.
// Expects input bmv2 json, p4info, and table entries files as command
// line flags.
// Produces test packets that hit every row in the P4 program tables.

#include <iostream>
#include <memory>
#include <optional>
#include <sstream>
#include <string>
#include <vector>

#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "absl/flags/usage.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/strings/str_format.h"
#include "google/protobuf/message_lite.h"
#include "gutil/io.h"
#include "gutil/ordered_map.h"
#include "gutil/status.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_symbolic/symbolic/context.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "p4_symbolic/test_util.h"

ABSL_FLAG(std::string, p4info, "",
          "The path to the p4info protobuf file (required)");
ABSL_FLAG(std::string, bmv2, "", "The path to the bmv2 json file (required)");
ABSL_FLAG(std::string, entries, "",
          "The path to the table entries txt file (optional), leave this empty "
          "if the input p4 program contains no (explicit) tables for which "
          "entries are needed.");
ABSL_FLAG(std::string, packets, "", "The concrete packets output file");
ABSL_FLAG(std::string, smt, "", "The SMT program output file");
ABSL_FLAG(int, port_count, 2, "Number of used ports (numbered 0 to N-1)");

namespace {

// Finds a packet matching every table entry.
absl::StatusOr<std::string> GetConcretePacketsCoveringAllTableEntries(
    p4_symbolic::symbolic::SolverState &solver_state) {
  constexpr int kColumnSize = 80;
  std::ostringstream result;

  // Loop over tables in a deterministic order for output consistency
  // (important for CI tests).
  for (const auto &[table_name, table] :
       gutil::AsOrderedView(solver_state.program.tables())) {
    int row_count = 0;
    if (solver_state.context.table_entries.count(table_name) > 0) {
      row_count = static_cast<int>(
          solver_state.context.table_entries.at(table_name).size());
    }

    for (int i = -1; i < row_count; i++) {
      std::string banner = "Finding packet for table " + table_name +
                           " and row " + std::to_string(i);
      result << std::string(kColumnSize, '=') << std::endl
             << banner << std::endl
             << std::string(kColumnSize, '=') << std::endl;

      p4_symbolic::symbolic::Assertion table_entry_assertion =
          [name = table_name,
           i](const p4_symbolic::symbolic::SymbolicContext &symbolic_context) {
            const p4_symbolic::symbolic::SymbolicTableMatch &match =
                symbolic_context.trace.matched_entries.at(name);
            return (!symbolic_context.trace.dropped && match.matched &&
                    match.entry_index == static_cast<int>(i));
          };

      ASSIGN_OR_RETURN(
          std::optional<p4_symbolic::symbolic::ConcreteContext> concrete_packet,
          p4_symbolic::symbolic::Solve(solver_state, table_entry_assertion));

      if (concrete_packet) {
        result << concrete_packet->to_string(/*verbose=*/true) << std::endl;
      } else {
        result << "Cannot find solution!" << std::endl;
      }
      result << std::string(kColumnSize, '_') << std::endl << std::endl;
    }
  }

  return result.str();
}

// Parses input P4 program, analyzes it symbolically and generates test packets.
absl::Status ParseAndEvaluate() {
  const std::string &p4info_path = absl::GetFlag(FLAGS_p4info);
  const std::string &bmv2_path = absl::GetFlag(FLAGS_bmv2);
  const std::string &entries_path = absl::GetFlag(FLAGS_entries);
  const std::string &packets_path = absl::GetFlag(FLAGS_packets);
  const std::string &smt_path = absl::GetFlag(FLAGS_smt);
  const int port_count = absl::GetFlag(FLAGS_port_count);

  RET_CHECK(!p4info_path.empty());
  RET_CHECK(!bmv2_path.empty());

  ASSIGN_OR_RETURN(
      p4::v1::ForwardingPipelineConfig config,
      p4_symbolic::ParseToForwardingPipelineConfig(bmv2_path, p4info_path));
  ASSIGN_OR_RETURN(
      std::vector<p4::v1::Entity> entities,
      p4_symbolic::GetPiEntitiesFromPiUpdatesProtoTextFile(entries_path));

  // Generate port list.
  std::vector<int> physical_ports(port_count);
  for (int i = 0; i < port_count; i++) physical_ports[i] = i;

  // Evaluate program symbolically.
  ASSIGN_OR_RETURN(
      std::unique_ptr<p4_symbolic::symbolic::SolverState> solver_state,
      p4_symbolic::symbolic::EvaluateP4Program(config, entities,
                                               physical_ports));

  // Output SMT formula.
  if (!smt_path.empty()) {
    RETURN_IF_ERROR(gutil::WriteFile(
        solver_state->GetHeadersAndSolverConstraintsSMT(), smt_path));
  }

  // Solve and output a concrete packet for each table entry.
  if (packets_path.empty()) {
    LOG(WARNING) << "No output path is provided for concrete packets. Consider "
                    "using --packets=path/to/packets.txt option.";
  } else {
    ASSIGN_OR_RETURN(std::string concrete_packets,
                     GetConcretePacketsCoveringAllTableEntries(*solver_state));
    RETURN_IF_ERROR(gutil::WriteFile(concrete_packets, packets_path));
  }

  return absl::OkStatus();
}

}  // namespace

int main(int argc, char *argv[]) {
  // Verify link and compile versions are the same.
  // GOOGLE_PROTOBUF_VERIFY_VERSION;

  // Command line arguments and help message.
  absl::SetProgramUsageMessage(absl::StrFormat(
      "usage: %s %s", argv[0],
      "--bmv2=path/to/bmv2.json --p4info=path/to/p4info.pb.txt "
      "[--entries=path/to/table_entries.txt] [--packets=path/to/packets.txt] "
      "[--smt=path/to/formulas.smt2] [--port_count=N]"));
  absl::ParseCommandLine(argc, argv);

  // Run code
  absl::Status status = ParseAndEvaluate();

  // Clean up
  google::protobuf::ShutdownProtobufLibrary();

  // Error handling.
  if (!status.ok()) {
    std::cerr << "Error: " << status << std::endl;
    return 1;
  }

  return 0;
}
