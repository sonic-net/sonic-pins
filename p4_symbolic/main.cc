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
#include <map>
#include <string>

#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "absl/flags/usage.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "gutil/status.h"
#include "p4_symbolic/bmv2/bmv2.h"
#include "p4_symbolic/parser.h"
#include "p4_symbolic/sai/parser.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "p4_symbolic/util/io.h"

ABSL_FLAG(std::string, p4info, "",
          "The path to the p4info protobuf file (required)");
ABSL_FLAG(std::string, bmv2, "", "The path to the bmv2 json file (required)");
ABSL_FLAG(std::string, entries, "",
          "The path to the table entries txt file (optional), leave this empty "
          "if the input p4 program contains no (explicit) tables for which "
          "entries are needed.");
ABSL_FLAG(std::string, debug, "", "Dump the SMT program for debugging");
ABSL_FLAG(int, port_count, 2, "Number of used ports (numbered 0 to N-1)");
ABSL_FLAG(bool, hardcoded_parser, true,
          "Use the hardcoded parser during symbolic evaluation");

namespace {
// Parse input P4 program, analyze it symbolically
// and generate test pakcets.
absl::Status ParseAndEvaluate() {
  const std::string &p4info_path = absl::GetFlag(FLAGS_p4info);
  const std::string &bmv2_path = absl::GetFlag(FLAGS_bmv2);
  const std::string &entries_path = absl::GetFlag(FLAGS_entries);
  const std::string &debug_path = absl::GetFlag(FLAGS_debug);
  const int port_count = absl::GetFlag(FLAGS_port_count);
  bool hardcoded_parser = absl::GetFlag(FLAGS_hardcoded_parser);

  RET_CHECK(!p4info_path.empty());
  RET_CHECK(!bmv2_path.empty());

  // Transform to IR.
  ASSIGN_OR_RETURN(
      p4_symbolic::symbolic::Dataplane dataplane,
      p4_symbolic::ParseToIr(bmv2_path, p4info_path, entries_path));

  // Generate port list.
  std::vector<int> physical_ports(port_count);
  for (int i = 0; i < port_count; i++) physical_ports[i] = i;

  // Evaluate program symbolically.
  ASSIGN_OR_RETURN(
      const std::unique_ptr<p4_symbolic::symbolic::SolverState> &solver_state,
      p4_symbolic::symbolic::EvaluateP4Pipeline(dataplane, physical_ports));
  // Add constraints for parser.
  if (hardcoded_parser) {
    ASSIGN_OR_RETURN(
        std::vector<z3::expr> parser_constraints,
        p4_symbolic::EvaluateSaiParser(solver_state->context.ingress_headers));
    for (auto &constraint : parser_constraints) {
      solver_state->solver->add(constraint);
    }
  }

  // Find a packet matching every entry of every table.
  // Loop over tables in a deterministic order for output consistency (important
  // for ci tests).
  std::string debug_smt_formula = "";
  auto ordered_tables = absl::btree_map<std::string, p4_symbolic::ir::Table>(
      dataplane.program.tables().cbegin(), dataplane.program.tables().cend());
  for (const auto &[name, table] : ordered_tables) {
    int row_count = static_cast<int>(dataplane.entries[name].size());
    for (int i = -1; i < row_count; i++) {
      std::cout << "Finding packet for table " << name << " and row " << i
                << std::endl;

      p4_symbolic::symbolic::Assertion table_entry_assertion =
          [name = name,
           i](const p4_symbolic::symbolic::SymbolicContext &symbolic_context) {
            const p4_symbolic::symbolic::SymbolicTableMatch &match =
                symbolic_context.trace.matched_entries.at(name);
            return (!symbolic_context.trace.dropped && match.matched &&
                    match.entry_index == static_cast<int>(i));
          };

      absl::StrAppend(
          &debug_smt_formula,
          p4_symbolic::symbolic::DebugSMT(solver_state, table_entry_assertion),
          "\n");

      ASSIGN_OR_RETURN(
          std::optional<p4_symbolic::symbolic::ConcreteContext> packet_option,
          p4_symbolic::symbolic::Solve(solver_state, table_entry_assertion));

      if (packet_option) {
        // Whether packet was dropped or not!
        std::cout << "\tDropped = " << packet_option.value().trace.dropped
                  << std::endl;

        // Ports
        std::cout << "\tstandard_metadata.ingress_port = "
                  << packet_option.value().ingress_port << std::endl;
        std::cout << "\tstandard_metadata.egress_spec = "
                  << packet_option.value().egress_port << std::endl;
        // IPV4
        if (packet_option.value().egress_headers.count("ipv4.srcAddr")) {
          std::cout << "\tipv4.srcAddr = "
                    << packet_option.value().egress_headers.at("ipv4.srcAddr")
                    << std::endl;
        }
        if (packet_option.value().egress_headers.count("ipv4.dstAddr")) {
          std::cout << "\tipv4.dstAddr = "
                    << packet_option.value().egress_headers.at("ipv4.dstAddr")
                    << std::endl;
        }
        // Ethernet
        if (packet_option.value().egress_headers.count("ethernet.dstAddr")) {
          std::cout << "\tethernet.dstAddr = "
                    << packet_option.value().egress_headers.at(
                           "ethernet.dstAddr")
                    << std::endl;
        }
        // VRF
        if (packet_option.value().egress_headers.count(
                "scalars.userMetadata.vrf")) {
          std::cout << "\tscalars.userMetadata.vrf = "
                    << packet_option.value().egress_headers.at(
                           "scalars.userMetadata.vrf")
                    << std::endl;
        }
        if (packet_option.value().egress_headers.count(
                "scalars.userMetadata.vrf_is_valid")) {
          std::cout << "\tscalars.userMetadata.vrf_is_valid = "
                    << packet_option.value().egress_headers.at(
                           "scalars.userMetadata.vrf_is_valid")
                    << std::endl;
        }
        // Custom metadata field defined in testdata/string-optional/program.p4
        if (packet_option.value().egress_headers.contains(
                "scalars.userMetadata.string_field")) {
          std::cout << "\tscalars.userMetadata.string_field = "
                    << packet_option.value().egress_headers.at(
                           "scalars.userMetadata.string_field")
                    << std::endl;
        }
      } else {
        std::cout << "Cannot find solution!" << std::endl;
      }
      std::cout << std::endl;
    }
  }

  // Debugging.
  if (!debug_path.empty()) {
    RETURN_IF_ERROR(
        p4_symbolic::util::WriteFile(debug_smt_formula, debug_path));
  }

  return absl::OkStatus();
}

}  // namespace

int main(int argc, char *argv[]) {
  // Verify link and compile versions are the same.
  // GOOGLE_PROTOBUF_VERIFY_VERSION;

  // Command line arugments and help message.
  absl::SetProgramUsageMessage(absl::StrFormat(
      "usage: %s %s", argv[0],
      "--bmv2=path/to/bmv2.json --p4info=path/to/p4info.pb.txt "
      "[--entries=path/to/table_entries.txt] [--hardcoded_parser=false]"));
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
