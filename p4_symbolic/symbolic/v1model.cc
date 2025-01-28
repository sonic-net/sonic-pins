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

#include "p4_symbolic/symbolic/v1model.h"

#include <array>
#include <string>
#include <utility>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_format.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "gutil/status.h"
#include "p4_pdpi/internal/ordered_map.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/symbolic/context.h"
#include "p4_symbolic/symbolic/control.h"
#include "p4_symbolic/symbolic/guarded_map.h"
#include "p4_symbolic/symbolic/operators.h"
#include "p4_symbolic/symbolic/parser.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "p4_symbolic/symbolic/v1model_intrinsic.h"
#include "z3++.h"

namespace p4_symbolic {
namespace symbolic {
namespace v1model {

namespace {

// Initializes standard metadata fields to zero, except for `ingress_port`,
// `egress_port`, and `packet_length`.
absl::Status InitializeStandardMetadata(const ir::P4Program &program,
                                        SymbolicPerPacketState &headers,
                                        z3::context &z3_context) {
  // Check if the standard metadata header exists.
  auto it = program.headers().find(kStandardMetadataHeaderName);
  if (it == program.headers().end()) {
    return gutil::InternalErrorBuilder()
           << "Header '" << kStandardMetadataHeaderName
           << "' not found in P4 program.";
  }

  const google::protobuf::Map<std::string, ir::HeaderField>
      &standard_metadata_fields = it->second.fields();

  // List of standard metadata fields to be initialized to zero. See
  // https://github.com/p4lang/p4c/blob/main/p4include/v1model.p4 for the full
  // list of fields.
  static constexpr std::array kFieldsToBeInitialized = {
      // The ingress port should not be fixed.
      // "ingress_port",
      "egress_spec",
      // TODO: Whenever `egress_port` is initialized to zero,
      // `packet_util_production_test` fails. It would be helpful to understand
      // why that's the case.
      // "egress_port",
      "instance_type",
      // TODO: Packet length depends on the validity of headers.
      // "packet_length",
      "enq_timestamp",
      "enq_qdepth",
      "deq_timedelta",
      "deq_qdepth",
      "ingress_global_timestamp",
      "egress_global_timestamp",
      "mcast_grp",
      "egress_rid",
      "checksum_error",
      "parser_error",
      "priority",
  };

  // Initialize the listed standard metadata fields to zero.
  for (const absl::string_view field_name : kFieldsToBeInitialized) {
    auto it = standard_metadata_fields.find(field_name);
    if (it == standard_metadata_fields.end()) {
      return gutil::InternalErrorBuilder()
             << "Field '" << field_name << "' not found in standard metadata.";
    }

    std::string field_full_name =
        absl::StrFormat("%s.%s", kStandardMetadataHeaderName, field_name);
    z3::expr zero = z3_context.bv_val(
        (field_name == "instance_type" ? PKT_INSTANCE_TYPE_NORMAL : 0),
        it->second.bitwidth());
    RETURN_IF_ERROR(headers.UnguardedSet(field_full_name, zero));
  }

  return absl::OkStatus();
}

absl::Status CheckPhysicalPortsConformanceToV1Model(
    const std::vector<int> &physical_ports) {
  for (const int port : physical_ports) {
    if (port < 0 || port >= 512) {
      return absl::InvalidArgumentError(absl::Substitute(
          "Cannot use the value $0 as a physical port as the value does not "
          "fit into PortId_t (bit<9>), the type of "
          "standard_metadata.{ingress/egress}_port in v1model.p4.",
          port));
    }
    if (port == kDropPort) {
      return gutil::InvalidArgumentErrorBuilder()
             << "cannot use physical port " << kDropPort
             << " as p4-symbolic reserves it to encode dropping a packet; see "
                "the documentation of `mark_to_drop` in v1mode1.p4 for details";
    }
    if (port == kCpuPort) {
      return absl::InvalidArgumentError(
          absl::Substitute("Cannot use the value $0 as a physical port as the "
                           "value is reserved for the CPU port.",
                           port));
    }
  }

  return absl::OkStatus();
}

absl::StatusOr<z3::expr> IsDropped(const SymbolicPerPacketState &state,
                                   z3::context &z3_context) {
  ASSIGN_OR_RETURN(z3::expr egress_spec,
                   state.Get("standard_metadata.egress_spec"));
  return operators::Eq(egress_spec, EgressSpecDroppedValue(z3_context));
}

absl::StatusOr<z3::expr> GotCloned(const SymbolicPerPacketState &state) {
  return state.Get(std::string(kGotClonedPseudoField));
}

}  // namespace

z3::expr EgressSpecDroppedValue(z3::context &z3_context) {
  return z3_context.bv_val(kDropPort, kPortBitwidth);
}

absl::Status InitializeIngressHeaders(const ir::P4Program &program,
                                      SymbolicPerPacketState &ingress_headers,
                                      z3::context &z3_context) {
  RETURN_IF_ERROR(
      InitializeStandardMetadata(program, ingress_headers, z3_context));

  // Set the `$valid$` and `$extracted$` fields of all headers to false.
  const z3::expr false_expr = z3_context.bool_val(false);
  for (const auto &[header_name, _] : Ordered(program.headers())) {
    RETURN_IF_ERROR(ingress_headers.UnguardedSet(header_name, kValidPseudoField,
                                                 false_expr));
    RETURN_IF_ERROR(ingress_headers.UnguardedSet(
        header_name, kExtractedPseudoField, false_expr));
  }

  return absl::OkStatus();
}

absl::Status EvaluateV1model(SolverState &state,
                             const std::vector<int> &physical_ports) {
  SymbolicContext &context = state.context;

  // Check input physical ports.
  RETURN_IF_ERROR(CheckPhysicalPortsConformanceToV1Model(physical_ports));

  // The ingress headers represent the symbolic ingress packet before entering
  // the parsers or the pipelines. It contains an unconstrained symbolic
  // variable for each header field.
  ASSIGN_OR_RETURN(context.ingress_headers,
                   SymbolicGuardedMap::CreateSymbolicGuardedMap(
                       *context.z3_context, state.program.headers()));
  // Initialize the symbolic ingress packet before evaluation.
  RETURN_IF_ERROR(InitializeIngressHeaders(
      state.program, context.ingress_headers, *context.z3_context));

  // Evaluate all parsers in the P4 program.
  // If a parser error occurs, the `standard_metadata.parser_error` field will
  // be set to the corresponding error code and the execution will continue
  // directly to the ingress pipeline. The current implementation of P4-Symbolic
  // will only yield 2 kinds of parser error, NoError and NoMatch.
  ASSIGN_OR_RETURN(
      context.parsed_headers,
      parser::EvaluateParsers(state.program, context.ingress_headers,
                              *context.z3_context));

  // Update the ingress_headers' valid fields to be parsed_headers' extracted
  // fields.
  for (const auto &[header_name, _] : Ordered(state.program.headers())) {
    ASSIGN_OR_RETURN(
        z3::expr extracted,
        context.parsed_headers.Get(header_name, kExtractedPseudoField));
    RETURN_IF_ERROR(context.ingress_headers.UnguardedSet(
        header_name, kValidPseudoField, extracted));
  }

  // Duplicate the symbolic headers for evaluating pipelines. This is to
  // preserve the symbolic state after evaluating the parsers but before
  // evaluating the pipelines.
  context.egress_headers = context.parsed_headers;

  // Evaluate the ingress pipeline.
  // TODO: This is a simplification that omits a lot of features, e.g.
  // cloning, digests, resubmit, and multicast. The full semantics we should
  // implement is documented here:
  // https://github.com/p4lang/behavioral-model/blob/main/docs/simple_switch.md#pseudocode-for-what-happens-at-the-end-of-ingress-and-egress-processing
  ASSIGN_OR_RETURN(
      SymbolicTableMatches matches,
      control::EvaluatePipeline("ingress", state, context.egress_headers,
                                /*guard=*/context.z3_context->bool_val(true)));
  ASSIGN_OR_RETURN(z3::expr dropped,
                   IsDropped(context.egress_headers, *context.z3_context));

  // Assign egress_spec to egress_port if the packet is not dropped.
  // https://github.com/p4lang/behavioral-model/blob/main/docs/simple_switch.md
  ASSIGN_OR_RETURN(z3::expr egress_spec,
                   context.egress_headers.Get("standard_metadata.egress_spec"));
  RETURN_IF_ERROR(context.egress_headers.Set("standard_metadata.egress_port",
                                             egress_spec,
                                             /*guard=*/!dropped));

  // Evaluate the egress pipeline.
  ASSIGN_OR_RETURN(
      SymbolicTableMatches egress_matches,
      control::EvaluatePipeline("egress", state, context.egress_headers,
                                /*guard=*/!dropped));
  matches.merge(std::move(egress_matches));

  // Populate and build the symbolic context.
  context.trace.matched_entries = std::move(matches);
  ASSIGN_OR_RETURN(context.trace.dropped,
                   IsDropped(context.egress_headers, *context.z3_context));
  ASSIGN_OR_RETURN(context.trace.got_cloned, GotCloned(context.egress_headers));
  ASSIGN_OR_RETURN(context.ingress_port, context.ingress_headers.Get(
                                             "standard_metadata.ingress_port"));
  ASSIGN_OR_RETURN(context.egress_port,
                   context.egress_headers.Get("standard_metadata.egress_spec"));
  return absl::OkStatus();
}

}  // namespace v1model
}  // namespace symbolic
}  // namespace p4_symbolic
