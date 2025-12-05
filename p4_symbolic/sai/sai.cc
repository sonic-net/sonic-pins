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

#include <cstdint>
#include <optional>
#include <string>
#include <vector>

#include "absl/container/flat_hash_set.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/ascii.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_join.h"
#include "absl/strings/string_view.h"
#include "gutil/gutil/collections.h"
#include "gutil/gutil/status.h"
#include "p4_pdpi/internal/ordered_map.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_symbolic/ir/ir.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/symbolic/context.h"
#include "p4_symbolic/symbolic/operators.h"
#include "p4_symbolic/symbolic/solver_state.h"
#include "p4_symbolic/symbolic/symbolic_table_entry.h"
#include "p4_symbolic/symbolic/util.h"
#include "p4_symbolic/symbolic/values.h"
#include "z3++.h"

namespace p4_symbolic {

absl::Status CheckPhysicalPortAndPortIdTypeValueConsistency(
    const std::vector<int> &physical_ports,
    const symbolic::TranslationPerType &translation_per_type) {
  absl::flat_hash_set<uint64_t> physical_port_set(physical_ports.begin(),
                                                  physical_ports.end());
  absl::flat_hash_set<uint64_t> numeric_value_set;
  if (auto it = translation_per_type.find(kPortIdTypeName);
      it != translation_per_type.end()) {
    for (const auto &[_, numeric_value] : it->second.static_mapping) {
      // Ignore mapping for CPU port (if any).
      if (numeric_value == symbolic::kCpuPort) continue;

      numeric_value_set.insert(numeric_value);
    }
  }

  if (physical_port_set != numeric_value_set) {
    return absl::InvalidArgumentError(absl::StrCat(
        "Input physical port is inconsistent with the static mapping for ",
        kPortIdTypeName));
  }

  return absl::OkStatus();
}

absl::Status AddVrfIdTypeTranslation(
    symbolic::TranslationPerType &translation_per_type) {
  if (translation_per_type.contains(kVrfIdTypeName)) {
    return absl::InvalidArgumentError(absl::StrCat(
        "Did not expect user defined translation for ", kVrfIdTypeName));
  }

  // TODO: A temporary workaround until the issue is fixed.
  // Map the string "" to value 0. The rest of the mapping is done dynamically.
  translation_per_type[kVrfIdTypeName] = symbolic::values::TranslationData{
      .static_mapping = {{"", 0}},
      .dynamic_translation = true,
  };

  return absl::OkStatus();
}

absl::StatusOr<std::string> GetUserMetadataFieldName(
    absl::string_view field_name,
    const symbolic::SymbolicPerPacketState &state) {
  // Compute set of mangled field names that match the given field name.
  std::vector<std::string> mangled_candidates;

  // p4c seems to use the following template to name user metadata fields:
  //
  // - Until ~ 2022-11-01:
  //   "scalars.userMetadata._<field name><a number>"
  //
  // - After ~ 2022-11-01:
  //  "scalars.<user metadata typename>._<field name><a number>", where
  //  <user metadata typename> is the header type name of the given
  //  `header_name`.
  //
  // We look for names that match these templates.
  // TODO: Remove the old prefix eventually when we no
  // longer need backward compatibility.
  std::vector<std::string> fully_qualified_field_prefixes;
  fully_qualified_field_prefixes.reserve(2);
  // Old prefix.
  fully_qualified_field_prefixes.push_back(
      absl::StrCat("scalars.userMetadata._", field_name));
  // New prefix. Note that this is SAI-specific.
  fully_qualified_field_prefixes.push_back(
      absl::StrCat("scalars.local_metadata_t._", field_name));

  for (const auto &[key, _] : state) {
    for (absl::string_view prefix : fully_qualified_field_prefixes) {
      if (absl::StartsWith(key, prefix) && key.length() > prefix.length() &&
          absl::ascii_isdigit(key.at(prefix.length()))) {
        mangled_candidates.push_back(key);
      }
    }
  }

  if (mangled_candidates.size() == 1) {
    return mangled_candidates.back();
  }

  auto error = gutil::InternalErrorBuilder()
               << "unable to disambiguate metadata field '" << field_name
               << "': ";
  if (mangled_candidates.empty()) {
    return error << "no matching fields found in config: "
                 << absl::StrJoin(state, "\n  - ",
                                  [](std::string *out, const auto &key_value) {
                                    absl::StrAppend(out, key_value.first);
                                  });
  }
  return error << "several mangled fields in the config match:\n- "
               << absl::StrJoin(mangled_candidates, "\n- ");
}

absl::StatusOr<std::string> GetLocalMetadataIngressPortFromModel(
    const symbolic::SolverState &solver_state,
    std::optional<symbolic::SymbolicPerPacketState> headers) {
  ASSIGN_OR_RETURN(
      std::string ingress_port_field_name,
      GetUserMetadataFieldName("ingress_port",
                               headers.has_value()
                                   ? headers.value()
                                   : solver_state.context.parsed_headers));
  ASSIGN_OR_RETURN(
      z3::expr ingress_port_expr,
      headers.has_value()
          ? headers.value().Get(ingress_port_field_name)
          : solver_state.context.parsed_headers.Get(ingress_port_field_name));
  ASSIGN_OR_RETURN(auto translated_value,
                   symbolic::values::TranslateZ3ValueStringToP4RT(
                       solver_state.solver->get_model()
                           .eval(ingress_port_expr, true)
                           .to_string(),
                       ingress_port_field_name,
                       /*type_name=*/std::nullopt, solver_state.translator));
  return translated_value.first;
}

absl::Status AddConstraintsForP4ConstraintsAnnotations(
    symbolic::SolverState &state) {
  RETURN_IF_ERROR(AddConstraintsToForbidVrfZero(state));
  RETURN_IF_ERROR(AddConstraintsForAclPreIngressTable(state));
  RETURN_IF_ERROR(AddConstraintsForAclIngressTable(state));
  return absl::OkStatus();
}

absl::Status AddConstraintsToForbidVrfZero(symbolic::SolverState &state) {
  // Restrict the values of all header fields with type `vrf_id_t` to non-zero.
  for (const auto &[field_name, type_name] :
       Ordered(state.translator.fields_p4runtime_type)) {
    if (type_name == kVrfIdTypeName) {
      ASSIGN_OR_RETURN(z3::expr value,
                       state.context.ingress_headers.Get(field_name));
      state.solver->add(value != 0);
    }
  }

  // Restrict the values of all symbolic variables of type `vrf_id_t` in table
  // entries to non-zero.
  for (const auto &[table_name, entries_per_table] :
       state.context.table_entries) {
    ASSIGN_OR_RETURN(const ir::Table *table,
                     symbolic::util::GetIrTable(state.program, table_name));
    for (const ir::TableEntry &entry : entries_per_table) {
      if (!entry.has_symbolic_entry()) continue;
      const ir::SymbolicTableEntry &symbolic_entry = entry.symbolic_entry();

      // Constrain the symbolic variables for entry matches.
      for (const pdpi::IrMatch &symbolic_match :
           symbolic_entry.sketch().matches()) {
        const std::string &match_name = symbolic_match.name();
        ASSIGN_OR_RETURN(
            pdpi::IrMatchFieldDefinition match_definition,
            symbolic::util::GetMatchDefinition(match_name, *table));
        // Get the match field type name.
        std::string type_name =
            match_definition.match_field().type_name().name();
        // If the match field type is not populated in the match definition, get
        // the type name based on the matched field name if the matched field is
        // a translated type.
        if (type_name.empty()) {
          ASSIGN_OR_RETURN(
              std::string field_name,
              symbolic::util::GetFieldNameFromMatch(match_name, *table));
          auto it = state.translator.fields_p4runtime_type.find(field_name);
          if (it != state.translator.fields_p4runtime_type.end())
            type_name = it->second;
        }

        if (type_name == kVrfIdTypeName) {
          ASSIGN_OR_RETURN(symbolic::SymbolicMatch match_variables,
                           symbolic::GetSymbolicMatch(
                               symbolic_entry, match_name, *table,
                               state.program, *state.context.z3_context));
          state.solver->add(match_variables.value != 0);
        }
      }

      // Constrain the symbolic variables for action parameters.
      for (const auto &action_ref : table->table_definition().entry_actions()) {
        const std::string &action_name = action_ref.action().preamble().name();

        // Check and get the action in P4-Symbolic IR.
        auto it = state.program.actions().find(action_name);
        if (it == state.program.actions().end()) {
          return gutil::NotFoundErrorBuilder()
                 << "Action '" << action_name << "' not found.";
        }
        const ir::Action &action = it->second;

        for (const auto &[param_name, param_definition] :
             Ordered(action.action_definition().params_by_name())) {
          const std::string &type_name =
              param_definition.param().type_name().name();

          if (type_name == kVrfIdTypeName) {
            ASSIGN_OR_RETURN(z3::expr param,
                             symbolic::GetSymbolicActionParameter(
                                 symbolic_entry, param_name, action, *table,
                                 *state.context.z3_context));
            state.solver->add(param != 0);
          }
        }
      }
    }
  }

  return absl::OkStatus();
}

absl::Status AddConstraintsForAclPreIngressTable(symbolic::SolverState &state) {
  constexpr absl::string_view kAclPreIngressTableName =
      "ingress.acl_pre_ingress.acl_pre_ingress_table";
  auto it = state.context.table_entries.find(kAclPreIngressTableName);
  if (it == state.context.table_entries.end()) {
    return absl::OkStatus();
  }

  ASSIGN_OR_RETURN(
      const ir::Table *table,
      symbolic::util::GetIrTable(state.program, kAclPreIngressTableName));

  for (const auto &entry : it->second) {
    if (!entry.has_symbolic_entry()) continue;
    const ir::SymbolicTableEntry &symbolic_entry = entry.symbolic_entry();
    z3::expr_vector constraints(*state.context.z3_context);

    // Obtain symbolic variables.
    ASSIGN_OR_RETURN(auto dscp, symbolic::GetSymbolicMatch(
                                    symbolic_entry, "dscp", *table,
                                    state.program, *state.context.z3_context));
    ASSIGN_OR_RETURN(
        auto dst_ip,
        symbolic::GetSymbolicMatch(symbolic_entry, "dst_ip", *table,
                                   state.program, *state.context.z3_context));
    ASSIGN_OR_RETURN(
        auto dst_ipv6,
        symbolic::GetSymbolicMatch(symbolic_entry, "dst_ipv6", *table,
                                   state.program, *state.context.z3_context));
    ASSIGN_OR_RETURN(auto ecn, symbolic::GetSymbolicMatch(
                                   symbolic_entry, "ecn", *table, state.program,
                                   *state.context.z3_context));
    ASSIGN_OR_RETURN(
        auto in_port,
        symbolic::GetSymbolicMatch(symbolic_entry, "in_port", *table,
                                   state.program, *state.context.z3_context));
    ASSIGN_OR_RETURN(auto is_ip, symbolic::GetSymbolicMatch(
                                     symbolic_entry, "is_ip", *table,
                                     state.program, *state.context.z3_context));
    ASSIGN_OR_RETURN(
        auto is_ipv4,
        symbolic::GetSymbolicMatch(symbolic_entry, "is_ipv4", *table,
                                   state.program, *state.context.z3_context));
    ASSIGN_OR_RETURN(
        auto is_ipv6,
        symbolic::GetSymbolicMatch(symbolic_entry, "is_ipv6", *table,
                                   state.program, *state.context.z3_context));

    // dscp::mask != 0 -> (is_ip == 1 || is_ipv4 == 1 || is_ipv6 == 1);
    constraints.push_back(
        dscp.mask == 0 ||
        (is_ip.value == 1 || is_ipv4.value == 1 || is_ipv6.value == 1));
    // ecn::mask != 0 -> (is_ip == 1 || is_ipv4 == 1 || is_ipv6 == 1);
    constraints.push_back(
        ecn.mask == 0 ||
        (is_ip.value == 1 || is_ipv4.value == 1 || is_ipv6.value == 1));
    // dst_ip::mask != 0 -> is_ipv4 == 1;
    constraints.push_back(dst_ip.mask == 0 || is_ipv4.value == 1);
    // dst_ipv6::mask != 0 -> is_ipv6 == 1;
    constraints.push_back(dst_ipv6.mask == 0 || is_ipv6.value == 1);
    // is_ip::mask != 0 -> (is_ipv4::mask == 0 && is_ipv6::mask == 0);
    constraints.push_back(is_ip.mask == 0 ||
                          (is_ipv4.mask == 0 && is_ipv6.mask == 0));
    // is_ipv4::mask != 0 -> (is_ip::mask == 0 && is_ipv6::mask == 0);
    constraints.push_back(is_ipv4.mask == 0 ||
                          (is_ip.mask == 0 && is_ipv6.mask == 0));
    // is_ipv6::mask != 0 -> (is_ip::mask == 0 && is_ipv4::mask == 0);
    constraints.push_back(is_ipv6.mask == 0 ||
                          (is_ip.mask == 0 && is_ipv4.mask == 0));
    // is_ipv4::mask != 0 -> (is_ipv4 == 1);
    constraints.push_back(is_ipv4.mask == 0 || is_ipv4.value == 1);
    // is_ipv6::mask != 0 -> (is_ipv6 == 1);
    constraints.push_back(is_ipv6.mask == 0 || is_ipv6.value == 1);
    // ::priority < 0x7fffffff;
    if (int priority = symbolic_entry.sketch().priority();
        priority >= 0x7fffffff) {
      return gutil::InvalidArgumentErrorBuilder()
             << "Invalid priority '" << priority << "' for entry #"
             << symbolic_entry.index() << " in table "
             << kAclPreIngressTableName;
    }

    state.solver->add(constraints);
  }

  return absl::OkStatus();
}

absl::Status AddConstraintsForAclIngressTable(symbolic::SolverState &state) {
  constexpr absl::string_view kAclPreIngressTableName =
      "ingress.acl_ingress.acl_ingress_table";
  auto it = state.context.table_entries.find(kAclPreIngressTableName);
  if (it == state.context.table_entries.end()) {
    return absl::OkStatus();
  }

  ASSIGN_OR_RETURN(
      const ir::Table *table,
      symbolic::util::GetIrTable(state.program, kAclPreIngressTableName));

  for (const auto &entry : it->second) {
    if (!entry.has_symbolic_entry()) continue;
    const ir::SymbolicTableEntry &symbolic_entry = entry.symbolic_entry();
    z3::expr_vector constraints(*state.context.z3_context);

    // Obtain symbolic variables.
    ASSIGN_OR_RETURN(auto dscp, symbolic::GetSymbolicMatch(
                                    symbolic_entry, "dscp", *table,
                                    state.program, *state.context.z3_context));
    ASSIGN_OR_RETURN(
        auto dst_ip,
        symbolic::GetSymbolicMatch(symbolic_entry, "dst_ip", *table,
                                   state.program, *state.context.z3_context));
    ASSIGN_OR_RETURN(
        auto src_ip,
        symbolic::GetSymbolicMatch(symbolic_entry, "src_ip", *table,
                                   state.program, *state.context.z3_context));
    ASSIGN_OR_RETURN(auto ttl, symbolic::GetSymbolicMatch(
                                   symbolic_entry, "ttl", *table, state.program,
                                   *state.context.z3_context));
    ASSIGN_OR_RETURN(
        auto dst_ipv6,
        symbolic::GetSymbolicMatch(symbolic_entry, "dst_ipv6", *table,
                                   state.program, *state.context.z3_context));
    ASSIGN_OR_RETURN(
        auto src_ipv6,
        symbolic::GetSymbolicMatch(symbolic_entry, "src_ipv6", *table,
                                   state.program, *state.context.z3_context));
    ASSIGN_OR_RETURN(auto ecn, symbolic::GetSymbolicMatch(
                                   symbolic_entry, "ecn", *table, state.program,
                                   *state.context.z3_context));
    ASSIGN_OR_RETURN(auto is_ip, symbolic::GetSymbolicMatch(
                                     symbolic_entry, "is_ip", *table,
                                     state.program, *state.context.z3_context));
    ASSIGN_OR_RETURN(
        auto is_ipv4,
        symbolic::GetSymbolicMatch(symbolic_entry, "is_ipv4", *table,
                                   state.program, *state.context.z3_context));
    ASSIGN_OR_RETURN(
        auto is_ipv6,
        symbolic::GetSymbolicMatch(symbolic_entry, "is_ipv6", *table,
                                   state.program, *state.context.z3_context));
    ASSIGN_OR_RETURN(
        auto ether_type,
        symbolic::GetSymbolicMatch(symbolic_entry, "ether_type", *table,
                                   state.program, *state.context.z3_context));
    ASSIGN_OR_RETURN(
        auto ip_protocol,
        symbolic::GetSymbolicMatch(symbolic_entry, "ip_protocol", *table,
                                   state.program, *state.context.z3_context));
    ASSIGN_OR_RETURN(
        auto arp_tpa,
        symbolic::GetSymbolicMatch(symbolic_entry, "arp_tpa", *table,
                                   state.program, *state.context.z3_context));
    ASSIGN_OR_RETURN(
        auto l4_src_port,
        symbolic::GetSymbolicMatch(symbolic_entry, "l4_src_port", *table,
                                   state.program, *state.context.z3_context));
    ASSIGN_OR_RETURN(
        auto l4_dst_port,
        symbolic::GetSymbolicMatch(symbolic_entry, "l4_dst_port", *table,
                                   state.program, *state.context.z3_context));
    ASSIGN_OR_RETURN(
        auto icmpv6_type,
        symbolic::GetSymbolicMatch(symbolic_entry, "icmpv6_type", *table,
                                   state.program, *state.context.z3_context));
    ASSIGN_OR_RETURN(
        auto psp_next_header,
        symbolic::GetSymbolicMatch(symbolic_entry, "psp_next_header", *table,
                                   state.program, *state.context.z3_context));
    ASSIGN_OR_RETURN(
        auto psp_info,
        symbolic::GetSymbolicMatch(symbolic_entry, "psp_info", *table,
                                   state.program, *state.context.z3_context));
    ASSIGN_OR_RETURN(
        auto inner_psp_udp_dst,
        symbolic::GetSymbolicMatch(symbolic_entry, "inner_psp_udp_dst", *table,
                                   state.program, *state.context.z3_context));

    // Forbid using ether_type for IP packets (by convention, use is_ip*
    // instead).
    // ether_type != 0x0800 && ether_type != 0x86dd;
    constraints.push_back(ether_type.mask == 0 || (ether_type.value == 0x0800 &&
                                                   ether_type.value == 0x86dd));

    // Only allow IP field matches for IP packets.
    // dst_ip::mask != 0 -> is_ipv4 == 1;
    constraints.push_back(dst_ip.mask == 0 || is_ipv4.value == 1);

    // "src_ip::mask != 0 -> is_ipv4 == 1;
    constraints.push_back(src_ip.mask == 0 || is_ipv4.value == 1);

    // "dst_ipv6::mask != 0 -> is_ipv6 == 1;
    constraints.push_back(dst_ipv6.mask == 0 || is_ipv6.value == 1);

    // src_ipv6::mask != 0 -> is_ipv6 == 1;
    constraints.push_back(src_ipv6.mask == 0 || is_ipv6.value == 1);

    // ttl::mask != 0 -> (is_ip == 1 || is_ipv4 == 1 || is_ipv6 == 1);
    constraints.push_back(
        ttl.mask == 0 ||
        (is_ip.value == 1 || is_ipv4.value == 1 || is_ipv6.value == 1));

    // dscp::mask != 0 -> (is_ip == 1 || is_ipv4 == 1 || is_ipv6 == 1);
    constraints.push_back(
        dscp.mask == 0 ||
        (is_ip.value == 1 || is_ipv4.value == 1 || is_ipv6.value == 1));

    // ip_protocol::mask != 0 -> (is_ip == 1 || is_ipv4 == 1 || is_ipv6 == 1);
    constraints.push_back(
        ip_protocol.mask == 0 ||
        (is_ip.value == 1 || is_ipv4.value == 1 || is_ipv6.value == 1));

    // Only allow l4_dst_port and l4_src_port matches for TCP/UDP packets.
    // l4_src_port::mask != 0 -> (ip_protocol == 6 || ip_protocol== 17);
    constraints.push_back(l4_src_port.mask == 0 ||
                          (ip_protocol.value == 6 || ip_protocol.value == 17));
    // l4_dst_port::mask != 0 -> (ip_protocol == 6 || ip_protocol == 17);
    constraints.push_back(l4_dst_port.mask == 0 ||
                          (ip_protocol.value == 6 || ip_protocol.value == 17));

    // Only allow arp_tpa matches for ARP packets.
    // arp_tpa::mask != 0 -> ether_type == 0x0806;
    constraints.push_back(arp_tpa.mask == 0 || ether_type.value == 0x0806);

    // icmpv6_type::mask != 0 -> ip_protocol == 58;
    constraints.push_back(icmpv6_type.mask == 0 || ip_protocol.value == 58);

    // psp_next_header::mask != 0 -> (ip_protocol == 17 && l4_dst_port == 1000);
    constraints.push_back(
        z3::implies(psp_next_header.mask != 0,
                    (ip_protocol.value == 17 && l4_dst_port.value == 1000)));

    // psp_info::mask != 0 -> (ip_protocol == 17 && l4_dst_port == 1000);
    constraints.push_back(
        z3::implies(psp_info.mask != 0,
                    (ip_protocol.value == 17 && l4_dst_port.value == 1000)));

    // inner_psp_udp_dst::mask != 0 -> (psp_next_header == 17);
    constraints.push_back(
        z3::implies(inner_psp_udp_dst.mask != 0, psp_next_header.value == 17));

    // Forbid illegal combinations of IP_TYPE fields.
    // is_ip::mask != 0 -> (is_ipv4::mask == 0 && is_ipv6::mask == 0);
    constraints.push_back(is_ip.mask == 0 ||
                          (is_ipv4.mask == 0 && is_ipv6.mask == 0));
    // is_ipv4::mask != 0 -> (is_ip::mask == 0 && is_ipv6::mask == 0);
    constraints.push_back(is_ipv4.mask == 0 ||
                          (is_ip.mask == 0 && is_ipv6.mask == 0));
    // is_ipv6::mask != 0 -> (is_ip::mask == 0 && is_ipv4::mask == 0);
    constraints.push_back(is_ipv6.mask == 0 ||
                          (is_ip.mask == 0 && is_ipv4.mask == 0));

    // Forbid unsupported combinations of IP_TYPE fields.
    // is_ipv4::mask != 0 -> (is_ipv4 == 1);
    constraints.push_back(is_ipv4.mask == 0 || is_ipv4.value == 1);
    // is_ipv6::mask != 0 -> (is_ipv6 == 1);
    constraints.push_back(is_ipv6.mask == 0 || is_ipv6.value == 1);

    state.solver->add(constraints);
  }

  return absl::OkStatus();
}

absl::Status AddConstraintsPreventingIngressPortBeingInLoopbackMode(
    symbolic::SolverState &state) {
  constexpr absl::string_view kEgressPortLoopbackTableName =
      "egress.egress_port_loopback.egress_port_loopback_table";
  ASSIGN_OR_RETURN(const ir::Table *loopback_table,
                   gutil::FindPtrOrStatus(state.program.tables(),
                                          kEgressPortLoopbackTableName));

  // Get field definitions.
  constexpr absl::string_view kOutPortMatchFieldName = "out_port";
  ASSIGN_OR_RETURN(
      const pdpi::IrMatchFieldDefinition *out_port_match_field_def,
      gutil::FindPtrOrStatus(
          loopback_table->table_definition().match_fields_by_name(),
          kOutPortMatchFieldName));
  ASSIGN_OR_RETURN(
      const p4_symbolic::ir::FieldValue
          *standard_metadata_egress_port_header_field,
      gutil::FindPtrOrStatus(
          loopback_table->table_implementation().match_name_to_field(),
          kOutPortMatchFieldName));
  const std::string standard_metadata_egress_port_header_field_name =
      absl::StrFormat("%s.%s",
                      standard_metadata_egress_port_header_field->header_name(),
                      standard_metadata_egress_port_header_field->field_name());
  // Sanity check.
  if (standard_metadata_egress_port_header_field_name !=
      "standard_metadata.egress_port") {
    return gutil::FailedPreconditionErrorBuilder()
           << "Expected '" << kOutPortMatchFieldName << "' in '"
           << kEgressPortLoopbackTableName << "' match on header name "
           << "'standard_metadata.egress_port' but got '"
           << standard_metadata_egress_port_header_field_name << "'";
  }

  const std::vector<ir::TableEntry> *table_entries = gutil::FindOrNull(
      state.context.table_entries, kEgressPortLoopbackTableName);
  if (table_entries == nullptr) {
    // This is ok because the table may be empty.
    return absl::OkStatus();
  }
  // For each match on out_port `p`, add a constraint: ingress_port != `p`.
  for (const ir::TableEntry &entry : *table_entries) {
    if (!entry.has_concrete_entry()) {
      return absl::UnimplementedError(
          "Adding constraints preventing ingress port being in loopback mode "
          "is not supported for non-concrete entries in loopback table.");
    } else {
      // Sanity check: ensure the entry contains only (exact) match on
      // egress port.
      const auto &matches =
          entry.concrete_entry().pdpi_ir_entity().table_entry().matches();
      if (matches.size() != 1 ||
          matches.at(0).name() != kOutPortMatchFieldName ||
          !matches.at(0).has_exact()) {
        return gutil::FailedPreconditionErrorBuilder()
               << "expected one exact match on egress_port in "
                  "egress_port_loopback_table_entry, got "
               << entry.concrete_entry().DebugString();
      }

      // Get the port.
      ASSIGN_OR_RETURN(
          z3::expr loopback_port,
          symbolic::values::FormatP4RTValue(
              matches.at(0).exact(),
              standard_metadata_egress_port_header_field_name,
              out_port_match_field_def->match_field().type_name().name(),
              out_port_match_field_def->match_field().bitwidth(),
              *state.context.z3_context, state.translator));

      // Add Z3 constraint.
      ASSIGN_OR_RETURN(
          z3::expr constraint,
          symbolic::operators::Neq(state.context.ingress_port, loopback_port));
      state.solver->add(constraint);
    }
  }

  return absl::OkStatus();
}

}  // namespace p4_symbolic
