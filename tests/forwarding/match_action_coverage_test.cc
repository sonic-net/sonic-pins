#include "tests/forwarding/match_action_coverage_test.h"

#include <algorithm>
#include <functional>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "absl/container/flat_hash_set.h"
#include "absl/random/random.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/strings/strip.h"
#include "absl/strings/substitute.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/collections.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/version.h"
#include "lib/gnmi/gnmi_helper.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_constraints/backend/constraint_info.h"
#include "p4_constraints/backend/symbolic_interpreter.h"
#include "p4_fuzzer/fuzz_util.h"
#include "p4_fuzzer/fuzzer_config.h"
#include "p4_fuzzer/switch_state.h"
#include "p4_infra/p4_pdpi/built_ins.h"
#include "p4_infra/p4_pdpi/ir.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/ir_properties.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "p4_infra/p4_pdpi/string_encodings/hex_string.h"
#include "sai_p4/fixed/ids.h"
#include "sai_p4/instantiations/google/versions.h"
#include "tests/lib/switch_test_setup_helpers.h"
#include "thinkit/mirror_testbed.h"
#include "thinkit/test_environment.h"

namespace p4_fuzzer {
namespace {

using ::p4::v1::Entity;
using ::p4::v1::TableEntry;
using ::p4::v1::Update;
using ::pdpi::GetMulticastGroupTableName;

using EntityPredicate = std::function<bool(const Entity&)>;

// TODO: Factor all of this logic out of this test and into the
// base fuzzer, parameterizing the test on these names instead.
// Used to mask bugs where omitting a match causes issues. This function returns
// a set of fully qualified names of omittable match fields in the P4Info. These
// match fields will be treated as required instead.
absl::flat_hash_set<std::string> GetRequiredFullyQualifiedNames() {
  static const absl::flat_hash_set<std::string> required_fully_qualified_names =
      {};
  return required_fully_qualified_names;
}

bool IsRequiredDueToBug(
    const pdpi::IrTableDefinition& table_definition,
    const pdpi::IrMatchFieldDefinition& match_field_definition) {
  const std::string fully_qualified_match_field =
      absl::StrCat(table_definition.preamble().name(), ".",
                   match_field_definition.match_field().name());
  return GetRequiredFullyQualifiedNames().contains(fully_qualified_match_field);
}

bool EntryUsesMatchField(
    const TableEntry& entry,
    const pdpi::IrMatchFieldDefinition& match_field_definition) {
  for (const auto& match : entry.match()) {
    if (match.field_id() == match_field_definition.match_field().id()) {
      return true;
    }
  }
  return false;
}

bool EntryUsesAction(const TableEntry& entry,
                     const pdpi::IrActionReference& action_reference) {
  if (entry.action().has_action()) {
    return entry.action().action().action_id() ==
           action_reference.action().preamble().id();
  }
  if (entry.action().has_action_profile_action_set()) {
    for (const auto& action :
         entry.action().action_profile_action_set().action_profile_actions()) {
      if (action.action().action_id() ==
          action_reference.action().preamble().id()) {
        return true;
      }
    }
  }
  return false;
}

// Returns the route metadata as an int if it's present in the entry and nullopt
// otherwise.
absl::StatusOr<std::optional<int>> ExtractRouteMetadataAsIntFromEntry(
    const pdpi::IrTableEntry& ir_entry) {
  if (ir_entry.table_name() == "ipv4_table" ||
      ir_entry.table_name() == "ipv6_table") {
    for (const auto& param : ir_entry.action().params()) {
      if (param.name() == "route_metadata") {
        RET_CHECK(param.value().has_hex_str())
            << "Route metadata expected to be hex string, but got parameter: "
            << param.DebugString();
        return pdpi::HexStringToInt(param.value().hex_str());
      }
    }
  }
  return std::nullopt;
}

// Used to mask bugs that affect specific entries, but not every entry of a
// particular table, with a particular match field, or with a particular action.
// Such bugs should be masked using the FuzzerConfig's
// `disabled_fully_qualified_names`.
absl::StatusOr<bool> EntityTriggersKnownBug(const pdpi::IrP4Info& info,
                                            const Entity& entity,
                                            const SwitchState& state) {
  // Convert the entry to IR to simplify logic.
  ASSIGN_OR_RETURN(pdpi::IrEntity ir_entity, pdpi::PiEntityToIr(info, entity));

  ASSIGN_OR_RETURN(std::optional<int> route_metadata,
                   ExtractRouteMetadataAsIntFromEntry(ir_entity.table_entry()));
  // Route metadata values between 56 and 63 are reserved for internal switch
  // operations.
  // TODO: This should be handled by P4 Constraints.
  if (route_metadata.has_value() && *route_metadata >= 56) {
    return true;
  }

  // Remove once tunnel encap entries can refer to RIFs with
  // Condition on NON-DELETE once we cover deletion.
  // Empty multicast group entries are not supported by the switch.
  if (ir_entity.packet_replication_engine_entry().has_multicast_group_entry() &&
      ir_entity.packet_replication_engine_entry()
          .multicast_group_entry()
          .replicas()
          .empty()) {
    return true;
  }

  // Remove once tunnel encap entries can refer to RIFs with
  // the `unicast_set_port_and_src_mac_and_vlan_id` action.
  if (entity.table_entry().table_id() == ROUTING_TUNNEL_TABLE_ID &&
      entity.table_entry().action().action().action_id() ==
          ROUTING_MARK_FOR_P2P_TUNNEL_ENCAP_ACTION_ID) {
    std::string referenced_rif;
    for (const auto& param : ir_entity.table_entry().action().params()) {
      if (param.name() == "router_interface_id") {
        referenced_rif = param.value().str();
        break;
      }
    }

    // Search for referenced RIF entry.
    p4::v1::TableEntry rif_entry_key_only;
    rif_entry_key_only.set_table_id(ROUTING_ROUTER_INTERFACE_TABLE_ID);
    p4::v1::FieldMatch& rif_field = *rif_entry_key_only.add_match();
    // Field ID 1 is `router_interface_id` and the only match field.
    rif_field.set_field_id(1);
    rif_field.mutable_exact()->set_value(referenced_rif);
    std::optional<p4::v1::TableEntry> stored_rif_entry =
        state.GetTableEntry(rif_entry_key_only);

    if (!stored_rif_entry.has_value()) {
      return gutil::InvalidArgumentErrorBuilder()
             << "Tunnel encap entry refers to RIF that does not exist. Entry: "
             << gutil::PrintTextProto(ir_entity.table_entry());
    }

    // tunnel encap entries cannot refer to RIFs with
    // the `unicast_set_port_and_src_mac_and_vlan_id` action.
    if (stored_rif_entry->action().action().action_id() ==
	ROUTING_UNICAST_SET_PORT_AND_SRC_MAC_AND_VLAN_ID_ACTION_ID)
      return true;
  }
  return false;
}

absl::Status ModifyEntityToAvoidKnownBug(const pdpi::IrP4Info& info,
                                         Entity& entity) {
  // Convert the entry to IR to simplify logic.
  ASSIGN_OR_RETURN(pdpi::IrEntity ir_entity, pdpi::PiEntityToIr(info, entity));

  // TODO: Remove once this is covered by P4 Constraints.
  if (ir_entity.table_entry().table_name() == "l3_admit_table") {
    ir_entity.mutable_table_entry()->set_priority(1);
  }

  // TODO: Remove when the old version is out of use.
  if (ir_entity.table_entry().has_action_set() &&
      ir_entity.table_entry().action_set().actions_size() > 1) {
    // If the version does not support duplicate WCMP members, then remove all
    // members except the first one.
    ASSIGN_OR_RETURN(gutil::Version p4info_version,
                     gutil::ParseVersion(info.pkg_info().version()));
    if (p4info_version <
        *gutil::ParseVersion(
            SAI_P4_PKGINFO_VERSION_HAS_DUPLICATE_WCMP_MEMBER_SUPPORT)) {
      auto action = std::move(ir_entity.table_entry().action_set().actions(0));
      ir_entity.mutable_table_entry()->mutable_action_set()->clear_actions();
      *ir_entity.mutable_table_entry()->mutable_action_set()->add_actions() =
          std::move(action);
    }
  }

  ASSIGN_OR_RETURN(entity, pdpi::IrEntityToPi(info, ir_entity));
  return absl::OkStatus();
}

absl::Status ModifyDeleteAndReinstallEntity(
    const FuzzerConfig& config, const SwitchState& state,
    const Entity& initial_entity, bool skip_modify, bool mask_known_failures,
    absl::BitGen& gen, pdpi::P4RuntimeSession& session) {
  p4::v1::Update update;
  update.set_type(p4::v1::Update::MODIFY);
  *update.mutable_entity() = initial_entity;
  pdpi::IrEntity entity_to_modify_to;

  if (!skip_modify) {
    const absl::Time kDeadline = absl::Now() + absl::Seconds(10);
    bool entry_triggers_known_bug = false;
    do {
      RETURN_IF_ERROR(p4_fuzzer::ModifyEntity(&gen, config, state,
                                              *update.mutable_entity()));
      if (mask_known_failures) {
        RETURN_IF_ERROR(ModifyEntityToAvoidKnownBug(config.GetIrP4Info(),
                                                    *update.mutable_entity()));
      }
      ASSIGN_OR_RETURN(
          entry_triggers_known_bug,
          EntityTriggersKnownBug(config.GetIrP4Info(), update.entity(), state));
    } while (mask_known_failures && entry_triggers_known_bug &&
             absl::Now() < kDeadline);
    // If we timeout, we return an error.
    if (mask_known_failures && entry_triggers_known_bug) {
      return gutil::DeadlineExceededErrorBuilder()
             << "failed to generate a modification within 10s that doesn't "
                "trigger a known bug for entity: "
             << initial_entity.DebugString();
    }

    // Perform the modification if it was correctly generated.
    ASSIGN_OR_RETURN(entity_to_modify_to,
                     pdpi::PiEntityToIr(config.GetIrP4Info(), update.entity()));
    RETURN_IF_ERROR(pdpi::SendPiUpdates(&session, {update}))
        << "during modification from original entity to new entity:\n"
        << entity_to_modify_to.DebugString();
  }

  if (!skip_modify) {
    *update.mutable_entity() = initial_entity;
    RETURN_IF_ERROR(pdpi::SendPiUpdates(&session, {update}))
        << "during modification back to original entity from new entity:\n"
        << entity_to_modify_to.DebugString();
  }
  return absl::OkStatus();
}

// Generates valid entries for `table` until one meets the given
// `predicate`. Unless an entry with the same keys already exists on the switch,
// installs the generated entry and updates `state`.
// installs the generated entry and updates `state`. `custom_constraint` must be
// a valid P4-Constraints string representing an additional constraint enforced
// on the generated entry, if empty, no additional constraint is enforced.
absl::Status GenerateAndInstallEntryThatMeetsPredicate(
    absl::BitGen& gen, pdpi::P4RuntimeSession& session,
    const FuzzerConfig& config, SwitchState& state,
    thinkit::TestEnvironment& environment, absl::string_view table_name,
    const EntityPredicate& predicate,
    std::optional<absl::string_view> custom_constraint = std::nullopt) {
  Entity entity;
  // As of now, we only support p4 defined tables or the multicast group table.
  // This means that an empty optional also signals that we have the multicast
  // group table.
  std::optional<pdpi::IrTableDefinition> p4_table_def = std::nullopt;
  if (table_name != GetMulticastGroupTableName()) {
    ASSIGN_OR_RETURN(
        p4_table_def,
        gutil::FindOrStatus(config.GetIrP4Info().tables_by_name(), table_name));
  }
  // Generate new entries until we satisfy our predicates or do not trigger
  // known bugs (if we are masking known failures). Continue trying for at most
  // 10 seconds.
  const absl::Time kDeadline = absl::Now() + absl::Seconds(10);
  bool entry_triggers_known_bug = false;
  bool mask_known_failures = environment.MaskKnownFailures();
  do {
    if (p4_table_def.has_value()) {
      ASSIGN_OR_RETURN(*entity.mutable_table_entry(),
                       FuzzValidTableEntry(&gen, config, state, *p4_table_def,
                                           custom_constraint));

    } else {
      ASSIGN_OR_RETURN(*entity.mutable_packet_replication_engine_entry()
                            ->mutable_multicast_group_entry(),
                       FuzzValidMulticastGroupEntry(&gen, config, state));
    }
    if (mask_known_failures) {
      RETURN_IF_ERROR(
          ModifyEntityToAvoidKnownBug(config.GetIrP4Info(), entity));
    }
    ASSIGN_OR_RETURN(
        entry_triggers_known_bug,
        EntityTriggersKnownBug(config.GetIrP4Info(), entity, state));
  } while ((!predicate(entity) ||
            (mask_known_failures && entry_triggers_known_bug)) &&
           absl::Now() < kDeadline);
  // If we timeout, we return an error.
  if (!predicate(entity) || (mask_known_failures && entry_triggers_known_bug)) {
    return gutil::DeadlineExceededErrorBuilder() << absl::Substitute(
               "failed to generate an entry meeting the given predicate and "
               "doesn't trigger a known bug for table '$0' within 10s",
               table_name);
  }

  // If the generated entry is identical to one we already have installed,
  // then we return early since we have already covered the predicate.
  if (state.GetEntity(entity).has_value()) {
    return absl::OkStatus();
  }

  ASSIGN_OR_RETURN(pdpi::IrEntity ir_entity,
                   pdpi::PiEntityToIr(config.GetIrP4Info(), entity));
  RETURN_IF_ERROR(environment.AppendToTestArtifact(
      "install_requests_and_responses.txt",
      absl::StrCat("# IR Entity:\n", ir_entity.DebugString())));

  if (absl::Status status = pdpi::InstallPiEntity(&session, entity);
      status.ok()) {
    RETURN_IF_ERROR(environment.AppendToTestArtifact(
        "install_requests_and_responses.txt", "# Successfully installed!\n"));
  } else {
    RETURN_IF_ERROR(environment.AppendToTestArtifact(
        "install_requests_and_responses.txt",
        absl::StrCat("# Installation failed:\n", status.ToString())));
    RETURN_IF_ERROR(status) << "IR entity:\n" << ir_entity.DebugString();
  }

  // Don't modify non-modifiable tables.
  absl::string_view fully_qualified_table_name =
      p4_table_def.has_value() ? p4_table_def->preamble().name() : table_name;
  bool skip_modify =
      config.GetNonModifiableTables().contains(fully_qualified_table_name);
  // Test if modification and deletion works as expected for this entity.
  RETURN_IF_ERROR(ModifyDeleteAndReinstallEntity(
      config, state, entity, skip_modify, mask_known_failures, gen, session))
      << absl::StrCat("When attempting to ", skip_modify ? "" : "modify, then ",
                      "delete and reinstall IR entity:\n", ir_entity);

  // Update state.
  Update update;
  update.set_type(Update::INSERT);
  *update.mutable_entity() = entity;
  return state.ApplyUpdate(update);
}

// Remove function once built-in multicast group table can
// be treated like any other table.
// Installs a multicast group entry with and without replicas.
absl::Status AddMulticastGroupEntryWithAndWithoutReplicas(
    absl::BitGen& gen, pdpi::P4RuntimeSession& session,
    const FuzzerConfig& config, SwitchState& state,
    thinkit::TestEnvironment& environment,
    const p4::config::v1::P4Info& p4info) {
  LOG(INFO) << "INSTALLING ENTRIES INTO BUILT-IN MULTICAST GROUP TABLE";

  // Ensure both a L2 and L3 multicast entry are
  // installed. L2 groups are currently disabled, so all groups are L3.
  RETURN_IF_ERROR(GenerateAndInstallEntryThatMeetsPredicate(
                      gen, session, config, state, environment,
                      GetMulticastGroupTableName(),
                      /*predicate=*/
                      [&](const Entity& entity) { return true; }))
          .SetPrepend()
      << "while generating entry for '" << GetMulticastGroupTableName()
      << "': ";
  LOG(INFO) << absl::Substitute("   -  With $0: Present",
                                pdpi::GetReplicaActionName());

  // Uncomment once empty multicast groups are supported.
  // RETURN_IF_ERROR(GenerateAndInstallEntryThatMeetsPredicate(
  //                     gen, session, config, state, environment,
  //                     GetMulticastGroupTableName(),
  //                     /*predicate=*/
  //                     [&](const Entity& entity) {
  //                       // Checks that the multicast entry has no replicas.
  //                       return entity.packet_replication_engine_entry()
  //                                  .has_multicast_group_entry() &&
  //                              entity.packet_replication_engine_entry()
  //                                  .multicast_group_entry()
  //                                  .replicas()
  //                                  .empty();
  //                     }))
  //         .SetPrepend()
  //     << "while generating entry for '" << GetMulticastGroupTableName()
  //     << "': ";
  // LOG(INFO) << absl::Substitute("   -  With $0: Absent",
  //                               pdpi::GetReplicaActionName());
  return absl::OkStatus();
}

// Returns a P4-constraints string enforcing that `field` be omitted or present
// depending on the value of `omit`. If the field is not omittable, returns
// InvalidArgumentError.

absl::StatusOr<std::string> FieldPresenceConstraintString(
    const pdpi::IrMatchFieldDefinition& field, bool present) {
  std::string op = present ? "!=" : "==";
  switch (field.match_field().match_type()) {
    case p4::config::v1::MatchField::TERNARY:
    case p4::config::v1::MatchField::OPTIONAL:
      return absl::Substitute("$0::mask $1 0", field.match_field().name(), op);
    case p4::config::v1::MatchField::LPM:
      return absl::Substitute("$0::prefix_length $1 0",
                              field.match_field().name(), op);
    default:
      return absl::InvalidArgumentError(
          absl::Substitute("Match type '$0' is not omittable",
                           p4::config::v1::MatchField::MatchType_Name(
                               field.match_field().match_type())));
  }
}

// For each programmable table, installs a set of table entries covering all
// match fields and actions in the following sense:
// - Each omittable match field is omitted and included in at least one table
//   entry.
// - Each action is included in at least one table entry.
// Tables are installed in the order of their dependency rank so that all
// references can be satisfied. In other words, if Table A refers to Table B,
// then Table B will be installed first.
// Remove p4info param and use config to get P4Info.
absl::Status AddTableEntryForEachMatchAndEachAction(
    absl::BitGen& gen, pdpi::P4RuntimeSession& session,
    const FuzzerConfig& config, SwitchState& state,
    thinkit::TestEnvironment& environment,
    const p4::config::v1::P4Info& p4info) {
  ASSIGN_OR_RETURN(const p4_constraints::ConstraintInfo constraints_by_table_id,
                   p4_constraints::P4ToConstraintInfo(p4info));

  // Order tables so that tables being referenced have valid entries.
  std::vector<std::string> table_names_by_dependency_rank;
  for (const auto& table_def : AllValidTablesForP4RtRole(config)) {
    table_names_by_dependency_rank.push_back(table_def.preamble().alias());
  }

  // Remove once built-in tables can be treated like any
  // other table.
  // Add built-in tables that are not disabled.
  for (const auto& [name, unused] : config.GetIrP4Info().built_in_tables()) {
    if (!config.GetDisabledFullyQualifiedNames().contains(name)) {
      table_names_by_dependency_rank.push_back(name);
    }
  }

  // Move function to sequencing library.
  std::sort(
      table_names_by_dependency_rank.begin(),
      table_names_by_dependency_rank.end(),
      [&](absl::string_view a, absl::string_view b) -> bool {
        int rank_a = config.GetIrP4Info().dependency_rank_by_table_name().at(a);
        int rank_b = config.GetIrP4Info().dependency_rank_by_table_name().at(b);
        // If the ranks are the same, sort alphabetically. Otherwise,
        // larger rank (i.e. table w/ smaller dependency chain) comes first.
        return rank_a == rank_b ? a < b : rank_a > rank_b;
      });

  for (absl::string_view table_name : table_names_by_dependency_rank) {
    // Built-in multicast group table is handled separately.
    if (table_name == GetMulticastGroupTableName()) {
      RETURN_IF_ERROR(AddMulticastGroupEntryWithAndWithoutReplicas(
          gen, session, config, state, environment, p4info));
      continue;
    }

    ASSIGN_OR_RETURN(
        const pdpi::IrTableDefinition& table,
        gutil::FindOrStatus(config.GetIrP4Info().tables_by_name(), table_name));
    LOG(INFO) << absl::Substitute("For table '$0', installing entries with:",
                                  table.preamble().alias());
    std::vector<std::string> required_match_descriptions;
    std::vector<std::string> omittable_match_descriptions;
    // For each valid match field, install a table entry with (and without
    // if possible) that field.
    for (const pdpi::IrMatchFieldDefinition& field :
         AllValidMatchFields(config, table)) {
      if (!pdpi::IsOmittable(field) || (environment.MaskKnownFailures() &&
                                        IsRequiredDueToBug(table, field))) {
        // If the field can't be a wildcard, then any value will do:
        RETURN_IF_ERROR(GenerateAndInstallEntryThatMeetsPredicate(
                            gen, session, config, state, environment,
                            table.preamble().alias(),
                            /*predicate=*/[](auto&) { return true; }))
                .SetPrepend()
            << absl::Substitute("while generating entry with field $0: ",
                                field.match_field().name());
        required_match_descriptions.push_back(
            absl::Substitute("   -   $0: Present", field.match_field().name()));
      } else {
        // If the field can be a wildcard, install one entry with a wildcard and
        // one without.
        for (bool use_field : {true, false}) {
          std::optional<std::string> additional_constraint;
          // Remove conditional if statement.
          if (!pdpi::HasP4RuntimeTranslatedType(field)) {
            ASSIGN_OR_RETURN(additional_constraint,
                             FieldPresenceConstraintString(field, use_field));
            auto* table_info = p4_constraints::GetTableInfoOrNull(
                constraints_by_table_id, table.preamble().id());
            if (table_info == nullptr) {
              return gutil::InternalErrorBuilder()
                     << "Table info not present for id "
                     << table.preamble().id();
            }
            // TODO: Support P4RT translated types.
            auto skip_key =
                [&](absl::string_view key_name) -> absl::StatusOr<bool> {
              return pdpi::HasP4RuntimeTranslatedType(
                  table.match_fields_by_name().at(key_name));
            };

            ASSIGN_OR_RETURN(p4_constraints::ConstraintSolver solver,
                             p4_constraints::ConstraintSolver::Create(
                                 *table_info, skip_key));
            ASSIGN_OR_RETURN(bool is_sat,
                             solver.AddConstraint(*additional_constraint));

            // If appending the additional constraint makes the constraint
            // unsatisfiable, then we cannot enforce this field presence.
            // Add parameter that fails test if unsat.
            if (!is_sat) {
              LOG(INFO) << "Forcing match field" << field.match_field().name()
                        << " to be " << (use_field ? "present" : "absent")
                        << " for entry in table" << table.preamble().alias()
                        << " is not possible due to being unsatisfiable with"
                           " existing table constraints.";
              continue;
            };
          }
          RETURN_IF_ERROR(GenerateAndInstallEntryThatMeetsPredicate(
                              gen, session, config, state, environment,
                              table.preamble().alias(),
                              /*predicate=*/
                              [&](const Entity& entity) {
                                return use_field ==
                                       EntryUsesMatchField(entity.table_entry(),
                                                           field);
                              },
                              additional_constraint))
                  .SetPrepend()
              << absl::Substitute("while generating entry $0 field $1: ",
                                  (use_field ? "with" : "without"),
                                  field.match_field().name());
        }
        omittable_match_descriptions.push_back(absl::Substitute(
            "   -   $0: Present and Absent", field.match_field().name()));
      }
    }

    // Log whether we hit the match fields in the table.
    if (!required_match_descriptions.empty()) {
      LOG(INFO) << "-  Required match fields:";
      for (const std::string& description : required_match_descriptions) {
        LOG(INFO) << description;
      }
    }

    // Only omittable match fields can be disabled.
    bool has_a_disabled_fully_qualified_name = false;
    for (const std::string& path : config.GetDisabledFullyQualifiedNames()) {
      has_a_disabled_fully_qualified_name =
          has_a_disabled_fully_qualified_name ||
          absl::StartsWith(path, table.preamble().name());
    }
    if (!omittable_match_descriptions.empty() ||
        has_a_disabled_fully_qualified_name) {
      LOG(INFO) << "-  Omittable match fields:";
      for (const std::string& description : omittable_match_descriptions) {
        LOG(INFO) << description;
      }
      for (const std::string& path : config.GetDisabledFullyQualifiedNames()) {
        if (absl::StartsWith(path, table.preamble().name())) {
          LOG(INFO) << absl::Substitute(
              "   -  $0: Absent due to being disabled",
              absl::StripPrefix(path, table.preamble().name()));
        }
      }
      if (environment.MaskKnownFailures()) {
        for (const std::string& path : GetRequiredFullyQualifiedNames()) {
          if (absl::StartsWith(path, table.preamble().name())) {
            LOG(INFO) << absl::Substitute(
                "   -  $0: Required due to bug",
                absl::StripPrefix(path, table.preamble().name()));
          }
        }
      }
    }

    // For each valid action, install a table entry using it.
    LOG(INFO) << "-  Actions:";
    for (const pdpi::IrActionReference& action_reference :
         AllValidActions(config, table)) {
      RETURN_IF_ERROR(GenerateAndInstallEntryThatMeetsPredicate(
                          gen, session, config, state, environment,
                          table.preamble().alias(),
                          /*predicate=*/
                          [&](const Entity& entity) {
                            return EntryUsesAction(entity.table_entry(),
                                                   action_reference);
                          }))
              .SetPrepend()
          << absl::Substitute("while generating entry with action $0: ",
                              action_reference.action().preamble().alias());
      LOG(INFO) << absl::Substitute(
          "   -  $0: Present", action_reference.action().preamble().alias());
    }
    // Print disabled actions.
    for (const pdpi::IrActionReference& action_reference :
         table.entry_actions()) {
      if (IsDisabledForFuzzing(config,
                               action_reference.action().preamble().name())) {
        LOG(INFO) << absl::Substitute(
            "   -  $0: Absent due to being disabled",
            action_reference.action().preamble().alias());
      }
    }
  }

  // Print disabled tables.
  for (const auto& [name, table] : config.GetIrP4Info().tables_by_name()) {
    if (IsDisabledForFuzzing(config, table.preamble().name())) {
      LOG(INFO) << absl::Substitute(
          "No entries installed into table '$0' because it was disabled.",
          table.preamble().alias());
    }
  }
  return absl::OkStatus();
}

TEST_P(MatchActionCoverageTestFixture,
       InsertEntriesForEveryTableAndMatchConfiguration) {
  thinkit::MirrorTestbed& testbed =
      GetParam().testbed_interface->GetMirrorTestbed();

  // Initialize the connection and clear table entries for the SUT.
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<pdpi::P4RuntimeSession> p4rt_session,
      pins_test::ConfigureSwitchAndReturnP4RuntimeSession(
          testbed.Sut(), /*gnmi_config=*/std::nullopt, GetParam().p4info));

  absl::BitGen gen;

  FuzzerConfig config = GetParam().config;
  // If the ports in the FuzzerConfig are unset, get all valid ports from the
  // switch via gNMI.
  if (config.GetPorts().empty()) {
    ASSERT_OK_AND_ASSIGN(auto stub, testbed.Sut().CreateGnmiStub());
    ASSERT_OK_AND_ASSIGN(auto ports,
                         pins_test::GetMatchingP4rtPortIds(
                             *stub, pins_test::IsEnabledEthernetInterface));
    config.SetPorts(std::move(ports));
  }

  ASSERT_FALSE(config.GetPorts().empty())
      << "ports must be specified in the gNMI config pushed to the switch, but "
         "none were";

  // For this test, mutations are undesirable.
  config.SetMutateUpdateProbability(0);

  SwitchState state(config.GetIrP4Info());

  // Generates and installs entries that use every match field and action.
  EXPECT_OK(AddTableEntryForEachMatchAndEachAction(gen, *p4rt_session, config,
                                                   state, testbed.Environment(),
                                                   GetParam().p4info));
}

}  // namespace
}  // namespace p4_fuzzer
