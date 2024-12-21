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
#ifndef PINS_INFRA_P4_FUZZER_FUZZER_CONFIG_H_
#define PINS_INFRA_P4_FUZZER_FUZZER_CONFIG_H_

#include <functional>
#include <optional>
#include <string>
#include <vector>

#include "absl/container/btree_set.h"
#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "lib/p4rt/p4rt_port.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_constraints/backend/constraint_info.h"
#include "p4_pdpi/ir.pb.h"

namespace p4_fuzzer {

struct ConfigParams {
  // -- Required ---------------------------------------------------------------
  // NOTE: These values are required for correct function. All of them are
  // initialized to values that should usually work for GPINs switches.
  // ---------------------------------------------------------------------------
  // The set of valid port names. 1 tends to be mapped on most GPINs switches.
  std::vector<pins_test::P4rtPortId> ports =
      pins_test::P4rtPortId::MakeVectorFromOpenConfigEncodings({1});
  // The set of valid QOS queues. CONTROLLER_PRIORITY_5 tends to be mapped on
  // most GPINs switches.
  std::vector<std::string> qos_queues = {"CONTROLLER_PRIORITY_5"};
  // The P4RT role the fuzzer should use.
  std::string role = "sdn_controller";
  // The probability of performing a mutation on a given table entry.
  float mutate_update_probability = 0.1;
  // The probability of fuzzing a multicast group entry when fuzzing an update.
  // TODO: b/316926338 - Remove once switch state transitions to entities and
  // fuzzer can use weighted distribution for multicast.
  float fuzz_multicast_group_entry_probability = 0;

  // -- Optional ---------------------------------------------------------------
  // The set of tables where the fuzzer should treat their resource guarantees
  // as hard limits rather than trying to go above them. If there are
  // limitations or bugs on the switch causing it to behave incorrectly when the
  // resource guarantees of particular tables are exceeded, this list can be
  // used to allow the fuzzer to produce interesting results in spite of this
  // shortcoming.
  // This is a btree_set to ensure a deterministic ordering.
  absl::btree_set<std::string>
      tables_for_which_to_not_exceed_resource_guarantees;
  // Fully qualified names of tables, actions, or match fields to skip during
  // fuzzing. Match field names should be prepended with the relevant table name
  // to uniquely identify them.
  // Users should ensure that any set that makes it impossible to generate a
  // valid table entry for a particular table contains the table itself.
  // TODO: Check the property above instead.
  absl::flat_hash_set<std::string> disabled_fully_qualified_names;
  // TODO: Fully qualified names of tables that do not support
  // MODIFY updates. This behaviour is not compliant with p4 runtime spec.
  absl::flat_hash_set<std::string> non_modifiable_tables;
  // A function for masking inequalities (due to known bugs) between entries
  // with the same TableEntryKey on the switch and in the fuzzer.
  std::optional<std::function<bool(const pdpi::IrTableEntry &,
                                   const pdpi::IrTableEntry &)>>
      TreatAsEqualDuringReadDueToKnownBug;
  // Controls whether empty ActionProfile one-shots should be generated.
  bool no_empty_action_profile_groups = false;
  // Ignores the constraints on tables listed when fuzzing entries.
  absl::flat_hash_set<std::string> ignore_constraints_on_tables;
};

class FuzzerConfig {
public:
  static absl::StatusOr<FuzzerConfig> Create(const p4::config::v1::P4Info &info,
                                             ConfigParams params);

  absl::Status SetP4Info(const p4::config::v1::P4Info &info);

  const p4::config::v1::P4Info &GetP4Info() const { return info_; }
  const pdpi::IrP4Info &GetIrP4Info() const { return ir_info_; }
  const p4_constraints::ConstraintInfo &GetConstraintInfo() const {
    return constraint_info_;
  }

  // Param Setters - implement only if needed.
  void SetPorts(const std::vector<pins_test::P4rtPortId> &ports) {
    params_.ports = ports;
  }
  void SetQosQueues(const std::vector<std::string> &qos_queues) {
    params_.qos_queues = qos_queues;
  }
  void SetMutateUpdateProbability(float mutate_update_probability) {
    params_.mutate_update_probability = mutate_update_probability;
  }
  void SetFuzzMulticastGroupEntryProbability(
      float fuzz_multicast_group_entry_probability) {
    params_.fuzz_multicast_group_entry_probability =
        fuzz_multicast_group_entry_probability;
  }
  void SetDisabledFullyQualifiedNames(
      const absl::flat_hash_set<std::string> &disabled_fully_qualified_names) {
    params_.disabled_fully_qualified_names = disabled_fully_qualified_names;
  }
  void SetNoEmptyActionProfileGroups(bool no_empty_action_profile_groups) {
    params_.no_empty_action_profile_groups = no_empty_action_profile_groups;
  }

  // Param Getters
  const std::vector<pins_test::P4rtPortId> &GetPorts() const {
    return params_.ports;
  }
  const std::vector<std::string> &GetQosQueues() const {
    return params_.qos_queues;
  }
  std::string GetRole() const { return params_.role; }
  float GetMutateUpdateProbability() const {
    return params_.mutate_update_probability;
  }
  float GetFuzzMulticastGroupEntryProbability() const {
    return params_.fuzz_multicast_group_entry_probability;
  }
  const absl::btree_set<std::string> &
  GetTablesForWhichToNotExceedResourceGuarantees() const {
    return params_.tables_for_which_to_not_exceed_resource_guarantees;
  }
  const absl::flat_hash_set<std::string> &
  GetDisabledFullyQualifiedNames() const {
    return params_.disabled_fully_qualified_names;
  }
  const absl::flat_hash_set<std::string> &GetNonModifiableTables() const {
    return params_.non_modifiable_tables;
  }
  const std::optional<std::function<bool(const pdpi::IrTableEntry &,
                                         const pdpi::IrTableEntry &)>> &
  GetTreatAsEqualDuringReadDueToKnownBug() const {
    return params_.TreatAsEqualDuringReadDueToKnownBug;
  }
  bool GetNoEmptyActionProfileGroups() const {
    return params_.no_empty_action_profile_groups;
  }
  const absl::flat_hash_set<std::string> &GetIgnoreConstraintsOnTables() const {
    return params_.ignore_constraints_on_tables;
  }

private:
  explicit FuzzerConfig() {}

  // The P4Info of the program to be fuzzed.
  // Invariant: The two P4Infos and ConstraintInfo are always in sync.
  p4::config::v1::P4Info info_;
  pdpi::IrP4Info ir_info_;
  // Used to fuzz table entries for tables with P4-Constraints.
  p4_constraints::ConstraintInfo constraint_info_;

  ConfigParams params_;

  // TODO: b/276461175 - Support P4RT translated types.
  // Checks the following assumptions made about p4 constraints that aren't
  // marked as ignored in `params_`:
  // 1) No constraint includes a match field that has a P4Runtime translated
  //    type and is an EXACT match field. The fuzzer cannot satisfy constraints
  //    on this type and EXACT fields are required, so this combination is
  //    forbidden.
  // Also logs the following information:
  // TODO: b/324083270 - Remove once references+constraints are handled.
  // 1) A field that is both constrained and has a reference. The fuzzer will
  //    choose to satisfy references over constraints, which means the resulting
  //    entry may not satisfy constraints. This is a current weakness of the
  //    fuzzer, but does not make it impossible to fuzz valid values if
  //    constraints are permissive or referenced values have relevant
  //    constraints.
  // 2) A field is constrained, a P4Runtime translated type and omittable. The
  //    fuzzer cannot satisfy constraints on this type, but valid entries may
  //    still be fuzzed if this field is omitted when fuzzing.
  absl::Status CheckConstraintAssumptions();
};

} // namespace p4_fuzzer

#endif // PINS_INFRA_P4_FUZZER_FUZZER_CONFIG_H_
