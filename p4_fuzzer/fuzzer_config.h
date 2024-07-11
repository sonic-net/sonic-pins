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
#ifndef PINS_P4_FUZZER_FUZZER_CONFIG_H_
#define PINS_P4_FUZZER_FUZZER_CONFIG_H_

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
#include "p4_pdpi/ir.pb.h"

namespace p4_fuzzer {

class FuzzerConfig {
 public:
  static absl::StatusOr<FuzzerConfig> Create(
      const p4::config::v1::P4Info& info);

  absl::Status SetP4Info(const p4::config::v1::P4Info& info);

  const p4::config::v1::P4Info& GetP4Info() const { return info_; }
  const pdpi::IrP4Info& GetIrP4Info() const { return ir_info_; }

  // TODO: These should be taken in as parameters and populated
  // with Create instead.
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
  std::optional<
      std::function<bool(const pdpi::IrTableEntry&, const pdpi::IrTableEntry&)>>
      TreatAsEqualDuringReadDueToKnownBug;
  // Controls whether empty ActionProfile one-shots should be generated.
  bool no_empty_action_profile_groups = false;

 private:
  explicit FuzzerConfig() {}

  // The P4Info of the program to be fuzzed.
  p4::config::v1::P4Info info_;
  // Invariant: The two P4Infos are always consistent.
  pdpi::IrP4Info ir_info_;
};

}  // namespace p4_fuzzer

#endif  // PINS_P4_FUZZER_FUZZER_CONFIG_H_
