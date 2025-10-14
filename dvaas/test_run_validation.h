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

#ifndef PINS_test_run_validation_H_
#define PINS_test_run_validation_H_

#include <functional>
#include <string>
#include <vector>

#include "absl/base/nullability.h"
#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "dvaas/switch_api.h"
#include "dvaas/test_vector.pb.h"
#include "google/protobuf/descriptor.h"
#include "google/protobuf/repeated_ptr_field.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"

namespace dvaas {

// Parameters to control the comparison between the actual switch output and the
// expected switch output per input packet.
struct SwitchOutputDiffParams {
  // Used to skip packet fields where model and switch are known to have
  // different behavior, which we don't want to test. All FieldDescriptors
  // should belong to packetlib::Packet. The ignored fields are ignored both in
  // normal (i.e. front-panel) packets and in packet-ins.
  std::vector<const google::protobuf::FieldDescriptor *>
      ignored_packetlib_fields;

  // Used to skip packet-in metadata where model and switch are known to have
  // different behavior, which we don't want to test. If a packet-in metadata
  // field name in the actual or expected packets is equal to one of the entries
  // in `ignored_metadata_for_validation`, the field is ignored during
  // comparison.
  absl::flat_hash_set<std::string> ignored_packet_in_metadata;

  // If true, packet-ins (punted packets) are ignored while comparing expected
  // and actual output. Note that packet-ins are completely ignored on both
  // sides. Effectively the expected and actual outputs are compared assuming
  // neither has any packet-ins.
  // TODO: Remove and replace with
  // `ignore_missing_packet_ins_in_actual_output`.
  bool treat_expected_and_actual_outputs_as_having_no_packet_ins = false;

  // If instantiated, `ModifyExpectedOutputPreDiffing` is used to modify the
  // expected switch output prior to diffing it against the actual output. This
  // can be a useful workaround if the BMv2 simulation producing the expected
  // output cannot be made 100% accurate (e.g. go/dvaas-fopic). This is only
  // recommended as a last resort, fixing the simulation should be preferred.
  std::function<absl::Status(
      const SwitchInput& input, const SwitchOutput& actual_output,
      const SwitchApi& sut,
      google::protobuf::RepeatedPtrField<SwitchOutput>& acceptable_outputs)>
      ModifyExpectedOutputPreDiffing;
};

// Validates the given `test_run` using the parameters in `diff_params`. The
// parameter `sut` is required if and only if
// `diff_params.ModifyExpectedOutputPreDiffing` is set. The function returns an
// invalid argument error if `sut` is required but null.
absl::StatusOr<PacketTestValidationResult> ValidateTestRun(
    PacketTestRun test_run, const SwitchOutputDiffParams& diff_params = {},
    absl::Nullable<SwitchApi*> sut = nullptr);

// Like `ValidateTestRun`, but for a collection of `test_runs`.
absl::StatusOr<PacketTestOutcomes> ValidateTestRuns(
    const PacketTestRuns& test_runs, const SwitchOutputDiffParams& diff_params,
    absl::Nullable<SwitchApi*> sut = nullptr);

} // namespace dvaas

#endif // PINS_test_run_validation_H_
