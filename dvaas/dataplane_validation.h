// Library for validating dataplane behavior of a switch under test using
// automatically synthesized test packets. See go/dvaas for more details.

/* Copyright 2024 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/

#ifndef PINS_DVAAS_DATAPLANE_VALIDATION_H_
#define PINS_DVAAS_DATAPLANE_VALIDATION_H_

#include <functional>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "dvaas/labeler.h"
#include "dvaas/output_writer.h"
#include "dvaas/packet_injection.h"
#include "dvaas/packet_trace.pb.h"
#include "dvaas/port_id_map.h"
#include "dvaas/switch_api.h"
#include "dvaas/test_run_validation.h"
#include "dvaas/test_vector.h"
#include "dvaas/test_vector.pb.h"
#include "dvaas/validation_result.h"
#include "gutil/gutil/test_artifact_writer.h"
#include "lib/p4rt/p4rt_port.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_symbolic/packet_synthesizer/coverage_goal.pb.h"
#include "p4_symbolic/packet_synthesizer/packet_synthesizer.pb.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "thinkit/mirror_testbed.h"

namespace dvaas {

// -- User Facing API ----------------------------------------------------------

// P4 artifacts specifying the switch control plane API and its intended
// dataplane behavior.
struct P4Specification {
  // P4-Symbolic is the packet generator that we use. Its P4Info and device
  // configuration may need to be specifically modified to workaround
  // potential P4-Symbolic issues.
  p4::v1::ForwardingPipelineConfig p4_symbolic_config;

  // BMv2 is the switch simulator that we compare the dataplane results to. It
  // is instantiated with a BMv2 compatible forwarding pipeline config
  // containing a P4Info and a device configuration. These may need to be
  // specifically modified for BMv2 due to some missing features, e.g. the
  // lack of support for @p4runtime_translation.
  p4::v1::ForwardingPipelineConfig bmv2_config;
};

// Stores configurable parameters for `PostProcessTestVectorFailure` for packet
// failure determinism. Attempt at most
// `num_of_replication_attempts_per_failure` number of reruns for the first
// `max_failures_to_attempt_to_replicate` failures.
struct FailureEnhancementOptions {
  int max_failures_to_attempt_to_replicate = 1;
  int num_of_replication_attempts_per_failure = 100;
  // If true, collect and print the packet's trace.
  bool collect_packet_trace = true;
  // Minimize the set of test vectors that caused the first
  // `max_number_of_failures_to_minimize` failures.
  // TODO: Currently, the algorithm terminates if the set of
  // entities from packet trace is not sufficient to reproduce the failure.
  int max_number_of_failures_to_minimize = 1;
  // Ensures that any minimized failure maintains the original expectation and
  // switch output.
  bool maintain_original_failure_during_minimization = true;
};

// Specifies user-facing parameters of DVaaS. These are also the parameters that
// are likely to vary across tests.
struct DataplaneValidationParams {
  // Parameters to control the comparison between the actual switch
  // output and the expected switch output per input packet.
  SwitchOutputDiffParams switch_output_diff_params;

  // Prefix to add to the names of artifacts written by DVaaS.
  std::string artifact_prefix = "dvaas";

  // Optional parameter that, if set, is used by DVaaS to generate a header to
  // append to each artifact before writing to it.
  std::optional<std::function<std::string()>> get_artifact_header;

  // If set, causes DVaaS to use the given `P4Specification` instead of
  // inferring one from the SUT.
  std::optional<P4Specification> specification_override;

  // Max number of packets to send per second. If no rate is given, DVaaS will
  // send packets as quickly as it can.
  std::optional<int> max_packets_to_send_per_second;

  // For a packet-in from SUT or control switch without a test tag (i.e. an
  // "unsolicited packet"), this function determines if the packet is among
  // expected such packets or not. If this function returns false, dataplane
  // validation fails immediately.
  IsExpectedUnsolicitedPacketFunctionType is_expected_unsolicited_packet =
      [](const packetlib::Packet& packet) -> bool { return false; };

  // Optionally, a list of custom packet test vectors. If non-empty, automated
  // test vector generation is disabled and only the given test vectors are used
  // for validation.
  //
  // See `user_provided_packet_test_vector.h` for documentation on how to define
  // valid test vectors.
  std::vector<PacketTestVector> packet_test_vector_override;

  // Optionally, can be used to override the default assumption that each SUT
  // port is connected to a control switch port with the same OpenConfig
  // interface name.
  // NOTE: Not required for valid mirror testbeds. This is a workaround for
  // non-standard testbeds only.
  std::optional<MirrorTestbedP4rtPortIdMap> mirror_testbed_port_map_override;

  // Maximum allowed time for dataplane validation to synthesize test packets.
  // If nullopt, packet synthesizer runs to completion for its coverage goals.
  // Otherwise, if packet synthesis timed out, the synthesis results cover the
  // coverage goals only partially.
  std::optional<absl::Duration> packet_synthesis_time_limit = std::nullopt;

  // Coverage goals override for automated packet synthesis (go/coverage-goals).
  // If nullopt the backend uses its default goals, which should work well
  // enough in most cases.
  std::optional<p4_symbolic::packet_synthesizer::CoverageGoals>
      coverage_goals_override;

  // A struct to store configurable parameters for packet failure determinism.
  // Parameters in `failure_enhancement_options` are assigned default values.
  FailureEnhancementOptions failure_enhancement_options;

  // A list of labelers (go/test-vector-labeling) that are applied to each
  // `PacketTestRun`. The labels may be extracted based on various
  // characteristics such as packet injection time, tables hit, punted, dropped,
  // etc.
  std::vector<std::function<absl::StatusOr<Labels>(const PacketTestRun&)>>
      labelers = DefaultPacketTestRunLabelers();

  // If true, collect and print the switch counters.
  bool reset_and_collect_counters = true;
};

// Forward declaration. See below for description.
class DataplaneValidationBackend;

// Used to validate the dataplane behavior of a mirror testbed. See go/dvaas for
// more details.
// WARNING: This class is NOT thread-safe.
class DataplaneValidator {
 public:
  DataplaneValidator() = delete;
  explicit DataplaneValidator(
      std::unique_ptr<DataplaneValidationBackend> backend)
      : backend_(std::move(backend)) {}

  // Validates that the `testbed.Sut()` processes packets according to the
  // `P4Specification` of the switch as follows:
  //
  // 1. Opens P4RT and gNMI connections to SUT and control switch.
  //
  // 2. Mirrors the SUT P4RT port ID <-> interface mapping to the control
  //    switch. If a port map override is provided, this step is skipped and the
  //    provided port map gets used.
  //
  // 3. Generates test packets that together satisfy some coverage goal, which
  //    can be tweaked using the `params`. By default, generates test packets to
  //    hit every table entry installed on the switch at least once.
  //
  // 4. Sends those test packets to the switch and a P4 simulator, where the
  //    simulator is initialized using the switch's `P4Specification`.
  //
  // 5. Validates that the switch forwards/punts/drops packets as the P4
  //    simulator predicts.
  //
  // Preconditions:
  // 1. Both switches must be configured with a P4Info and gNMI config.
  // 2. Enabled ports must be up.
  //
  // Post-conditions on success:
  // 1. The only entries installed on control switch will be those returned by
  //    `GetEntriesToPuntAllPackets`.
  // 2. Any preexisting P4RT connections to SUT and control switch will be
  //    non-primary.
  // 3. The gNMI configs will be unchanged.
  // 4. Switch counters may change arbitrarily.
  //
  // Returns an Ok status if dataplane validation succeeds, or an error status
  // detailing invalid dataplane behaviors otherwise.
  absl::StatusOr<ValidationResult> ValidateDataplane(
      thinkit::MirrorTestbed& testbed,
      const DataplaneValidationParams& params = {});

  // Same as above `ValidateDataplane`, but has these differences:
  // Preconditions:
  // 1. The `sut` and `control_switch` P4RT connections must be primary.
  // TODO: Remove this pre-condition.
  // 2. Either a SUT <-> control switch P4RT port map must be passed in `params`
  //    or the P4RT port ID <-> interface mapping of the control switch in the
  //    gNMI config must be the same as the SUT.
  //
  // Post-conditions:
  // 1. Pre-existing connections are left as they are.
  // 2. gNMI configs will be unchanged.
  absl::StatusOr<ValidationResult> ValidateDataplaneUsingExistingSwitchApis(
      SwitchApi& sut, SwitchApi& control_switch,
      thinkit::TestEnvironment& test_environment,
      const DataplaneValidationParams& params = {});

  // Returns statistics about all packets sent during the lifetime of the
  // DataplaneValidator. If dataplane validation has failed, the returned
  // statistics may be inaccurate and are instead lower bounds on the true
  // values.
  PacketStatistics GetCurrentPacketStatistics() const {
    return packet_statistics_;
  }

 private:
  std::unique_ptr<DataplaneValidationBackend> backend_;
  // Used to write artifacts.
  gutil::BazelTestArtifactWriter artifact_writer_;
  // Records packet statistics during dataplane validation.
  PacketStatistics packet_statistics_;
};

// -- Backend API --------------------------------------------------------------
// NOTICE: This portion of the API is only for DVaaS maintainers. Users need not
// worry about anything below this line!
// -----------------------------------------------------------------------------

// Abstract internals of Dataplane Validator. Specifies those
// parameters that we expect to be constant throughout a system, as opposed to
// DataplaneValidationParams, which specifies those that we expect may change
// between tests.
// These are abstract for one or more of the following reasons:
// 1. Some functions (e.g. IsExpectedUnsolicitedPacket,
//    GetEntriesToPuntAllPackets, and InferP4Specification) are non-portable in
//    that they differ by system, but are unlikely to change between tests of
//    the same system. Thus, there is no reason for users to implement these
//    individually.
// 2. Some functions (e.g. SynthesizePackets and
// GeneratePacketTestVectors) do not
//    yet have open-source implementations and thus need to be instantiated
//    outside of tests. Ideally, these would disappear from the
//    DataplaneValidationBackend as they become open-source and instead be
//    integrated directly into the DVaaS implementation.
//
// NOTE: Users are not expected to implement this class!
class DataplaneValidationBackend {
 public:
  // Synthesizes packets to send to the switch. We don't want to be tied to a
  // specific packet synthesis implementation (our current implementation is not
  // even open-source yet), so DVaaS takes the synthesis function as an input
  // parameter.
  virtual absl::StatusOr<PacketSynthesisResult> SynthesizePackets(
      const pdpi::IrP4Info& ir_p4info, const pdpi::IrEntities& ir_entities,
      const p4::v1::ForwardingPipelineConfig& p4_symbolic_config,
      absl::Span<const pins_test::P4rtPortId> ports,
      const OutputWriterFunctionType& write_stats,
      const std::optional<p4_symbolic::packet_synthesizer::CoverageGoals>&
          coverage_goals_override,
      std::optional<absl::Duration> time_limit = std::nullopt) const = 0;

  // Generates a map of test ID to PacketTestVector with output prediction
  // given a list of `synthesized_packets` for the given input (program,
  // entries, ports, etc.). We don't want to be tied to a specific test vector
  // generation implementation (the current implementation relies on a
  // non-open-source BMv2 wrapper), so DVaaS takes the function as an input.
  //
  // Note: The packets and ports used as input in the returned test vectors
  // should be slightly modified versions of the input `synthesize_packets`:
  //  1. If the ingress port is not specified in the synthesized packet,
  //     `default_ingress_port` is used.
  //  2. The payload of the original packet is tagged with the test vector ID.
  //     The tagged payload can be used associate the outputs of the device
  //     under test with its inputs.
  //  3. The packet will be padded to minimum size and the computed fields
  //     recomputed.
  //
  // If `check_prediction_conformity` is set to true, the method should ensure
  // that the `synthesized_packets` predictions are in line with the expected
  // outputs of the generated test vectors.
  virtual absl::StatusOr<PacketTestVectorById> GeneratePacketTestVectors(
      const pdpi::IrP4Info& ir_p4info, const pdpi::IrEntities& ir_entities,
      const p4::v1::ForwardingPipelineConfig& bmv2_config,
      absl::Span<const pins_test::P4rtPortId> ports,
      std::vector<p4_symbolic::packet_synthesizer::SynthesizedPacket>&
          synthesized_packets,
      const pins_test::P4rtPortId& default_ingress_port,
      bool check_prediction_conformity = true) const = 0;

  // Returns a set of entities that cause all received packets to be punted,
  // given the `switch_p4info` installed on the switch. The test *will* install
  // these entities on the control switch and the user *must* ensure that the
  // entities cause *all* packets to be punted. Otherwise, test behavior is
  // undefined.
  virtual absl::StatusOr<pdpi::IrEntities> GetEntitiesToPuntAllPackets(
      const pdpi::IrP4Info& switch_p4info) const = 0;

  // Returns the `P4Specification` that models the given `sut`. Used only if the
  // `specification_override` parameter is unset.
  // May query the SUT, but should not change it.
  virtual absl::StatusOr<P4Specification> InferP4Specification(
      SwitchApi& sut) const = 0;

  // Augments the given `packet_test_vectors` with compact packet traces if
  // `use_compact_traces` is true, otherwise full packet traces are added.
  virtual absl::Status AugmentPacketTestVectorsWithPacketTraces(
      std::vector<PacketTestVector>& packet_test_vectors,
      const pdpi::IrP4Info& ir_p4info, const pdpi::IrEntities& ir_entities,
      const p4::v1::ForwardingPipelineConfig& bmv2_compatible_config,
      bool use_compact_traces) const = 0;

  // Creates entities for v1Model auxiliary tables that model the effects of the
  // given entities (e.g. VLAN membership) and gNMI configuration (e.g. port
  // loopback mode).
  virtual absl::StatusOr<pdpi::IrEntities> CreateV1ModelAuxiliaryEntities(
      const pdpi::IrEntities& ir_entities, const pdpi::IrP4Info& ir_p4info,
      gnmi::gNMI::StubInterface& gnmi_stub) const = 0;

  virtual ~DataplaneValidationBackend() = default;
};

// Stores test vectors as well as the result of automated test packet synthesis
// (if any).
struct GenerateTestVectorsResult {
  PacketTestVectorById packet_test_vector_by_id;
  PacketSynthesisResult packet_synthesis_result;
};

// Generates and returns test vectors as well as packet synthesis result using
// the backend functions `SynthesizePackets` and `GeneratePacketTestVectors`.
// Reads the table entries, P4Info, and relevant P4RT port IDs from the switch.
absl::StatusOr<GenerateTestVectorsResult> GenerateTestVectors(
    const DataplaneValidationParams& params, SwitchApi& sut,
    DataplaneValidationBackend& backend, gutil::TestArtifactWriter& writer);

// Determines the P4 specification DVaaS should use, and performs some sanity
// checks to ensure the specification is compatible with the switch.
absl::StatusOr<P4Specification> InferP4Specification(
    const DataplaneValidationParams& params,
    const DataplaneValidationBackend& backend, SwitchApi& sut);

// Stores a given `packet_test_vector` as an ArribaTestVector using only the
// entries that might be hit by the packet (according to its P4 packet trace).
absl::Status StorePacketTestVectorAsArribaTestVector(
    const PacketTestVector& packet_test_vector,
    gutil::TestArtifactWriter& dvaas_test_artifact_writer);

}  // namespace dvaas

#endif  // PINS_DVAAS_DATAPLANE_VALIDATION_H_
