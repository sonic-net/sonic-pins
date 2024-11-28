// Copyright 2024 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "dvaas/test_run_validation.h"

#include <optional>
#include <ostream>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_join.h"
#include "absl/strings/str_replace.h"
#include "absl/strings/string_view.h"
#include "absl/strings/strip.h"
#include "absl/strings/substitute.h"
#include "absl/types/optional.h"
#include "absl/types/span.h"
#include "dvaas/output_writer.h"
#include "dvaas/test_vector.h"
#include "dvaas/test_vector.pb.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "google/protobuf/descriptor.h"
#include "google/protobuf/util/message_differencer.h"
#include "gtest/gtest.h"
#include "gutil/proto.h"
#include "gutil/status.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "re2/re2.h"

namespace dvaas {

namespace {

using ::google::protobuf::util::MessageDifferencer;
using ::gutil::PrintTextProto;
using ::testing::MatchResultListener;

// -- Detailed comparison of actual vs expected `SwitchOutput`s ----------------

bool PacketLessThan(const Packet* a, const Packet* b) {
  return a->hex() < b->hex();
}

bool PacketInLessThan(const PacketIn* a, const PacketIn* b) {
  return a->hex() < b->hex();
}

// Returns a copy of the given `string` with all newlines indented by
// (an additional) `indentation` number of spaces. Empty lines are not indented.
std::string Indent(int indentation, absl::string_view string) {
  // Avoid indenting empty lines: remove here, then add back at the end.
  bool stripped_trailing_newline = absl::ConsumeSuffix(&string, "\n");
  std::string result = absl::StrReplaceAll(
      string, {
                  {
                      "\n",
                      absl::StrCat("\n", std::string(indentation, ' ')),
                  },
              });
  if (stripped_trailing_newline) absl::StrAppend(&result, "\n");
  return result;
}

std::optional<pdpi::IrPacketMetadata> GetPacketInMetadataByName(
    const PacketIn& packet_in, absl::string_view target) {
  for (const auto& metadata : packet_in.metadata()) {
    if (metadata.name() == target) return metadata;
  }
  return std::nullopt;
}

bool CompareSwitchOutputs(SwitchOutput actual_output,
                          SwitchOutput expected_output,
                          const SwitchOutputDiffParams& params,
                          MatchResultListener* listener) {
  if (actual_output.packets_size() != expected_output.packets_size()) {
    *listener << "has mismatched number of packets (actual: "
              << actual_output.packets_size()
              << " expected: " << expected_output.packets_size() << ")\n";
    return false;
  }

  if (!params.treat_expected_and_actual_outputs_as_having_no_packet_ins) {
    if (actual_output.packet_ins_size() != expected_output.packet_ins_size()) {
      *listener << "has mismatched number of packet ins (actual: "
                << actual_output.packet_ins_size()
                << " expected: " << expected_output.packet_ins_size() << ")\n";
      return false;
    }
  }

  std::sort(actual_output.mutable_packets()->pointer_begin(),
            actual_output.mutable_packets()->pointer_end(), PacketLessThan);
  std::sort(expected_output.mutable_packets()->pointer_begin(),
            expected_output.mutable_packets()->pointer_end(), PacketLessThan);
  std::sort(actual_output.mutable_packet_ins()->pointer_begin(),
            actual_output.mutable_packet_ins()->pointer_end(),
            PacketInLessThan);
  std::sort(expected_output.mutable_packet_ins()->pointer_begin(),
            expected_output.mutable_packet_ins()->pointer_end(),
            PacketInLessThan);

  for (int i = 0; i < expected_output.packets_size(); ++i) {
    const Packet& actual_packet = actual_output.packets(i);
    const Packet& expected_packet = expected_output.packets(i);
    MessageDifferencer differ;
    for (auto* field : params.ignored_packetlib_fields)
      differ.IgnoreField(field);
    std::string diff;
    differ.ReportDifferencesToString(&diff);
    if (!differ.Compare(expected_packet.parsed(), actual_packet.parsed())) {
      *listener << "has packet " << i << " with mismatched header fields:\n  "
                << Indent(2, diff);
      return false;
    }
    if (expected_packet.port() != actual_packet.port()) {
      *listener << "has packet " << i << " with mismatched ports:\n"
                << absl::Substitute("  \"$0\" -> \"$1\"",
                                    expected_packet.port(),
                                    actual_packet.port());
      return false;
    }
  }

  if (!params.treat_expected_and_actual_outputs_as_having_no_packet_ins) {
    for (int i = 0; i < expected_output.packet_ins_size(); ++i) {
      const PacketIn& actual_packet_in = actual_output.packet_ins(i);
      const PacketIn& expected_packet_in = expected_output.packet_ins(i);

      MessageDifferencer differ;
      for (auto* field : params.ignored_packetlib_fields)
        differ.IgnoreField(field);
      std::string diff;
      differ.ReportDifferencesToString(&diff);
      if (!differ.Compare(expected_packet_in.parsed(),
                          actual_packet_in.parsed())) {
        *listener << "has packet in " << i
                  << " with mismatched header fields:\n  " << Indent(2, diff);
        return false;
      }

      // Check that received packet in has desired metadata (except for ignored
      // metadata).
      for (const auto& expected_metadata : expected_packet_in.metadata()) {
        if (params.ignored_packet_in_metadata.contains(
                expected_metadata.name()))
          continue;

        std::optional<pdpi::IrPacketMetadata> actual_metadata =
            GetPacketInMetadataByName(actual_packet_in,
                                      expected_metadata.name());
        if (!actual_metadata.has_value()) {
          *listener << "has packet in " << i << " with missing metadata field '"
                    << expected_metadata.name() << "':\n  " << Indent(2, diff);
          return false;
        }

        if (!differ.Compare(expected_metadata.value(),
                            actual_metadata->value())) {
          *listener << "has packet in " << i
                    << " with mismatched value for metadata field '"
                    << expected_metadata.name() << "':\n  " << Indent(2, diff);
          return false;
        }
      }

      // Check that received packet in does not have additional metadata (except
      // for ignored metadata).
      for (const auto& actual_metadata : actual_packet_in.metadata()) {
        if (params.ignored_packet_in_metadata.contains(actual_metadata.name()))
          continue;

        std::optional<pdpi::IrPacketMetadata> expected_metadata =
            GetPacketInMetadataByName(expected_packet_in,
                                      actual_metadata.name());
        if (!expected_metadata.has_value()) {
          *listener << "has packet in " << i
                    << " with additional metadata field '"
                    << actual_metadata.name() << "':\n  " << Indent(2, diff);
          return false;
        }
      }
    }
  }

  *listener << "matches\n";
  return true;
}

// Compares the `actual_output` to the `acceptable_outputs` in the given
// `packet_test_vector`, returning `absl::nullopt` if the actual output
// is acceptable, or an explanation of why it is not otherwise.
absl::optional<std::string> CompareSwitchOutputs(
    const PacketTestVector packet_test_vector,
    const SwitchOutput& actual_output, const SwitchOutputDiffParams& params) {
  testing::StringMatchResultListener listener;
  for (int i = 0; i < packet_test_vector.acceptable_outputs_size(); ++i) {
    const SwitchOutput& expected_output =
        packet_test_vector.acceptable_outputs(i);
    listener << "- acceptable output #" << (i + 1) << " ";
    if (CompareSwitchOutputs(actual_output, expected_output, params,
                             &listener)) {
      return absl::nullopt;
    }
  }
  return listener.str();
}

// -- Simplified switch output characterizations -------------------------------

// Characterization of a `SwitchOutput` in terms of two key metrics: how many
// packets got forwarded and how many got punted?
// The purpose of this struct is to give a compact summary of a switch output
// that is easy to understand. This is useful in error messages, because actual
// `SwitchOutput`s are complex (they specify packet header fields and payloads,
// for example) and so dumping them directly is overwhelming.
struct SwitchOutputCharacterization {
  int num_forwarded;
  int num_punted;

  // https://abseil.io/docs/cpp/guides/hash#tldr-how-do-i-make-my-type-hashable
  template <typename H>
  friend H AbslHashValue(H h, const SwitchOutputCharacterization& x) {
    return H::combine(std::move(h), x.num_forwarded, x.num_punted);
  }
};

bool operator==(const SwitchOutputCharacterization& x,
                const SwitchOutputCharacterization& y) {
  return x.num_forwarded == y.num_forwarded && x.num_punted == y.num_punted;
}

// Returns a simple characterization of the given `output`.
SwitchOutputCharacterization CharacterizeSwitchOutput(
    const SwitchOutput& output) {
  return SwitchOutputCharacterization{
      .num_forwarded = output.packets_size(),
      .num_punted = output.packet_ins_size(),
  };
}

// Returns a human-readable description of the given `output`, for use in error
// messages.
std::string DescribeSwitchOutput(const SwitchOutputCharacterization& output) {
  const bool forwarded = output.num_forwarded > 0;
  const bool punted = output.num_punted > 0;
  if (forwarded && punted)
    return absl::Substitute("forwarded ($0 copies) and punted ($1 copies)",
                            output.num_forwarded, output.num_punted);
  if (forwarded && !punted)
    return absl::Substitute("forwarded ($0 copies)", output.num_forwarded);
  if (!forwarded && punted)
    return absl::Substitute("punted ($0 copies)", output.num_punted);
  return "dropped";
}

// Returns a human-readable description of the expectation encoded by the given
// `acceptable_output_characterizations`, for use in error messages.
std::string DescribeExpectation(
    const SwitchInput& input,
    const absl::flat_hash_set<SwitchOutputCharacterization>&
        acceptable_output_characterizations) {
  // This should never happen, but it is convenient for this function to be pure
  // and so we handle the case gracefully and without erroring.
  if (acceptable_output_characterizations.empty())
    return "false (will always fail)";
  // In practice, while there are often multiple acceptable outputs
  // (e.g., due to WCMP), all of them tend to have the same *output
  // characterization*. So this function is optimized for the case
  // `acceptable_output_characterizations.size() == 1` and doesn't try to be
  // clever otherwise.
  return absl::StrJoin(acceptable_output_characterizations, ", or ",
                       [&](std::string* output, auto& acceptable_output) {
                         absl::StrAppend(
                             output, SwitchInput::Type_Name(input.type()),
                             " packet gets ",
                             DescribeSwitchOutput(acceptable_output));
                       });
}

// Returns a human-readable description of the given `actual_output`, for use in
// error messages.
std::string DescribeActual(const SwitchInput& input,
                           const SwitchOutputCharacterization& actual_output) {
  return absl::StrCat(SwitchInput::Type_Name(input.type()), " packet got ",
                      DescribeSwitchOutput(actual_output));
}

// Returns whether the packet with the given `characterization` got dropped.
bool IsCharacterizedAsDrop(
    const SwitchOutputCharacterization& characterization) {
  return characterization.num_forwarded == 0 &&
         characterization.num_punted == 0;
}

// Returns whether the packet with the given possible `characterizations`
// surely (according to all characterizations) got dropped.
bool IsCharacterizedAsDrop(
    const absl::flat_hash_set<SwitchOutputCharacterization>&
        characterizations) {
  return characterizations.size() == 1 &&
         IsCharacterizedAsDrop(*characterizations.cbegin());
}

static constexpr absl::string_view kInputBanner =
    "== INPUT "
    "=======================================================================";
static constexpr absl::string_view kActualBanner =
    "== ACTUAL OUTPUT "
    "===============================================================";
static constexpr absl::string_view kExpectationBanner =
    "== EXPECTED OUTPUT "
    "=============================================================";

}  // namespace

absl::StatusOr<int> ExtractTestPacketTag(const packetlib::Packet& packet) {
  // Regexp to extract the ID from a test packet's payload.
  constexpr LazyRE2 kTestPacketIdRegexp{R"(test packet #([0-9]+):)"};
  int tag;
  if (RE2::PartialMatch(packet.payload(), *kTestPacketIdRegexp, &tag))
    return tag;
  return absl::InvalidArgumentError(absl::StrCat(
      "Payload does not contain a packet id: ", packet.DebugString()));
}

PacketTestValidationResult ValidateTestRun(
    const PacketTestRun& test_run, const SwitchOutputDiffParams& diff_params) {
  PacketTestValidationResult result;

  const absl::optional<std::string> diff = CompareSwitchOutputs(
      test_run.test_vector(), test_run.actual_output(), diff_params);
  if (!diff.has_value()) return result;

  // To make the diff more digestible, we first give an abstract
  // characterization of the expected and actual outputs.
  absl::flat_hash_set<SwitchOutputCharacterization>
      acceptable_output_characterizations;
  for (auto& acceptable_output : test_run.test_vector().acceptable_outputs()) {
    acceptable_output_characterizations.insert(
        CharacterizeSwitchOutput(acceptable_output));
  }
  const SwitchOutputCharacterization actual_output_characterization =
      CharacterizeSwitchOutput(test_run.actual_output());
  const bool actual_matches_expected =
      acceptable_output_characterizations.contains(
          actual_output_characterization);

  std::string expectation = DescribeExpectation(
      test_run.test_vector().input(), acceptable_output_characterizations);
  if (!diff_params.ignored_packetlib_fields.empty()) {
    absl::StrAppend(
        &expectation, "\n          (ignoring the field(s) ",
        absl::StrJoin(diff_params.ignored_packetlib_fields, ",",
                      [](std::string* out,
                         const google::protobuf::FieldDescriptor* field) {
                        absl::StrAppend(out, "'", field->name(), "'");
                      }),
        ")");
  }
  if (diff_params.treat_expected_and_actual_outputs_as_having_no_packet_ins) {
    absl::StrAppend(&expectation, "\n          (ignoring packet-ins)");
  }
  std::string actual = DescribeActual(test_run.test_vector().input(),
                                      actual_output_characterization);
  if (actual_matches_expected) {
    absl::StrAppend(&actual, ", but with unexpected modifications");
  }
  std::string& failure = *result.mutable_failure()->mutable_description();
  failure = absl::Substitute(
      "Expected: $0\n  Actual: $1\n$2\nDetails dumped below.\n\n", expectation,
      actual, *diff);

  // Dump input.
  absl::StrAppend(&failure, kInputBanner, "\n",
                  PrintTextProto(test_run.test_vector().input()));

  // Dump actual output, if any.
  if (!IsCharacterizedAsDrop(actual_output_characterization)) {
    absl::StrAppend(&failure, kActualBanner, "\n",
                    PrintTextProto(test_run.actual_output()));
  }

  // Dump expected output, if any.
  if (!IsCharacterizedAsDrop(acceptable_output_characterizations)) {
    absl::StrAppend(&failure, kExpectationBanner, "\n");
    for (int i = 0; i < test_run.test_vector().acceptable_outputs_size(); ++i) {
      absl::StrAppendFormat(
          &failure, "-- Acceptable output: Alternative #%d --\n%s", (i + 1),
          PrintTextProto(test_run.test_vector().acceptable_outputs(i)));
    }
  }

  return result;
}

absl::Status ValidateTestRuns(const PacketTestRuns& test_runs,
                              const SwitchOutputDiffParams& diff_params,
                              const OutputWriterFunctionType& write_failures) {
  LOG(INFO) << "Validating test runs";

  std::vector<std::string> failures;
  for (const PacketTestRun& test_run : test_runs.test_runs()) {
    PacketTestValidationResult result = ValidateTestRun(test_run, diff_params);
    if (result.has_failure()) {
      failures.push_back(result.failure().description());
    }
  }

  RETURN_IF_ERROR(write_failures(absl::StrJoin(failures, "\n\n")));

  if (!failures.empty()) {
    return gutil::FailedPreconditionErrorBuilder()
           << failures.size()
           << " failures among test results. Showing only the first failure.\n"
           << failures[0]
           << "\nRefer to the test artifacts for the full list of failures.";
  }

  return absl::OkStatus();
}

}  // namespace dvaas
