// Copyright 2025 Google LLC
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

#ifndef PINS_P4_INFRA_P4_PDPI_UTILS_IR_H_
#define PINS_P4_INFRA_P4_PDPI_UTILS_IR_H_

#include <stdint.h>

#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "google/protobuf/repeated_ptr_field.h"
#include "google/rpc/code.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/translation_options.h"
#if !defined(ABSL_IS_LITTLE_ENDIAN)
#error \
    "Some of the utility functions are not supported in Big Endian architecture"
#endif

namespace pdpi {

// There are 3 flavors of byte strings used in this file:
// 1. Normalized Byte String: The number of bytes in this string is the same as
//    the number of bytes defined in the bitwidth field of the element in the
//    P4Info file.
// 2. Canonical Byte String: This is the shortest string that fits the encoded
//    value. This is the format used by P4RT as described in
//    https://p4.org/p4-spec/p4runtime/main/P4Runtime-Spec.html#sec-bytestrings.
// 3. Arbitrary Byte String: Any byte string encoding described by the P4RT
//    specification (specifically
//    https://p4.org/p4-spec/p4runtime/main/P4Runtime-Spec.html#sec-bytestrings).
//    This can be the canonical representation, but it could also contain
//    additional leading zeros.
//
// Generally PDPI functions take arbitrary byte strings as inputs, and produce
// byte strings in canonical form as output (unless otherwise stated).

constexpr int kNumBitsInByte = 8;
constexpr int kNumBitsInMac = 48;
constexpr int kNumBytesInMac = kNumBitsInMac / kNumBitsInByte;
constexpr int kNumBitsInIpv4 = 32;
constexpr int kNumBytesInIpv4 = kNumBitsInIpv4 / kNumBitsInByte;
constexpr int kNumBitsInIpv6 = 128;
constexpr int kNumBytesInIpv6 = kNumBitsInIpv6 / kNumBitsInByte;
constexpr absl::string_view kNewBullet = "- ";
constexpr absl::string_view kIndent = "  ";

// Returns the format for value, given the annotations on it, it's bitwidth
// and named type (if any).
absl::StatusOr<Format> GetFormat(const std::vector<std::string> &annotations,
                                 const int bitwidth, bool is_sdn_string);

// Checks if the IrValue in the IR table entry is in the same format as
// specified in the P4Info. If "allow_arbitrary_format" in the translation
// options is true, any format is accepted.
absl::Status ValidateIrValueFormat(const IrValue &ir_value, Format format,
                                   const TranslationOptions &options);

// Converts the IR value to a PI byte string and returns it.
absl::StatusOr<std::string> IrValueToNormalizedByteString(
    const IrValue& ir_value, const int bitwidth);

// Converts the PI value to an IR value and returns it.
absl::StatusOr<IrValue> ArbitraryByteStringToIrValue(Format format,
                                                     const int bitwidth,
                                                     const std::string &bytes);

// Returns an IrValue based on a string value and a format. The value is
// expected to already be formatted correctly, and is just copied to the correct
// oneof field.
absl::StatusOr<IrValue> FormattedStringToIrValue(const std::string &value,
                                                 Format format);

// Returns a std::string based on an IrValue value and a format. The value is
// expected to already be formatted correctly, and is just returned as is.
absl::StatusOr<std::string> IrValueToFormattedString(const IrValue& value,
                                                     Format format);

// Returns the string contents of an IrValue for the populated format (or "" if
// there is no data).
std::string IrValueString(const IrValue &value);

// Return a short-form representation of an IrTableEntry.
// This is useful for creating a unique, short description of the table entry
// and its actions. It is easier to read and shorter than a generic protobuf
// representation which will include repreated references to message and leaf
// names.
//
// Does not include metadata, meter, and counters.
std::string ShortDescription(const IrTableEntry &entry);

// Returns a string of length ceil(expected_bitwidth/8).
absl::StatusOr<std::string> ArbitraryToNormalizedByteString(
    const std::string& bytes, int expected_bitwidth);

// Convert an arbitrary byte string to its canonical form.
// TODO: Move to byte_string.h and rename appropriately.
std::string ArbitraryToCanonicalByteString(std::string bytes);

// Convert the given byte string into a uint value.
absl::StatusOr<uint64_t> ArbitraryByteStringToUint(const std::string &bytes,
                                                   int bitwidth);

// Convert the given uint to byte string.
absl::StatusOr<std::string> UintToNormalizedByteString(uint64_t value,
                                                       int bitwidth);

// Returns if a (normalized) byte string is all zeros.
bool IsAllZeros(const std::string &s);

// Returns the intersection of two (normalized) byte strings.
absl::StatusOr<std::string> Intersection(const std::string &left,
                                         const std::string &right);

// Returns the (normalized) mask for a given prefix length.
absl::StatusOr<std::string> PrefixLenToMask(int prefix_len, int bitwidth);

absl::Status IsGoogleRpcCode(int rpc_code);
// Checks if the rpc code and message satisfy the condition of UpdateStatus.
// 1: If `code` is ok, `message` should be empty.
// 2: If `code` is not ok, `message` should not be empty.
absl::Status ValidateGenericUpdateStatus(google::rpc::Code code,
                                         const std::string &message);
// Parses IrUpdateStatus inside of `ir_write_response`` into string.
std::string IrWriteResponseToReadableMessage(
    const IrWriteResponse& ir_write_response);

// Returns a formatted error message that can be inserted directly into a
// status.
std::string GenerateFormattedError(absl::string_view field,
                                   absl::string_view error_string);

// Generates a descriptive reason to return to caller.
std::string GenerateReason(absl::string_view entity_name,
                           absl::string_view error_message);

// Returns a "Table <table_name>" string.
std::string TableName(absl::string_view table_name);

// Returns a "MatchField <match_name>" string.
std::string MatchFieldName(absl::string_view match_name);

// Returns a "Action <action_name>" string.
std::string ActionName(absl::string_view action_name);

// Returns a "Param <param_name>" string.
std::string ParamName(absl::string_view param_name);

// Returns a "Metadata <packet_name>" string.
std::string MetadataName(absl::string_view metadata_name);

// Checks for an "@deprecated" annotation in the argument.
bool IsElementDeprecated(
    const google::protobuf::RepeatedPtrField<std::string> &annotations);

}  // namespace pdpi

#endif  // PINS_P4_INFRA_P4_PDPI_UTILS_IR_H_
