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

#ifndef PINS_TESTS_LIB_PACKET_GENERATOR_H_
#define PINS_TESTS_LIB_PACKET_GENERATOR_H_

#include <net/ethernet.h>
#include <netinet/in.h>

#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "absl/container/btree_set.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "gutil/gutil/status.h"  // IWYU pragma: keep
#include "gutil/gutil/status.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.pb.h"

// Helper library to hold a collection of functions to define a test
// configuration, define a packet, generate a packet etc.
namespace pins_test {
namespace packetgen {

// Modifiable fields within a packet.
enum class Field {
  kEthernetSrc,
  kEthernetDst,
  kIpSrc,
  kIpDst,
  kHopLimit,
  kDscp,
  kFlowLabelLower16,
  kFlowLabelUpper4,
  kInnerIpSrc,
  kInnerIpDst,
  kInnerHopLimit,
  kInnerDscp,
  kInnerFlowLabelLower16,
  kInnerFlowLabelUpper4,
  kL4SrcPort,
  kL4DstPort,
  // Any new Field values must be added to AllFields().
};

// Returns the string name of a field.
std::string FieldName(Field field);

// Returns a list of all field enums.
const absl::btree_set<Field>& AllFields();
const absl::btree_set<Field>& InnerIpFields();

enum class IpType { kIpv4, kIpv6 };

// Options to define the packet generation behavior.
struct Options {
  IpType ip_type;  // IP type of the packet or outer IP type if encapped.
  absl::btree_set<Field> variables;     // Set of fields to vary.
  std::optional<IpType> inner_ip_type;  // Inner IP type. Required if encapped.
};
inline Options Ipv4PacketOptions() { return {.ip_type = IpType::kIpv4}; }
inline Options Ipv6PacketOptions() { return {.ip_type = IpType::kIpv6}; }

// Returns ok if the Options struct is valid or an error if it is invalid.
absl::Status IsValid(const Options& options);

// Returns a string describing the Options struct.
std::string ToString(const Options& options);

// Returns the number of unique values that can be generated for the field.
int Range(Field field, IpType ip_type);

// This class generates packets from the provided options. Once the packet
// generator is created, it is expected that any Packet() call will create a
// valid packet.
class PacketGenerator {
 public:
  // Factory function.
  static absl::StatusOr<PacketGenerator> Create(Options options) {
    RETURN_IF_ERROR(IsValid(options));
    return PacketGenerator(std::move(options));
  }

  // Returns a description of the generator options.
  std::string Description() const { return ToString(options_); }

  // Returns the number of unique packets the generator can create.
  // For Options with a single variable, packets [0, NumPossiblePackets() - 1]
  // are guaranteed to be unique.
  int NumPossiblePackets() const;

  // Returns a packet at the given index. Subsequent calls for the same index
  // will return the same packet.
  packetlib::Packet Packet(int index = 0) const;

  // Returns multiple packets with sequential indices. An offset may be given to
  // change the starting index.
  std::vector<packetlib::Packet> Packets(int count, int offset = 0) const;

 private:
  explicit PacketGenerator(Options options) : options_(std::move(options)) {}

  const Options options_;
};

}  // namespace packetgen
}  // namespace pins_test

#endif  // PINS_TESTS_LIB_PACKET_GENERATOR_H_
