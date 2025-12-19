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

#include "tests/lib/packet_generator.h"

#include <netinet/in.h>

#include <algorithm>
#include <cctype>
#include <iterator>
#include <limits>
#include <optional>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/strings/numbers.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/proto_matchers.h"
#include "gutil/status_matchers.h"
#include "p4_pdpi/packetlib/packetlib.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"

namespace pins_test {
namespace packetgen {
namespace {

using ::gutil::EqualsProto;
using ::gutil::IsOk;
using ::testing::Each;
using ::testing::ElementsAre;
using ::testing::Eq;
using ::testing::Le;
using ::testing::Not;
using ::testing::Property;
using ::testing::ValuesIn;

std::string OptionsTestName(const testing::TestParamInfo<Options> info) {
  std::string test_name;
  for (char c : ToString(info.param)) {
    if (std::isalnum(c)) test_name.append(1, c);
  }
  return test_name;
}

std::vector<Options> AllOptions() {
  std::vector<Options> options;
  for (IpType ip_type : {IpType::kIpv4, IpType::kIpv6}) {
    for (Field field : AllFields()) {
      for (IpType inner_ip_type : {IpType::kIpv4, IpType::kIpv6}) {
        options.push_back({.ip_type = ip_type,
                           .variables = {field},
                           .inner_ip_type = inner_ip_type});
      }
      options.push_back({.ip_type = ip_type,
                         .variables = {field},
                         .inner_ip_type = std::nullopt});
    }
  }
  return options;
}

std::vector<Options> AllValidOptionsWithOneVariable() {
  std::vector<Options> options = AllOptions();
  options.erase(std::remove_if(options.begin(), options.end(),
                               [](const Options& options) {
                                 return !IsValid(options).ok();
                               }),
                options.end());
  return options;
}

std::vector<Options> AllValidOptionsWithTwoVariables() {
  // Use the name to identify options with equivalent field sets.
  absl::flat_hash_map<std::string, Options> options_by_name;
  for (const Options& one_var_options : AllValidOptionsWithOneVariable()) {
    for (Field field : AllFields()) {
      if (field == *one_var_options.variables.begin()) continue;
      Options two_var_options = one_var_options;
      two_var_options.variables.insert(field);
      options_by_name.insert_or_assign(ToString(two_var_options),
                                       two_var_options);
    }
  }
  std::vector<Options> options;
  for (auto& [name, option] : options_by_name) {
    options.push_back(std::move(option));
  }
  options.erase(std::remove_if(options.begin(), options.end(),
                               [](const Options& options) {
                                 return !IsValid(options).ok();
                               }),
                options.end());
  return options;
}

std::vector<Options> AllValidOptionsWithOneOrTwoVariables() {
  std::vector<Options> options = AllValidOptionsWithOneVariable();
  std::vector<Options> two_var_options = AllValidOptionsWithTwoVariables();
  options.insert(options.end(),
                 std::make_move_iterator(two_var_options.begin()),
                 std::make_move_iterator(two_var_options.end()));
  return options;
}

TEST(PacketGenerator, CreateReturnsErrorForIpv6FieldsInIpv4Packet) {
  EXPECT_THAT(PacketGenerator::Create({
                  .ip_type = IpType::kIpv4,
                  .variables = {Field::kFlowLabelLower16},
              }),
              Not(IsOk()));
  EXPECT_THAT(PacketGenerator::Create({
                  .ip_type = IpType::kIpv4,
                  .variables = {Field::kFlowLabelUpper4},
              }),
              Not(IsOk()));
}

TEST(PacketGenerator, CreateReturnsErrorForInnerIpv6FieldsInInnerIpv4Packet) {
  EXPECT_THAT(PacketGenerator::Create({
                  .ip_type = IpType::kIpv4,
                  .variables = {Field::kInnerFlowLabelLower16},
                  .inner_ip_type = IpType::kIpv4,
              }),
              Not(IsOk()));
  EXPECT_THAT(PacketGenerator::Create({
                  .ip_type = IpType::kIpv4,
                  .variables = {Field::kInnerFlowLabelUpper4},
                  .inner_ip_type = IpType::kIpv4,
              }),
              Not(IsOk()));
}

TEST(PacketGenerator, CreateReturnsErrorForInnerIpFieldInUnnestedPacket) {
  EXPECT_THAT(PacketGenerator::Create({
                  .ip_type = IpType::kIpv4,
                  .variables = {Field::kInnerIpSrc},
              }),
              Not(IsOk()));
  EXPECT_THAT(PacketGenerator::Create({
                  .ip_type = IpType::kIpv4,
                  .variables = {Field::kInnerIpDst},
              }),
              Not(IsOk()));
  EXPECT_THAT(PacketGenerator::Create({
                  .ip_type = IpType::kIpv4,
                  .variables = {Field::kInnerHopLimit},
              }),
              Not(IsOk()));
  EXPECT_THAT(PacketGenerator::Create({
                  .ip_type = IpType::kIpv4,
                  .variables = {Field::kInnerDscp},
              }),
              Not(IsOk()));
  EXPECT_THAT(PacketGenerator::Create({
                  .ip_type = IpType::kIpv4,
                  .variables = {Field::kInnerFlowLabelLower16},
              }),
              Not(IsOk()));
  EXPECT_THAT(PacketGenerator::Create({
                  .ip_type = IpType::kIpv4,
                  .variables = {Field::kInnerFlowLabelUpper4},
              }),
              Not(IsOk()));
}

TEST(PacketGenerator, CreateReturnsErrorForAnyVariableMismatch) {
  EXPECT_THAT(PacketGenerator::Create({
                  .ip_type = IpType::kIpv4,
                  .variables = {Field::kIpSrc, Field::kInnerFlowLabelUpper4},
              }),
              Not(IsOk()));
}

TEST(PacketGenerator, GeneratesValidIpv4Packet) {
  ASSERT_OK_AND_ASSIGN(PacketGenerator generator,
                       PacketGenerator::Create({.ip_type = IpType::kIpv4}));
  EXPECT_OK(packetlib::SerializePacket(generator.Packet()));
  EXPECT_THAT(
      generator.Packet().headers(),
      ElementsAre(Property(&packetlib::Header::has_ethernet_header, true),
                  Property(&packetlib::Header::has_ipv4_header, true),
                  Property(&packetlib::Header::has_udp_header, true)));
}

TEST(PacketGenerator, GeneratesValidIpv6Packet) {
  ASSERT_OK_AND_ASSIGN(PacketGenerator generator,
                       PacketGenerator::Create({.ip_type = IpType::kIpv6}));
  EXPECT_OK(packetlib::SerializePacket(generator.Packet()));
  EXPECT_THAT(
      generator.Packet().headers(),
      ElementsAre(Property(&packetlib::Header::has_ethernet_header, true),
                  Property(&packetlib::Header::has_ipv6_header, true),
                  Property(&packetlib::Header::has_udp_header, true)));
}

TEST(PacketGenerator, GeneratesValid4In4Packet) {
  ASSERT_OK_AND_ASSIGN(PacketGenerator generator,
                       PacketGenerator::Create({
                           .ip_type = IpType::kIpv4,
                           .inner_ip_type = IpType::kIpv4,
                       }));
  EXPECT_OK(packetlib::SerializePacket(generator.Packet()));
  EXPECT_THAT(
      generator.Packet().headers(),
      ElementsAre(Property(&packetlib::Header::has_ethernet_header, true),
                  Property(&packetlib::Header::has_ipv4_header, true),
                  Property(&packetlib::Header::has_ipv4_header, true),
                  Property(&packetlib::Header::has_udp_header, true)));
}

TEST(PacketGenerator, GeneratesValid6In4Packet) {
  ASSERT_OK_AND_ASSIGN(PacketGenerator generator,
                       PacketGenerator::Create({
                           .ip_type = IpType::kIpv4,
                           .inner_ip_type = IpType::kIpv6,
                       }));
  EXPECT_OK(packetlib::SerializePacket(generator.Packet()));
  EXPECT_THAT(
      generator.Packet().headers(),
      ElementsAre(Property(&packetlib::Header::has_ethernet_header, true),
                  Property(&packetlib::Header::has_ipv4_header, true),
                  Property(&packetlib::Header::has_ipv6_header, true),
                  Property(&packetlib::Header::has_udp_header, true)));
}

TEST(PacketGenerator, GeneratesValid4In6Packet) {
  ASSERT_OK_AND_ASSIGN(PacketGenerator generator,
                       PacketGenerator::Create({
                           .ip_type = IpType::kIpv6,
                           .inner_ip_type = IpType::kIpv4,
                       }));
  EXPECT_OK(packetlib::SerializePacket(generator.Packet()));
  EXPECT_THAT(
      generator.Packet().headers(),
      ElementsAre(Property(&packetlib::Header::has_ethernet_header, true),
                  Property(&packetlib::Header::has_ipv6_header, true),
                  Property(&packetlib::Header::has_ipv4_header, true),
                  Property(&packetlib::Header::has_udp_header, true)));
}

TEST(PacketGenerator, GeneratesValid6In6Packet) {
  ASSERT_OK_AND_ASSIGN(PacketGenerator generator,
                       PacketGenerator::Create({
                           .ip_type = IpType::kIpv6,
                           .inner_ip_type = IpType::kIpv6,
                       }));
  EXPECT_OK(packetlib::SerializePacket(generator.Packet()));
  EXPECT_THAT(
      generator.Packet().headers(),
      ElementsAre(Property(&packetlib::Header::has_ethernet_header, true),
                  Property(&packetlib::Header::has_ipv6_header, true),
                  Property(&packetlib::Header::has_ipv6_header, true),
                  Property(&packetlib::Header::has_udp_header, true)));
}

TEST(PacketGenerator, GeneratesMultipleFields) {
  ASSERT_OK_AND_ASSIGN(
      PacketGenerator generator,
      PacketGenerator::Create({
          .ip_type = IpType::kIpv4,
          .variables = {Field::kIpSrc, Field::kIpDst, Field::kL4DstPort},
      }));
  packetlib::Packet packet0 = generator.Packet(0);
  packetlib::Packet static_packet0 = packet0;
  static_packet0.mutable_headers(1)->mutable_ipv4_header()->clear_ipv4_source();
  static_packet0.mutable_headers(1)
      ->mutable_ipv4_header()
      ->clear_ipv4_destination();
  static_packet0.mutable_headers(2)
      ->mutable_udp_header()
      ->clear_destination_port();

  packetlib::Packet packet1 = generator.Packet(1);
  packetlib::Packet static_packet1 = packet1;
  static_packet1.mutable_headers(1)->mutable_ipv4_header()->clear_ipv4_source();
  static_packet1.mutable_headers(1)
      ->mutable_ipv4_header()
      ->clear_ipv4_destination();
  static_packet1.mutable_headers(2)
      ->mutable_udp_header()
      ->clear_destination_port();

  SCOPED_TRACE(
      absl::Substitute("Failed to verify packet diff from packets generator $0",
                       generator.Description()));
  EXPECT_THAT(static_packet0, EqualsProto(static_packet1));
  EXPECT_THAT(packet0.headers(1).ipv4_header().ipv4_source(),
              Not(Eq(packet1.headers(1).ipv4_header().ipv4_source())));
  EXPECT_THAT(packet0.headers(1).ipv4_header().ipv4_destination(),
              Not(Eq(packet1.headers(1).ipv4_header().ipv4_destination())));
  EXPECT_THAT(packet0.headers(2).udp_header().destination_port(),
              Not(Eq(packet1.headers(2).udp_header().destination_port())));
}

// Define a tuple-based matcher for EqualsProto for use in testing::Pointwise.
MATCHER(PointwiseEqualsProto, "") {
  return gutil::ProtobufEqMatcher(std::get<1>(arg))
      .MatchAndExplain(std::get<0>(arg), result_listener);
}

TEST(PacketGenerator, PacketsMatchesIndividualPacketResults) {
  ASSERT_OK_AND_ASSIGN(PacketGenerator generator,
                       PacketGenerator::Create({
                           .ip_type = IpType::kIpv4,
                           .variables = {Field::kIpSrc, Field::kL4SrcPort},
                           .inner_ip_type = IpType::kIpv6,
                       }));
  std::vector<packetlib::Packet> packets = generator.Packets(10);
  std::vector<packetlib::Packet> individual_packets;
  for (int i = 0; i < 10; ++i) {
    individual_packets.push_back(generator.Packet(i));
  }
  EXPECT_THAT(packets,
              testing::Pointwise(PointwiseEqualsProto(), individual_packets));
}

TEST(PacketGenerator, PacketsMatchesIndividualPacketResultsWithOffset) {
  ASSERT_OK_AND_ASSIGN(PacketGenerator generator,
                       PacketGenerator::Create({
                           .ip_type = IpType::kIpv4,
                           .variables = {Field::kIpSrc, Field::kL4SrcPort},
                           .inner_ip_type = IpType::kIpv6,
                       }));
  std::vector<packetlib::Packet> packets = generator.Packets(10, 11);
  std::vector<packetlib::Packet> individual_packets;
  for (int i = 11; i < 11 + 10; ++i) {
    individual_packets.push_back(generator.Packet(i));
  }
  EXPECT_THAT(packets,
              testing::Pointwise(PointwiseEqualsProto(), individual_packets));
}

TEST(PacketGenerator, NonVariableGeneratorHasRangeOfOne) {
  ASSERT_OK_AND_ASSIGN(PacketGenerator generator,
                       PacketGenerator::Create(Ipv4PacketOptions()));
  EXPECT_EQ(generator.NumPossiblePackets(), 1);
}

// The following two tests verify the general value skipping logic but are not
// meant to test all skipped values.

class PacketGeneratorOptions : public testing::TestWithParam<Options> {};

TEST_P(PacketGeneratorOptions, AreAllValidOrInvalid) {
  auto generator = PacketGenerator::Create(GetParam());
  if (generator.ok()) {
    EXPECT_OK(packetlib::SerializePacket(generator->Packet()));
  }
}

INSTANTIATE_TEST_SUITE_P(AllOptions, PacketGeneratorOptions,
                         ValuesIn(AllOptions()), OptionsTestName);

class SingleFieldOptions : public testing::TestWithParam<Options> {};

TEST_P(SingleFieldOptions, RangeIsPositive) {
  Field field = *GetParam().variables.begin();
  switch (field) {
    case Field::kFlowLabelLower16:
    case Field::kFlowLabelUpper4:
    case Field::kInnerFlowLabelLower16:
    case Field::kInnerFlowLabelUpper4:
      EXPECT_GT(Range(field, IpType::kIpv4), 0);
      break;
    default:
      EXPECT_GT(Range(field, IpType::kIpv4), 0);
      EXPECT_GT(Range(field, IpType::kIpv6), 0);
  }
}

TEST_P(SingleFieldOptions, EditsOnlyTheRequestedField) {
  ASSERT_OK_AND_ASSIGN(auto generator, PacketGenerator::Create(GetParam()));
  packetlib::Packet packet0 = generator.Packet();
  packet0.clear_payload();
  packetlib::Packet packet1 = generator.Packet(1);
  packet1.clear_payload();

  bool encapped = GetParam().inner_ip_type.has_value();
  switch (*GetParam().variables.begin()) {
    case Field::kEthernetSrc:
      packet0.mutable_headers(0)
          ->mutable_ethernet_header()
          ->clear_ethernet_source();
      packet1.mutable_headers(0)
          ->mutable_ethernet_header()
          ->clear_ethernet_source();
      break;
    case Field::kEthernetDst:
      packet0.mutable_headers(0)
          ->mutable_ethernet_header()
          ->clear_ethernet_destination();
      packet1.mutable_headers(0)
          ->mutable_ethernet_header()
          ->clear_ethernet_destination();
      break;
    case Field::kIpSrc:
      if (GetParam().ip_type == IpType::kIpv4) {
        packet0.mutable_headers(1)->mutable_ipv4_header()->clear_ipv4_source();
        packet1.mutable_headers(1)->mutable_ipv4_header()->clear_ipv4_source();
      } else {
        packet0.mutable_headers(1)->mutable_ipv6_header()->clear_ipv6_source();
        packet1.mutable_headers(1)->mutable_ipv6_header()->clear_ipv6_source();
      }
      break;
    case Field::kIpDst:
      if (GetParam().ip_type == IpType::kIpv4) {
        packet0.mutable_headers(1)
            ->mutable_ipv4_header()
            ->clear_ipv4_destination();
        packet1.mutable_headers(1)
            ->mutable_ipv4_header()
            ->clear_ipv4_destination();
      } else {
        packet0.mutable_headers(1)
            ->mutable_ipv6_header()
            ->clear_ipv6_destination();
        packet1.mutable_headers(1)
            ->mutable_ipv6_header()
            ->clear_ipv6_destination();
      }
      break;
    case Field::kHopLimit:
      if (GetParam().ip_type == IpType::kIpv4) {
        packet0.mutable_headers(1)->mutable_ipv4_header()->clear_ttl();
        packet1.mutable_headers(1)->mutable_ipv4_header()->clear_ttl();
      } else {
        packet0.mutable_headers(1)->mutable_ipv6_header()->clear_hop_limit();
        packet1.mutable_headers(1)->mutable_ipv6_header()->clear_hop_limit();
      }
      break;
    case Field::kDscp:
      if (GetParam().ip_type == IpType::kIpv4) {
        packet0.mutable_headers(1)->mutable_ipv4_header()->clear_dscp();
        packet1.mutable_headers(1)->mutable_ipv4_header()->clear_dscp();
      } else {
        packet0.mutable_headers(1)->mutable_ipv6_header()->clear_dscp();
        packet1.mutable_headers(1)->mutable_ipv6_header()->clear_dscp();
      }
      break;
    // Flow label is 20 bits, which is 5 hex digits +2 chars for '0x'.
    // We split the hex string into:
    // * Upper-4  bits (0xN)nnnn | chars [0 - 2]
    // * Lower-16 bits 0xn(NNNN) | chars [3 - 6]
    case Field::kFlowLabelLower16:
      EXPECT_THAT(
          packet0.headers(1).ipv6_header().flow_label().substr(0, 3),
          Eq(packet1.headers(1).ipv6_header().flow_label().substr(0, 3)))
          << "Unexpected difference in upper 4 bits of Flow Label.";
      packet0.mutable_headers(1)->mutable_ipv6_header()->clear_flow_label();
      packet1.mutable_headers(1)->mutable_ipv6_header()->clear_flow_label();
      break;
    case Field::kFlowLabelUpper4:
      EXPECT_THAT(packet0.headers(1).ipv6_header().flow_label().substr(3),
                  Eq(packet1.headers(1).ipv6_header().flow_label().substr(3)))
          << "Unexpected difference in lower 16 bits of Flow Label.";
      packet0.mutable_headers(1)->mutable_ipv6_header()->clear_flow_label();
      packet1.mutable_headers(1)->mutable_ipv6_header()->clear_flow_label();
      break;
    case Field::kInnerIpSrc:
      if (GetParam().inner_ip_type == IpType::kIpv4) {
        packet0.mutable_headers(2)->mutable_ipv4_header()->clear_ipv4_source();
        packet1.mutable_headers(2)->mutable_ipv4_header()->clear_ipv4_source();
      } else {
        packet0.mutable_headers(2)->mutable_ipv6_header()->clear_ipv6_source();
        packet1.mutable_headers(2)->mutable_ipv6_header()->clear_ipv6_source();
      }
      break;
    case Field::kInnerIpDst:
      if (GetParam().inner_ip_type == IpType::kIpv4) {
        packet0.mutable_headers(2)
            ->mutable_ipv4_header()
            ->clear_ipv4_destination();
        packet1.mutable_headers(2)
            ->mutable_ipv4_header()
            ->clear_ipv4_destination();
      } else {
        packet0.mutable_headers(2)
            ->mutable_ipv6_header()
            ->clear_ipv6_destination();
        packet1.mutable_headers(2)
            ->mutable_ipv6_header()
            ->clear_ipv6_destination();
      }
      break;
    case Field::kInnerHopLimit:
      if (GetParam().inner_ip_type == IpType::kIpv4) {
        packet0.mutable_headers(2)->mutable_ipv4_header()->clear_ttl();
        packet1.mutable_headers(2)->mutable_ipv4_header()->clear_ttl();
      } else {
        packet0.mutable_headers(2)->mutable_ipv6_header()->clear_hop_limit();
        packet1.mutable_headers(2)->mutable_ipv6_header()->clear_hop_limit();
      }
      break;
    case Field::kInnerDscp:
      if (GetParam().inner_ip_type == IpType::kIpv4) {
        packet0.mutable_headers(2)->mutable_ipv4_header()->clear_dscp();
        packet1.mutable_headers(2)->mutable_ipv4_header()->clear_dscp();
      } else {
        packet0.mutable_headers(2)->mutable_ipv6_header()->clear_dscp();
        packet1.mutable_headers(2)->mutable_ipv6_header()->clear_dscp();
      }
      break;
    case Field::kInnerFlowLabelLower16:
      EXPECT_THAT(
          packet0.headers(2).ipv6_header().flow_label().substr(0, 3),
          Eq(packet1.headers(2).ipv6_header().flow_label().substr(0, 3)))
          << "Unexpected difference in upper 4 bits of Flow Label.";
      packet0.mutable_headers(2)->mutable_ipv6_header()->clear_flow_label();
      packet1.mutable_headers(2)->mutable_ipv6_header()->clear_flow_label();
      break;
    case Field::kInnerFlowLabelUpper4:
      EXPECT_THAT(packet0.headers(2).ipv6_header().flow_label().substr(3),
                  Eq(packet1.headers(2).ipv6_header().flow_label().substr(3)))
          << "Unexpected difference in lower 16 bits of Flow Label.";
      packet0.mutable_headers(2)->mutable_ipv6_header()->clear_flow_label();
      packet1.mutable_headers(2)->mutable_ipv6_header()->clear_flow_label();
      break;
    case Field::kL4SrcPort:
      packet0.mutable_headers(encapped ? 3 : 2)
          ->mutable_udp_header()
          ->clear_source_port();
      packet1.mutable_headers(encapped ? 3 : 2)
          ->mutable_udp_header()
          ->clear_source_port();
      break;
    case Field::kL4DstPort:
      packet0.mutable_headers(encapped ? 3 : 2)
          ->mutable_udp_header()
          ->clear_destination_port();
      packet1.mutable_headers(encapped ? 3 : 2)
          ->mutable_udp_header()
          ->clear_destination_port();
      break;
  }
  EXPECT_THAT(packet0, EqualsProto(packet1));
}

INSTANTIATE_TEST_SUITE_P(PacketGeneratorTest, SingleFieldOptions,
                         ValuesIn(AllValidOptionsWithOneVariable()),
                         OptionsTestName);

class SingleOrDoubleFieldOptions : public testing::TestWithParam<Options> {};

TEST_P(SingleOrDoubleFieldOptions, GeneratorRangeMatchesVariableRange) {
  const Options options = GetParam();
  std::vector<int> ranges_from_options;
  for (const Field field : options.variables) {
    if (InnerIpFields().contains(field)) {
      ranges_from_options.push_back(Range(field, *options.inner_ip_type));
    } else {
      ranges_from_options.push_back(Range(field, options.ip_type));
    }
  }

  ASSERT_OK_AND_ASSIGN(auto generator, PacketGenerator::Create(options));
  if (ranges_from_options.size() == 1) {
    EXPECT_EQ(generator.NumPossiblePackets(), ranges_from_options[0]);
  } else {
    EXPECT_THAT(ranges_from_options, Each(Le(generator.NumPossiblePackets())));
  }
}

TEST_P(SingleOrDoubleFieldOptions, CreatesDifferentPackets) {
  ASSERT_OK_AND_ASSIGN(auto generator, PacketGenerator::Create(GetParam()));
  std::vector<std::string> packet_descriptions;
  std::set<std::string> packet_contents;
  int num_packets = std::min(1000, generator.NumPossiblePackets());
  ASSERT_GT(num_packets, 0);
  for (int i = 0; i < num_packets; ++i) {
    SCOPED_TRACE(absl::Substitute("Failed packet $0 of $1", i, num_packets));
    packetlib::Packet packet = generator.Packet(i);
    packet.set_payload("");  // Only check the header.
    packet_descriptions.push_back(packet.ShortDebugString());
    ASSERT_OK_AND_ASSIGN(std::string raw_packet,
                         packetlib::SerializePacket(packet));
    EXPECT_FALSE(packet_contents.count(raw_packet))
        << "Duplicate packet: " << packet.ShortDebugString();
  }
}

TEST_P(SingleOrDoubleFieldOptions, GeneratesAValidPacketAtAnyIndex) {
  ASSERT_OK_AND_ASSIGN(auto generator, PacketGenerator::Create(GetParam()));
  EXPECT_OK(SerializePacket(generator.Packet(0)));
  for (int i = 0; i < std::numeric_limits<int>::digits; ++i) {
    int index = 1 << i;
    EXPECT_OK(SerializePacket(generator.Packet(index)));
    EXPECT_OK(SerializePacket(generator.Packet(index - 1)));
    EXPECT_OK(SerializePacket(generator.Packet(-index)));
    EXPECT_OK(SerializePacket(generator.Packet(-index + 1)));
  }
  EXPECT_OK(SerializePacket(generator.Packet(std::numeric_limits<int>::max())));
  EXPECT_OK(SerializePacket(generator.Packet(std::numeric_limits<int>::min())));
}

INSTANTIATE_TEST_SUITE_P(PacketGeneratorTest, SingleOrDoubleFieldOptions,
                         ValuesIn(AllValidOptionsWithOneOrTwoVariables()),
                         OptionsTestName);

}  // namespace
}  // namespace packetgen
}  // namespace pins_test
