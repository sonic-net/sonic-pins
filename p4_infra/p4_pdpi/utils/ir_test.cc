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

#include "p4_infra/p4_pdpi/utils/ir.h"

#include <stdint.h>

#include <string>
#include <tuple>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "gmock/gmock.h"
#include "google/protobuf/repeated_ptr_field.h"
#include "google/protobuf/util/message_differencer.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/proto_matchers.h"
#include "gutil/gutil/status_matchers.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/netaddr/ipv6_address.h"

namespace pdpi {
namespace {

using ::google::protobuf::util::MessageDifferencer;
using ::gutil::EqualsProto;
using ::gutil::IsOkAndHolds;
using ::gutil::StatusIs;

TEST(StringToIrValueTest, Okay) {
  std::vector<std::tuple<std::string, Format, std::string>> testcases = {
      {"abc", Format::STRING, R"pb(str: "abc")pb"},
      {"abc", Format::IPV4, R"pb(ipv4: "abc")pb"},
      {"abc", Format::IPV6, R"pb(ipv6: "abc")pb"},
      {"abc", Format::MAC, R"pb(mac: "abc")pb"},
      {"abc", Format::HEX_STRING, R"pb(hex_str: "abc")pb"},
  };
  for (const auto& [value, format, proto] : testcases) {
    ASSERT_OK_AND_ASSIGN(auto actual, FormattedStringToIrValue(value, format));
    IrValue expected;
    ASSERT_OK(gutil::ReadProtoFromString(proto, &expected));
    EXPECT_TRUE(MessageDifferencer::Equals(actual, expected));
  }
}

TEST(StringToIrValueTest, InvalidFormatFails) {
  ASSERT_FALSE(FormattedStringToIrValue("abc", (Format)-1).ok());
}

TEST(UintToNormalizedByteStringTest, ValidBitwidthValues) {
  std::string value;
  ASSERT_OK_AND_ASSIGN(value, UintToNormalizedByteString(1, 1));
  EXPECT_EQ(value, std::string("\x1"));
}

TEST(UintToNormalizedByteStringTest, InvalidBitwidth) {
  EXPECT_EQ(UintToNormalizedByteString(1, 0).status().code(),
            absl::StatusCode::kInvalidArgument);
  EXPECT_EQ(UintToNormalizedByteString(1, 65).status().code(),
            absl::StatusCode::kInvalidArgument);
}

TEST(UintToNormalizedByteStringTest, Valid8BitwidthValue) {
  const std::string expected = {"\x11"};
  ASSERT_OK_AND_ASSIGN(auto value, UintToNormalizedByteString(0x11, 8));
  EXPECT_EQ(value, expected);
}

TEST(UintToNormalizedByteStringTest, Valid16BitwidthValue) {
  const std::string expected = "\x11\x22";
  ASSERT_OK_AND_ASSIGN(auto value, UintToNormalizedByteString(0x1122, 16));
  EXPECT_EQ(value, expected);
}

TEST(UintToNormalizedByteStringTest, Valid32BitwidthValue) {
  const std::string expected = "\x11\x22\x33\x44";
  ASSERT_OK_AND_ASSIGN(auto value, UintToNormalizedByteString(0x11223344, 32));
  EXPECT_EQ(value, expected);
}

TEST(UintToNormalizedByteStringTest, Valid64BitwidthValue) {
  const std::string expected = "\x11\x22\x33\x44\x55\x66\x77\x88";
  ASSERT_OK_AND_ASSIGN(auto value,
                       UintToNormalizedByteString(0x1122334455667788, 64));
  EXPECT_EQ(value, expected);
}

TEST(UintToNormalizedByteStringAndReverseTest, Valid8BitwidthValue) {
  uint64_t expected = 0x11;
  ASSERT_OK_AND_ASSIGN(auto str_value, UintToNormalizedByteString(expected, 8));
  ASSERT_OK_AND_ASSIGN(auto value, ArbitraryByteStringToUint(str_value, 8));
  EXPECT_EQ(value, expected);
}

TEST(UintToNormalizedByteStringAndReverseTest, Valid16BitwidthValue) {
  uint64_t expected = 0x1122;
  ASSERT_OK_AND_ASSIGN(auto str_value,
                       UintToNormalizedByteString(expected, 16));
  ASSERT_OK_AND_ASSIGN(auto value, ArbitraryByteStringToUint(str_value, 16));
  EXPECT_EQ(value, expected);
}

TEST(UintToNormalizedByteStringAndReverseTest, Valid32BitwidthValue) {
  uint64_t expected = 0x11223344;
  ASSERT_OK_AND_ASSIGN(auto str_value,
                       UintToNormalizedByteString(expected, 32));
  ASSERT_OK_AND_ASSIGN(auto value, ArbitraryByteStringToUint(str_value, 32));
  EXPECT_EQ(value, expected);
}

TEST(UintToNormalizedByteStringAndReverseTest, Valid64BitwidthValue) {
  uint64_t expected = 0x1122334455667788;
  ASSERT_OK_AND_ASSIGN(auto str_value,
                       UintToNormalizedByteString(expected, 64));
  ASSERT_OK_AND_ASSIGN(auto value, ArbitraryByteStringToUint(str_value, 64));
  EXPECT_EQ(value, expected);
}

TEST(ArbitraryByteStringToUintAndReverseTest, Valid8BitwidthValue) {
  const std::string expected = "1";
  ASSERT_OK_AND_ASSIGN(auto uint_value, ArbitraryByteStringToUint(expected, 8));
  ASSERT_OK_AND_ASSIGN(auto value, UintToNormalizedByteString(uint_value, 8));
  EXPECT_EQ(value, expected);
}

TEST(ArbitraryByteStringToUintAndReverseTest, Valid16BitwidthValue) {
  const std::string expected = "12";
  ASSERT_OK_AND_ASSIGN(auto uint_value,
                       ArbitraryByteStringToUint(expected, 16));
  ASSERT_OK_AND_ASSIGN(auto value, UintToNormalizedByteString(uint_value, 16));
  EXPECT_EQ(value, expected);
}

TEST(ArbitraryByteStringToUintAndReverseTest, Valid32BitwidthValue) {
  const std::string expected = "1234";
  ASSERT_OK_AND_ASSIGN(auto uint_value,
                       ArbitraryByteStringToUint(expected, 32));
  ASSERT_OK_AND_ASSIGN(auto value, UintToNormalizedByteString(uint_value, 32));
  EXPECT_EQ(value, expected);
}

TEST(ArbitraryByteStringToUintAndReverseTest, Valid64BitwidthValue) {
  const std::string expected = "12345678";
  ASSERT_OK_AND_ASSIGN(auto uint_value,
                       ArbitraryByteStringToUint(expected, 64));
  ASSERT_OK_AND_ASSIGN(auto value, UintToNormalizedByteString(uint_value, 64));
  EXPECT_EQ(value, expected);
}

TEST(GetFormatTest, MacAnnotationPass) {
  std::vector<std::string> annotations = {"@format(MAC_ADDRESS)"};
  ASSERT_OK_AND_ASSIGN(auto format, GetFormat(annotations, kNumBitsInMac,
                                              /*is_sdn_string=*/false));
  EXPECT_EQ(format, Format::MAC);
}

TEST(GetFormatTest, MacAnnotationInvalidBitwidth) {
  std::vector<std::string> annotations = {"@format(MAC_ADDRESS)"};
  auto status_or_format =
      GetFormat(annotations, /*bitwidth=*/65, /*is_sdn_string=*/false);
  EXPECT_EQ(status_or_format.status().code(),
            absl::StatusCode::kInvalidArgument);
}

TEST(GetFormatTest, Ipv4AnnotationPass) {
  std::vector<std::string> annotations = {"@format(IPV4_ADDRESS)"};
  ASSERT_OK_AND_ASSIGN(auto format, GetFormat(annotations, kNumBitsInIpv4,
                                              /*is_sdn_string=*/false));
  EXPECT_EQ(format, Format::IPV4);
}

TEST(GetFormatTest, Ipv4AnnotationInvalidBitwidth) {
  std::vector<std::string> annotations = {"@format(IPV4_ADDRESS)"};
  auto status_or_format =
      GetFormat(annotations, /*bitwidth=*/65, /*is_sdn_string=*/false);
  EXPECT_EQ(status_or_format.status().code(),
            absl::StatusCode::kInvalidArgument);
}

TEST(GetFormatTest, Ipv6AnnotationPass) {
  EXPECT_THAT(GetFormat({"@format(IPV6_ADDRESS)"}, /*bitwidth=*/kNumBitsInIpv6,
                        /*is_sdn_string=*/false),
              IsOkAndHolds(Format::IPV6));
}

TEST(GetFormatTest, Ipv6AnnotationShortBitwidthPass) {
  EXPECT_THAT(
      GetFormat({"@format(IPV6_ADDRESS)"}, /*bitwidth=*/kNumBitsInIpv6 - 1,
                /*is_sdn_string=*/false),
      IsOkAndHolds(Format::IPV6));
}

TEST(GetFormatTest, Ipv6AnnotationInvalidBitwidth) {
  EXPECT_THAT(
      GetFormat({"@format(IPV6_ADDRESS)"}, /*bitwidth=*/kNumBitsInIpv6 + 1,
                /*is_sdn_string=*/false),
      StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(GetFormatTest, ConflictingAnnotations) {
  std::vector<std::string> annotations = {"@format(IPV6_ADDRESS)",
                                          "@format(IPV4_ADDRESS)"};
  auto status_or_format =
      GetFormat(annotations, /*bitwidth=*/65, /*is_sdn_string=*/false);
  EXPECT_EQ(status_or_format.status().code(),
            absl::StatusCode::kInvalidArgument);
}

TEST(GetFormatTest, SdnStringFormat) {
  std::vector<std::string> annotations = {};
  ASSERT_OK_AND_ASSIGN(auto format, GetFormat(annotations, /*bitwidth=*/65,
                                              /*is_sdn_string=*/true));
  EXPECT_EQ(format, Format::STRING);
}

TEST(GetFormatTest, SdnStringFormatConflictingAnnotations) {
  std::vector<std::string> annotations = {"@format(IPV4_ADDRESS)"};
  auto status_or_format =
      GetFormat(annotations, /*bitwidth=*/65, /*is_sdn_string=*/true);
  EXPECT_EQ(status_or_format.status().code(),
            absl::StatusCode::kInvalidArgument);
}

TEST(GetFormatTest, InvalidAnnotations) {
  std::vector<std::string> annotations = {"@format(IPVx_ADDRESS)"};
  auto status_or_format =
      GetFormat(annotations, /*bitwidth=*/65, /*is_sdn_string=*/false);
  EXPECT_EQ(status_or_format.status().code(),
            absl::StatusCode::kInvalidArgument);
}

TEST(ValidateIrValueFormatTest, ArbitraryFormatWorksForAllIPv4Cases) {
  IrValue testValue;
  testValue.set_ipv4("1.2.3.4");
  EXPECT_OK(ValidateIrValueFormat(testValue, Format::IPV4,
                                  {.allow_arbitrary_format = false}));
  EXPECT_THAT(ValidateIrValueFormat(testValue, Format::IPV6,
                                    {.allow_arbitrary_format = false}),
              StatusIs(absl::StatusCode::kInvalidArgument));
  EXPECT_OK(ValidateIrValueFormat(testValue, Format::IPV6,
                                  {.allow_arbitrary_format = true}));
  EXPECT_THAT(ValidateIrValueFormat(testValue, Format::STRING,
                                    {.allow_arbitrary_format = false}),
              StatusIs(absl::StatusCode::kInvalidArgument));
  EXPECT_OK(ValidateIrValueFormat(testValue, Format::STRING,
                                  {.allow_arbitrary_format = true}));
  EXPECT_THAT(ValidateIrValueFormat(testValue, Format::HEX_STRING,
                                    {.allow_arbitrary_format = false}),
              StatusIs(absl::StatusCode::kInvalidArgument));
  EXPECT_OK(ValidateIrValueFormat(testValue, Format::HEX_STRING,
                                  {.allow_arbitrary_format = true}));
  EXPECT_THAT(ValidateIrValueFormat(testValue, Format::MAC,
                                    {.allow_arbitrary_format = false}),
              StatusIs(absl::StatusCode::kInvalidArgument));
  EXPECT_OK(ValidateIrValueFormat(testValue, Format::MAC,
                                  {.allow_arbitrary_format = true}));
}

TEST(ValidateIrValueFormatTest, ArbitraryFormatWorksForAllIPv6Cases) {
  IrValue testValue;
  testValue.set_ipv6("0:aaaa:bbbb:cccc:dddd:eeee:ffff:0");
  EXPECT_OK(ValidateIrValueFormat(testValue, Format::IPV6,
                                  {.allow_arbitrary_format = false}));
  EXPECT_THAT(ValidateIrValueFormat(testValue, Format::IPV4,
                                    {.allow_arbitrary_format = false}),
              StatusIs(absl::StatusCode::kInvalidArgument));
  EXPECT_OK(ValidateIrValueFormat(testValue, Format::IPV4,
                                  {.allow_arbitrary_format = true}));
  EXPECT_THAT(ValidateIrValueFormat(testValue, Format::STRING,
                                    {.allow_arbitrary_format = false}),
              StatusIs(absl::StatusCode::kInvalidArgument));
  EXPECT_OK(ValidateIrValueFormat(testValue, Format::STRING,
                                  {.allow_arbitrary_format = true}));
  EXPECT_THAT(ValidateIrValueFormat(testValue, Format::HEX_STRING,
                                    {.allow_arbitrary_format = false}),
              StatusIs(absl::StatusCode::kInvalidArgument));
  EXPECT_OK(ValidateIrValueFormat(testValue, Format::HEX_STRING,
                                  {.allow_arbitrary_format = true}));
  EXPECT_THAT(ValidateIrValueFormat(testValue, Format::MAC,
                                    {.allow_arbitrary_format = false}),
              StatusIs(absl::StatusCode::kInvalidArgument));
  EXPECT_OK(ValidateIrValueFormat(testValue, Format::MAC,
                                  {.allow_arbitrary_format = true}));
}

TEST(ValidateIrValueFormatTest, ArbitraryFormatWorksForAllMacCases) {
  IrValue testValue;
  testValue.set_mac("00:11:22:33:44:55:66");
  EXPECT_OK(ValidateIrValueFormat(testValue, Format::MAC,
                                  {.allow_arbitrary_format = false}));
  EXPECT_THAT(ValidateIrValueFormat(testValue, Format::IPV4,
                                    {.allow_arbitrary_format = false}),
              StatusIs(absl::StatusCode::kInvalidArgument));
  EXPECT_OK(ValidateIrValueFormat(testValue, Format::IPV4,
                                  {.allow_arbitrary_format = true}));
  EXPECT_THAT(ValidateIrValueFormat(testValue, Format::IPV6,
                                    {.allow_arbitrary_format = false}),
              StatusIs(absl::StatusCode::kInvalidArgument));
  EXPECT_OK(ValidateIrValueFormat(testValue, Format::IPV6,
                                  {.allow_arbitrary_format = true}));
  EXPECT_THAT(ValidateIrValueFormat(testValue, Format::STRING,
                                    {.allow_arbitrary_format = false}),
              StatusIs(absl::StatusCode::kInvalidArgument));
  EXPECT_OK(ValidateIrValueFormat(testValue, Format::STRING,
                                  {.allow_arbitrary_format = true}));
  EXPECT_THAT(ValidateIrValueFormat(testValue, Format::HEX_STRING,
                                    {.allow_arbitrary_format = false}),
              StatusIs(absl::StatusCode::kInvalidArgument));
  EXPECT_OK(ValidateIrValueFormat(testValue, Format::HEX_STRING,
                                  {.allow_arbitrary_format = true}));
}

TEST(ValidateIrValueFormatTest, ArbitraryFormatWorksForAllHexStringCases) {
  IrValue testValue;
  testValue.set_hex_str("0x01");
  EXPECT_OK(ValidateIrValueFormat(testValue, Format::HEX_STRING,
                                  {.allow_arbitrary_format = false}));
  EXPECT_THAT(ValidateIrValueFormat(testValue, Format::IPV4,
                                    {.allow_arbitrary_format = false}),
              StatusIs(absl::StatusCode::kInvalidArgument));
  EXPECT_OK(ValidateIrValueFormat(testValue, Format::IPV4,
                                  {.allow_arbitrary_format = true}));
  EXPECT_THAT(ValidateIrValueFormat(testValue, Format::IPV6,
                                    {.allow_arbitrary_format = false}),
              StatusIs(absl::StatusCode::kInvalidArgument));
  EXPECT_OK(ValidateIrValueFormat(testValue, Format::IPV6,
                                  {.allow_arbitrary_format = true}));
  EXPECT_THAT(ValidateIrValueFormat(testValue, Format::STRING,
                                    {.allow_arbitrary_format = false}),
              StatusIs(absl::StatusCode::kInvalidArgument));
  EXPECT_OK(ValidateIrValueFormat(testValue, Format::STRING,
                                  {.allow_arbitrary_format = true}));
  EXPECT_THAT(ValidateIrValueFormat(testValue, Format::MAC,
                                    {.allow_arbitrary_format = false}),
              StatusIs(absl::StatusCode::kInvalidArgument));
  EXPECT_OK(ValidateIrValueFormat(testValue, Format::MAC,
                                  {.allow_arbitrary_format = true}));
}

TEST(ValidateIrValueFormatTest, ArbitraryFormatWorksForAllStringCases) {
  IrValue testValue;
  testValue.set_str("0x01");
  EXPECT_OK(ValidateIrValueFormat(testValue, Format::STRING,
                                  {.allow_arbitrary_format = false}));
  EXPECT_THAT(ValidateIrValueFormat(testValue, Format::IPV4,
                                    {.allow_arbitrary_format = false}),
              StatusIs(absl::StatusCode::kInvalidArgument));
  EXPECT_OK(ValidateIrValueFormat(testValue, Format::IPV4,
                                  {.allow_arbitrary_format = true}));
  EXPECT_THAT(ValidateIrValueFormat(testValue, Format::IPV6,
                                    {.allow_arbitrary_format = false}),
              StatusIs(absl::StatusCode::kInvalidArgument));
  EXPECT_OK(ValidateIrValueFormat(testValue, Format::IPV6,
                                  {.allow_arbitrary_format = true}));
  EXPECT_THAT(ValidateIrValueFormat(testValue, Format::HEX_STRING,
                                    {.allow_arbitrary_format = false}),
              StatusIs(absl::StatusCode::kInvalidArgument));
  EXPECT_OK(ValidateIrValueFormat(testValue, Format::HEX_STRING,
                                  {.allow_arbitrary_format = true}));
  EXPECT_THAT(ValidateIrValueFormat(testValue, Format::MAC,
                                    {.allow_arbitrary_format = false}),
              StatusIs(absl::StatusCode::kInvalidArgument));
  EXPECT_OK(ValidateIrValueFormat(testValue, Format::MAC,
                                  {.allow_arbitrary_format = true}));
}

TEST(IsAllZerosTest, TestZeros) {
  EXPECT_TRUE(IsAllZeros("\x00\x00\x00\x00"));
  EXPECT_FALSE(IsAllZeros("\x01\x00\x00\x00"));
}

TEST(IntersectionTest, UnequalLengths) {
  const auto status_or_result =
      Intersection("\x41\x42\x43", "\x41\x42\x43\x44");
  EXPECT_EQ(status_or_result.status().code(),
            absl::StatusCode::kInvalidArgument);
}

TEST(IntersectionTest, NoChange) {
  std::string expected = "\x41\x42\x43";
  ASSERT_OK_AND_ASSIGN(const auto& result,
                       Intersection(expected, "\xff\xff\xff"));
  EXPECT_EQ(result, expected);
}

TEST(IntersectionTest, AllZeros) {
  std::string input = "\x41\x42\x43";
  ASSERT_OK_AND_ASSIGN(const auto& result,
                       Intersection(input, std::string("\x00\x00\x00", 3)));
  EXPECT_TRUE(IsAllZeros(result));
}

TEST(PrefixLenToMaskTest, PrefixLenTooLong) {
  const auto status_or_result = PrefixLenToMask(33, 32);
  EXPECT_EQ(status_or_result.status().code(),
            absl::StatusCode::kInvalidArgument);
}

TEST(PrefixLenToMaskTest, Ipv4Test) {
  ASSERT_OK_AND_ASSIGN(const auto result, PrefixLenToMask(23, 32));
  std::string expected("\xff\xff\xfe\x00", 4);
  EXPECT_EQ(result, expected);
}

TEST(PrefixLenToMaskTest, Ipv6Test) {
  ASSERT_OK_AND_ASSIGN(const auto result, PrefixLenToMask(96, 128));
  std::string expected(
      "\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x00\x00\x00\x00", 16);
  EXPECT_EQ(result, expected);
}

TEST(PrefixLenToMaskTest, GenericValueTest) {
  ASSERT_OK_AND_ASSIGN(const auto result, PrefixLenToMask(23, 33));
  std::string expected("\x01\xff\xff\xfc\x00", 5);
  EXPECT_EQ(result, expected);
}

TEST(ArbitraryByteStringToIrValueTest, Ipv6FullBitwidthTest) {
  constexpr absl::string_view kIp = "0:aaaa:bbbb:cccc:dddd:eeee:ffff:0";
  ASSERT_OK_AND_ASSIGN(netaddr::Ipv6Address ipv6_address,
                       netaddr::Ipv6Address::OfString(kIp));
  EXPECT_THAT(
      ArbitraryByteStringToIrValue(Format::IPV6, /*bitwidth=*/kNumBitsInIpv6,
                                   /*bytes=*/ipv6_address.ToPaddedByteString()),
      IsOkAndHolds(EqualsProto(absl::Substitute(R"pb(ipv6: "$0")pb", kIp))));
}

TEST(ArbitraryByteStringToIrValueTest, EmptyBytestringReturnsError) {
  EXPECT_THAT(
      ArbitraryByteStringToIrValue(Format::IPV6, /*bitwidth=*/kNumBitsInIpv6,
                                   /*bytes=*/""),
      StatusIs(absl::StatusCode::kOutOfRange));
}

TEST(ArbitraryToNormalizedByteString, EmptyBytestringReturnsError) {
  EXPECT_THAT(
      ArbitraryToNormalizedByteString(/*bytes=*/"", /*expected_bitwidth=*/8),
      StatusIs(absl::StatusCode::kOutOfRange));
}

TEST(IrValueToNormalizedByteString, kStrWithEmptyStringReturnsError) {
  IrValue empty_string;
  empty_string.set_str("");
  EXPECT_THAT(IrValueToNormalizedByteString(empty_string, /*bitwidth=*/8),
              StatusIs(absl::StatusCode::kOutOfRange));
}

class Ipv6BitwidthTest : public testing::TestWithParam<int> {};

TEST_P(Ipv6BitwidthTest, ArbitraryByteStringToIrValueReturnsIp) {
  const int bitwidth = GetParam();
  ASSERT_OK_AND_ASSIGN(
      netaddr::Ipv6Address ipv6_address,
      netaddr::Ipv6Address::OfString("0:aaaa:bbbb:cccc:dddd:eeee:ffff:0"));
  ASSERT_OK_AND_ASSIGN(ipv6_address,
                       ipv6_address.MaskForPrefixLength(bitwidth));
  SCOPED_TRACE(absl::Substitute("Expected IP: $0", ipv6_address.ToString()));

  EXPECT_THAT(
      ArbitraryByteStringToIrValue(
          Format::IPV6, /*bitwidth=*/bitwidth,
          /*bytes=*/
          (ipv6_address >> (kNumBitsInIpv6 - bitwidth)).ToPaddedByteString()),
      IsOkAndHolds(EqualsProto(
          absl::Substitute(R"pb(ipv6: "$0")pb", ipv6_address.ToString()))));
}

TEST_P(Ipv6BitwidthTest, IrValueToNormalizedByteString) {
  const int bitwidth = GetParam();
  ASSERT_OK_AND_ASSIGN(
      netaddr::Ipv6Address ipv6_address,
      netaddr::Ipv6Address::OfString("0:aaaa:bbbb:cccc:dddd:eeee:ffff:0"));
  ASSERT_OK_AND_ASSIGN(ipv6_address,
                       ipv6_address.MaskForPrefixLength(bitwidth));
  SCOPED_TRACE(absl::Substitute("IP Address: $0", ipv6_address.ToString()));
  IrValue ir_value;
  ir_value.set_ipv6(ipv6_address.ToString());
  ipv6_address >>= (kNumBitsInIpv6 - bitwidth);

  EXPECT_THAT(IrValueToNormalizedByteString(ir_value, bitwidth),
              IsOkAndHolds(ipv6_address.ToPaddedByteString()));
}

TEST_P(Ipv6BitwidthTest, IrValueToNormalizedByteStringBitwidthTooLargeFails) {
  const int bitwidth = GetParam();
  if (bitwidth == kNumBitsInIpv6) return;
  netaddr::Ipv6Address ipv6_address = netaddr::Ipv6Address::AllOnes();
  ASSERT_OK_AND_ASSIGN(ipv6_address,
                       ipv6_address.MaskForPrefixLength(bitwidth + 1));
  SCOPED_TRACE(absl::Substitute("IP Address: $0", ipv6_address.ToString()));
  IrValue ir_value;
  ir_value.set_ipv6(ipv6_address.ToString());

  EXPECT_THAT(IrValueToNormalizedByteString(ir_value, bitwidth),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST_P(Ipv6BitwidthTest, ArbitraryByteStringToIrValueBitwidthTooLargeFails) {
  const int bitwidth = GetParam();
  if (bitwidth == kNumBitsInIpv6) return;

  netaddr::Ipv6Address ipv6_address = netaddr::Ipv6Address::AllOnes();
  ipv6_address >>= kNumBitsInIpv6 - bitwidth - 1;

  EXPECT_THAT(ArbitraryByteStringToIrValue(Format::IPV6, bitwidth,
                                           ipv6_address.ToPaddedByteString()),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

INSTANTIATE_TEST_SUITE_P(PerBitwidth, Ipv6BitwidthTest,
                         testing::Values(63, 64, 65, 128),
                         testing::PrintToStringParamName());

TEST(AnnotationTests, IsElementDeprecatedTest) {
  std::vector<std::string> annotations_with_deprecated = {
      "@irrelevant", "@deprecated", "@irrelevant2"};
  EXPECT_TRUE(
      IsElementDeprecated(google::protobuf::RepeatedPtrField<std::string>(
          annotations_with_deprecated.begin(),
          annotations_with_deprecated.end())));

  std::vector<std::string> annotations_without_deprecated = {
      "@irrelevant", "@unused", "@irrelevant2"};
  EXPECT_FALSE(
      IsElementDeprecated(google::protobuf::RepeatedPtrField<std::string>(
          annotations_without_deprecated.begin(),
          annotations_without_deprecated.end())));
}

TEST(ShortDescriptiontest, TranslatesIrTableEntryWithActionInvocation) {
  ASSERT_OK_AND_ASSIGN(auto entry,
                       gutil::ParseTextProto<pdpi::IrTableEntry>(R"pb(
                         table_name: "Table1"
                         priority: 12
                         matches {
                           name: "match1"
                           optional { value { hex_str: "0x1234" } }
                         }
                         matches {
                           name: "match2"
                           exact { str: "astring" }
                         }
                         matches {
                           name: "match3"
                           lpm {
                             value { ipv6: "2002::" }
                             prefix_length: 5
                           }
                         }
                         matches {
                           name: "match4"
                           ternary {
                             value { mac: "00:11:22:33:44:55" }
                             mask { mac: "ff:ff:ff:ff:ff:ff" }
                           }
                         }
                         matches {
                           name: "match5"
                           exact {}
                         }
                         action {
                           name: "myaction"
                           params {
                             name: "param1"
                             value { ipv4: "1.2.3.4" }
                           }
                           params {
                             name: "param2"
                             value {}
                           }
                         }
                       )pb"));
  EXPECT_EQ(ShortDescription(entry),
            "Table1|12:matches(match1=0x1234,match2=astring,match3=2002::/"
            "5,match4=00:11:22:33:44:55&ff:ff:ff:ff:ff:ff,match5=):myaction("
            "param1=1.2.3.4,param2=)");
}

TEST(ShortDescriptiontest, TranslatesIrTableEntryWithActionSet) {
  ASSERT_OK_AND_ASSIGN(auto entry,
                       gutil::ParseTextProto<pdpi::IrTableEntry>(R"pb(
                         table_name: "Table1"
                         matches {
                           name: "m"
                           optional { value { str: "s" } }
                         }
                         action_set {
                           actions {
                             weight: 1
                             watch_port: "wpa"
                             action { name: "wpaction" }
                           }
                           actions {
                             weight: 2
                             action {
                               name: "weightaction"
                               params {
                                 name: "param1"
                                 value { str: "stuff" }
                               }
                             }
                           }
                         }
                       )pb"));
  EXPECT_EQ(ShortDescription(entry),
            "Table1|matches(m=s):2[weightaction(param1=stuff)]wpa/1[wpaction]");
}

TEST(ShortDescriptiontest, TranslatesIrTableEntryWithConsistentOrdering) {
  ASSERT_OK_AND_ASSIGN(
      auto base_entry,
      gutil::ParseTextProto<pdpi::IrTableEntry>(R"pb(table_name: "Table1"
                                                     priority: 12)pb"));
  ASSERT_OK_AND_ASSIGN(auto match1, gutil::ParseTextProto<pdpi::IrMatch>(R"pb(
                         name: "match1"
                         optional { value { hex_str: "0x1234" } }
                       )pb"));
  ASSERT_OK_AND_ASSIGN(auto match2, gutil::ParseTextProto<pdpi::IrMatch>(R"pb(
                         name: "match2"
                         optional { value { str: "astring" } }
                       )pb"));
  ASSERT_OK_AND_ASSIGN(auto match3, gutil::ParseTextProto<pdpi::IrMatch>(R"pb(
                         name: "match3"
                         lpm {
                           value { ipv6: "2002::" }
                           prefix_length: 5
                         }
                       )pb"));

  ASSERT_OK_AND_ASSIGN(
      auto param1,
      gutil::ParseTextProto<pdpi::IrActionInvocation::IrActionParam>(
          R"pb(name: "param1"
               value { str: "p1" })pb"));
  ASSERT_OK_AND_ASSIGN(
      auto param2,
      gutil::ParseTextProto<pdpi::IrActionInvocation::IrActionParam>(
          R"pb(name: "param2"
               value { str: "p2" })pb"));
  ASSERT_OK_AND_ASSIGN(
      auto param3,
      gutil::ParseTextProto<pdpi::IrActionInvocation::IrActionParam>(
          R"pb(name: "param3"
               value { str: "p3" })pb"));
  ASSERT_OK_AND_ASSIGN(auto param_action,
                       gutil::ParseTextProto<pdpi::IrActionSetInvocation>(
                           R"pb(weight: 10
                                watch_port: "wp_param"
                                action { name: "param_action" })pb"));
  ASSERT_OK_AND_ASSIGN(auto action1,
                       gutil::ParseTextProto<pdpi::IrActionSetInvocation>(
                           R"pb(weight: 1
                                watch_port: "wpa"
                                action { name: "action1" })pb"));
  ASSERT_OK_AND_ASSIGN(auto action2,
                       gutil::ParseTextProto<pdpi::IrActionSetInvocation>(
                           R"pb(weight: 2
                                watch_port: "wpb"
                                action { name: "action2" })pb"));
  ASSERT_OK_AND_ASSIGN(auto action3,
                       gutil::ParseTextProto<pdpi::IrActionSetInvocation>(
                           R"pb(weight: 3
                                watch_port: "wpc"
                                action { name: "action3" })pb"));

  IrActionSetInvocation action123 = param_action;
  *action123.mutable_action()->add_params() = param1;
  *action123.mutable_action()->add_params() = param2;
  *action123.mutable_action()->add_params() = param3;
  IrTableEntry entry123 = base_entry;
  *entry123.add_matches() = match1;
  *entry123.add_matches() = match2;
  *entry123.add_matches() = match3;
  *entry123.mutable_action_set()->add_actions() = action1;
  *entry123.mutable_action_set()->add_actions() = action2;
  *entry123.mutable_action_set()->add_actions() = action3;
  *entry123.mutable_action_set()->add_actions() = action123;

  IrActionSetInvocation action312 = param_action;
  *action312.mutable_action()->add_params() = param3;
  *action312.mutable_action()->add_params() = param1;
  *action312.mutable_action()->add_params() = param2;
  IrTableEntry entry312 = base_entry;
  *entry312.add_matches() = match3;
  *entry312.add_matches() = match1;
  *entry312.add_matches() = match2;
  *entry312.mutable_action_set()->add_actions() = action3;
  *entry312.mutable_action_set()->add_actions() = action1;
  *entry312.mutable_action_set()->add_actions() = action2;
  *entry312.mutable_action_set()->add_actions() = action312;

  EXPECT_EQ(ShortDescription(entry123), ShortDescription(entry312));
}

}  // namespace
}  // namespace pdpi
