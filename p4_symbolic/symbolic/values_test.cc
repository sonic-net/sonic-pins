#include "p4_symbolic/symbolic/values.h"

#include <cstdint>
#include <string>

#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/status_matchers.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_symbolic/z3_util.h"
#include "z3++.h"

namespace p4_symbolic::symbolic::values {
namespace {

using gutil::StatusIs;

constexpr char kFieldName[] = "dummy_field_name";
constexpr char kFieldType[] = "dummy_field_type";

TEST(TranslateValueToP4RT, ReverseTranslatedValuesAreEqualToTheOriginalOnes) {
  constexpr int kNumIds = 256;
  z3::context z3_context;

  // Prepare the translator and expected values.
  P4RuntimeTranslator translator;
  absl::flat_hash_map<std::string, std::string> z3_value_to_id;
  for (int i = 0; i < kNumIds; i++) {
    const std::string id = absl::StrCat("id-", i);
    pdpi::IrValue ir_value;
    ir_value.set_str(id);
    ASSERT_OK_AND_ASSIGN(
        z3::expr expr, FormatP4RTValue(ir_value, kFieldName, kFieldType,
                                       /*bitwidth=*/0, z3_context, translator));
    z3_value_to_id[expr.to_string()] = id;
  }

  // Check that the reverse translation is as expected.
  for (const auto& [z3_value, expected_id] : z3_value_to_id) {
    ASSERT_OK_AND_ASSIGN(const auto translated_value,
                         TranslateZ3ValueStringToP4RT(z3_value, kFieldName,
                                                      kFieldType, translator));
    const std::string& actual_id = translated_value.first;
    ASSERT_THAT(actual_id, testing::Eq(expected_id));
  }
}

// Make sure the code conforms to the peculiarities of PDPI's value conversion.
TEST(FormatP4RTValue, WorksFor64BitIPv6) {
  P4RuntimeTranslator translator;
  z3::context z3_context;
  ASSERT_OK_AND_ASSIGN(auto ir_value,
                       gutil::ParseTextProto<pdpi::IrValue>(
                           R"pb(ipv6: "0000:ffff:ffff:ffff::")pb"));
  ASSERT_OK_AND_ASSIGN(
      z3::expr z3_expr,
      FormatP4RTValue(ir_value, kFieldName, kFieldType,
                      /*bitwidth=*/64, z3_context, translator));
  ASSERT_EQ(Z3ValueStringToInt(z3_expr.to_string()), 0x0000'ffff'ffff'ffffULL);
}

TEST(FormatP4RTValue, WorksForIpv4) {
  P4RuntimeTranslator translator;
  z3::context z3_context;
  ASSERT_OK_AND_ASSIGN(auto ir_value, gutil::ParseTextProto<pdpi::IrValue>(
                                          R"pb(ipv4: "127.0.0.1")pb"));
  ASSERT_OK_AND_ASSIGN(
      z3::expr z3_expr,
      FormatP4RTValue(ir_value, kFieldName, kFieldType,
                      /*bitwidth=*/32, z3_context, translator));
  ASSERT_EQ(Z3ValueStringToInt(z3_expr.to_string()), 0x7f000001);
}

TEST(FormatP4RTValue, WorksForMac) {
  P4RuntimeTranslator translator;
  z3::context z3_context;
  ASSERT_OK_AND_ASSIGN(auto ir_value, gutil::ParseTextProto<pdpi::IrValue>(
                                          R"pb(mac: "01:02:03:04:05:06")pb"));
  ASSERT_OK_AND_ASSIGN(
      z3::expr z3_expr,
      FormatP4RTValue(ir_value, kFieldName, kFieldType,
                      /*bitwidth=*/48, z3_context, translator));
  ASSERT_EQ(Z3ValueStringToInt(z3_expr.to_string()), 0x01'02'03'04'05'06ULL);
}

TEST(FormatP4RTValue, WorksForHexString) {
  P4RuntimeTranslator translator;
  z3::context z3_context;
  ASSERT_OK_AND_ASSIGN(auto ir_value, gutil::ParseTextProto<pdpi::IrValue>(
                                          R"pb(hex_str: "0xabcd")pb"));
  ASSERT_OK_AND_ASSIGN(
      z3::expr z3_expr,
      FormatP4RTValue(ir_value, kFieldName, kFieldType,
                      /*bitwidth=*/16, z3_context, translator));
  ASSERT_EQ(Z3ValueStringToInt(z3_expr.to_string()), 0xabcd);
}

TEST(FormatP4RTValue, FailsForStringWithNonZeroBitwidth) {
  P4RuntimeTranslator translator;
  z3::context z3_context;
  ASSERT_OK_AND_ASSIGN(auto ir_value, gutil::ParseTextProto<pdpi::IrValue>(
                                          R"pb(str: "dummy_value")pb"));
  ASSERT_THAT(FormatP4RTValue(ir_value, kFieldName, kFieldType,
                              /*bitwidth=*/16, z3_context, translator),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

constexpr char kDummyString1[] = "a";
constexpr char kDummyString2[] = "b";
constexpr int kDummyId1 = 10;

TEST(IdAllocatorTest, AssignedIdsAreUnique) {
  IdAllocator allocator(TranslationData{.dynamic_translation = true});
  ASSERT_OK_AND_ASSIGN(const uint64_t id_1,
                       allocator.AllocateId(kDummyString1));
  ASSERT_OK_AND_ASSIGN(const uint64_t id_2,
                       allocator.AllocateId(kDummyString2));
  ASSERT_NE(id_1, id_2);
}

TEST(IdAllocatorTest, ReverseTranslationYieldsOriginalString) {
  IdAllocator allocator(TranslationData{.dynamic_translation = true});
  ASSERT_OK_AND_ASSIGN(const uint64_t id_1,
                       allocator.AllocateId(kDummyString1));
  ASSERT_OK_AND_ASSIGN(const std::string string_1, allocator.IdToString(id_1));
  ASSERT_EQ(string_1, kDummyString1);
}

TEST(IdAllocatorTest, StaticMappingWorksForExistingString) {
  IdAllocator allocator(TranslationData{
      .static_mapping = {{kDummyString1, kDummyId1}},
      .dynamic_translation = true,
  });
  ASSERT_OK_AND_ASSIGN(const std::string string_1,
                       allocator.IdToString(kDummyId1));
  ASSERT_EQ(string_1, kDummyString1);
  ASSERT_OK_AND_ASSIGN(const uint64_t id, allocator.AllocateId(kDummyString1));
  ASSERT_EQ(id, kDummyId1);
}

TEST(IdAllocatorTest, StaticMappingWithDynamicAllocationWorksForNewString) {
  IdAllocator allocator(TranslationData{
      .static_mapping = {{kDummyString1, kDummyId1}},
      .dynamic_translation = true,
  });
  ASSERT_OK_AND_ASSIGN(const uint64_t id_2,
                       allocator.AllocateId(kDummyString2));
  ASSERT_NE(id_2, kDummyId1);
  ASSERT_OK_AND_ASSIGN(const std::string string_2, allocator.IdToString(id_2));
  ASSERT_EQ(string_2, kDummyString2);
}

TEST(IdAllocatorTest, StaticMappingWithoutDynamicAllocationFailForNewString) {
  IdAllocator allocator(TranslationData{
      .static_mapping = {{kDummyString1, kDummyId1}},
      .dynamic_translation = false,
  });
  ASSERT_THAT(allocator.AllocateId(kDummyString2),
              gutil::StatusIs(absl::StatusCode::kInvalidArgument));
}

}  // namespace
}  // namespace p4_symbolic::symbolic::values
