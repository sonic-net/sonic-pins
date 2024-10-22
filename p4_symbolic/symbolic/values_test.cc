#include "p4_symbolic/symbolic/values.h"

#include "absl/container/flat_hash_map.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_symbolic/z3_util.h"

namespace p4_symbolic::symbolic::values {
namespace {

using gutil::StatusIs;

constexpr char kFieldName[] = "dummy_field_name";
constexpr char kFieldType[] = "dummy_field_type";

TEST(TranslateValueToP4RT, ReverseTranslatedValuesAreEqualToTheOriginalOnes) {
  constexpr int kNumIds = 256;

  // Prepare the translator and expected values.
  P4RuntimeTranslator translator;
  absl::flat_hash_map<std::string, std::string> z3_value_to_id;
  for (int i = 0; i < kNumIds; i++) {
    const std::string id = absl::StrCat("id-", i);
    pdpi::IrValue ir_value;
    ir_value.set_str(id);
    ASSERT_OK_AND_ASSIGN(z3::expr expr,
                         FormatP4RTValue(kFieldName, kFieldType, ir_value,
                                         /*bitwidth=*/0, &translator));
    z3_value_to_id[expr.to_string()] = id;
  }

  // Check that the reverse translation is as expected.
  for (const auto& [z3_value, expected_id] : z3_value_to_id) {
    ASSERT_OK_AND_ASSIGN(
        const std::string actual_id,
        TranslateValueToP4RT(kFieldName, z3_value, translator));
    ASSERT_THAT(actual_id, testing::Eq(expected_id));
  }
}

// Make sure the code conforms to the pecularities of PDPI's value conversion.
TEST(FormatP4RTValue, WorksFor64BitIPv6) {
  P4RuntimeTranslator trasnlator;
  ASSERT_OK_AND_ASSIGN(auto ir_value,
                       gutil::ParseTextProto<pdpi::IrValue>(
                           R"pb(ipv6: "0000:ffff:ffff:ffff::")pb"));
  ASSERT_OK_AND_ASSIGN(z3::expr z3_expr,
                       FormatP4RTValue(kFieldName, kFieldType, ir_value,
                                       /*bitwidth=*/64, &trasnlator));
  ASSERT_EQ(Z3ValueStringToInt(z3_expr.to_string()), 0x0000'ffff'ffff'ffffULL);
}

TEST(FormatP4RTValue, WorksForIpv4) {
  P4RuntimeTranslator trasnlator;
  ASSERT_OK_AND_ASSIGN(auto ir_value, gutil::ParseTextProto<pdpi::IrValue>(
                                          R"pb(ipv4: "127.0.0.1")pb"));
  ASSERT_OK_AND_ASSIGN(z3::expr z3_expr,
                       FormatP4RTValue(kFieldName, kFieldType, ir_value,
                                       /*bitwidth=*/32, &trasnlator));
  ASSERT_EQ(Z3ValueStringToInt(z3_expr.to_string()), 0x7f000001);
}

TEST(FormatP4RTValue, WorksForMac) {
  P4RuntimeTranslator trasnlator;
  ASSERT_OK_AND_ASSIGN(auto ir_value, gutil::ParseTextProto<pdpi::IrValue>(
                                          R"pb(mac: "01:02:03:04:05:06")pb"));
  ASSERT_OK_AND_ASSIGN(z3::expr z3_expr,
                       FormatP4RTValue(kFieldName, kFieldType, ir_value,
                                       /*bitwidth=*/48, &trasnlator));
  ASSERT_EQ(Z3ValueStringToInt(z3_expr.to_string()), 0x01'02'03'04'05'06ULL);
}

TEST(FormatP4RTValue, WorksForHexString) {
  P4RuntimeTranslator trasnlator;
  ASSERT_OK_AND_ASSIGN(auto ir_value, gutil::ParseTextProto<pdpi::IrValue>(
                                          R"pb(hex_str: "0xabcd")pb"));
  ASSERT_OK_AND_ASSIGN(z3::expr z3_expr,
                       FormatP4RTValue(kFieldName, kFieldType, ir_value,
                                       /*bitwidth=*/16, &trasnlator));
  ASSERT_EQ(Z3ValueStringToInt(z3_expr.to_string()), 0xabcd);
}

TEST(FormatP4RTValue, FailsForStringWithNonZeroBitwidth) {
  P4RuntimeTranslator trasnlator;
  ASSERT_OK_AND_ASSIGN(auto ir_value, gutil::ParseTextProto<pdpi::IrValue>(
                                          R"pb(str: "dummy_value")pb"));
  ASSERT_THAT(FormatP4RTValue(kFieldName, kFieldType, ir_value,
                              /*bitwidth=*/16, &trasnlator),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

}  // namespace
}  // namespace p4_symbolic::symbolic::values
