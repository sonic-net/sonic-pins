#include "p4_symbolic/symbolic/values.h"

#include "absl/container/flat_hash_map.h"
#include "absl/strings/str_cat.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "p4_pdpi/ir.pb.h"

namespace p4_symbolic::symbolic::values {
namespace {

TEST(TranslateValueToP4RT, ReverseTranslatedValuesAreEqualToTheOriginalOnes) {
  constexpr int kNumIds = 256;
  const std::string kFieldName = "dummy_field_name";
  const std::string kFieldType = "dummy_field_type";

  // Prepare the translator and expected values.
  P4RuntimeTranslator translator;
  absl::flat_hash_map<std::string, std::string> z3_value_to_id;
  for (int i = 0; i < kNumIds; i++) {
    const std::string id = absl::StrCat("id-", i);
    pdpi::IrValue ir_value;
    ir_value.set_str(id);
    ASSERT_OK_AND_ASSIGN(z3::expr expr, FormatP4RTValue(kFieldName, kFieldType,
                                                        ir_value, &translator));
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

}  // namespace
}  // namespace p4_symbolic::symbolic::values
