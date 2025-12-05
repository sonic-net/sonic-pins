#include "p4_symbolic/z3_util.h"

#include <bitset>
#include <cstdint>
#include <string>

#include "absl/numeric/int128.h"
#include "absl/status/status.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status_matchers.h"
#include "p4_infra/string_encodings/bit_string.h"
#include "z3++.h"

namespace p4_symbolic {
namespace {

using ::gutil::StatusIs;

TEST(EvalZ3Bool, CheckEvalZ3Bool) {
  z3::context ctx;
  z3::solver solver(ctx);

  // Construct expressions.
  z3::expr expr1 = ctx.bool_val(true);
  z3::expr expr2 = ctx.bool_val(false);
  z3::expr expr3 = ctx.bool_val(true) && ctx.bool_val(false);
  z3::expr expr4 = ctx.bool_val(true) || ctx.bool_val(false);
  z3::expr expr5 = ctx.int_val(0);
  z3::expr expr6 = ctx.bv_val(1, 1);

  z3::check_result check_result = solver.check();
  ASSERT_EQ(check_result, z3::sat);
  z3::model model = solver.get_model();

  // Check for evaluated values.
  ASSERT_OK_AND_ASSIGN(bool ans1, EvalZ3Bool(expr1, model));
  EXPECT_TRUE(ans1);
  ASSERT_OK_AND_ASSIGN(bool ans2, EvalZ3Bool(expr2, model));
  EXPECT_FALSE(ans2);
  ASSERT_OK_AND_ASSIGN(bool ans3, EvalZ3Bool(expr3, model));
  EXPECT_FALSE(ans3);
  ASSERT_OK_AND_ASSIGN(bool ans4, EvalZ3Bool(expr4, model));
  EXPECT_TRUE(ans4);
  EXPECT_THAT(EvalZ3Bool(expr5, model),
              StatusIs(absl::StatusCode::kInvalidArgument));
  EXPECT_THAT(EvalZ3Bool(expr6, model),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(EvalZ3Int, CheckEvalZ3Int) {
  z3::context ctx;
  z3::solver solver(ctx);

  // Construct expressions.
  z3::expr expr1 = ctx.int_val(0);
  z3::expr expr2 = ctx.int_val(1);
  z3::expr expr3 = ctx.int_val(1000);
  z3::expr expr4 = ctx.int_val(1) + ctx.int_val(-1);
  z3::expr expr5 = ctx.int_val(1) - ctx.int_val(1);
  z3::expr expr6 = ctx.bv_val(1, 1);

  z3::check_result check_result = solver.check();
  ASSERT_EQ(check_result, z3::sat);
  z3::model model = solver.get_model();

  // Check for evaluated values.
  ASSERT_OK_AND_ASSIGN(int ans1, EvalZ3Int(expr1, model));
  EXPECT_EQ(ans1, 0);
  ASSERT_OK_AND_ASSIGN(int ans2, EvalZ3Int(expr2, model));
  EXPECT_EQ(ans2, 1);
  ASSERT_OK_AND_ASSIGN(int ans3, EvalZ3Int(expr3, model));
  EXPECT_EQ(ans3, 1000);
  ASSERT_OK_AND_ASSIGN(int ans4, EvalZ3Int(expr4, model));
  EXPECT_EQ(ans4, 0);
  ASSERT_OK_AND_ASSIGN(int ans5, EvalZ3Int(expr5, model));
  EXPECT_EQ(ans5, 0);
  EXPECT_THAT(EvalZ3Int(expr6, model),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(EvalAndAppendZ3BitvectorToBitString,
     CheckEvalAndAppendZ3BitvectorToBitString) {
  z3::context ctx;
  z3::solver solver(ctx);

  // Construct expressions.
  z3::expr expr1 = ctx.bv_val(0, 1);
  z3::expr expr2 = ctx.bv_val(0, 4);
  z3::expr expr3 = ctx.bv_val(0, 7);
  z3::expr expr4 = ctx.int_val(1);

  z3::check_result check_result = solver.check();
  ASSERT_EQ(check_result, z3::sat);
  z3::model model = solver.get_model();

  // Check for evaluated values.
  string_encodings::BitString ans1, ans2, ans3, ans4;
  ASSERT_OK(EvalAndAppendZ3BitvectorToBitString(ans1, expr1, model));
  ASSERT_OK(EvalAndAppendZ3BitvectorToBitString(ans2, expr2, model));
  ASSERT_OK(EvalAndAppendZ3BitvectorToBitString(ans3, expr3, model));
  EXPECT_THAT(EvalAndAppendZ3BitvectorToBitString(ans4, expr4, model),
              StatusIs(absl::StatusCode::kInvalidArgument));
  EXPECT_EQ(ans1.size(), 1);
  ASSERT_OK_AND_ASSIGN(std::bitset<1> bit, ans1.ConsumeBitset<1>());
  EXPECT_FALSE(bit.test(0));
  ASSERT_OK_AND_ASSIGN(std::string hex2, ans2.ToHexString());
  EXPECT_EQ(hex2, "0x0");
  ASSERT_OK_AND_ASSIGN(std::string hex3, ans3.ToHexString());
  EXPECT_EQ(hex3, "0x00");
}

TEST(EvalZ3BitvectorToUInt, CheckEvalZ3BitvectorToUInt) {
  z3::context ctx;
  z3::solver solver(ctx);

  // Construct expressions.
  z3::expr expr1 = ctx.int_val(0);
  z3::expr expr2 = ctx.bv_val(0, 65);
  z3::expr expr3 = ctx.bv_val(0, 64);
  z3::expr expr4 = ctx.bv_val(42, 8);

  z3::check_result check_result = solver.check();
  ASSERT_EQ(check_result, z3::sat);
  z3::model model = solver.get_model();

  // Check for evaluated values.
  EXPECT_THAT(EvalZ3BitvectorToUInt64(expr1, model),
              StatusIs(absl::StatusCode::kInvalidArgument));
  EXPECT_THAT(EvalZ3BitvectorToUInt64(expr2, model),
              StatusIs(absl::StatusCode::kInvalidArgument));
  ASSERT_OK_AND_ASSIGN(uint64_t ans3, EvalZ3BitvectorToUInt64(expr3, model));
  EXPECT_EQ(ans3, 0);
  ASSERT_OK_AND_ASSIGN(uint64_t ans4, EvalZ3BitvectorToUInt64(expr4, model));
  EXPECT_EQ(ans4, 42);
}

TEST(EvalZ3BitvectorToUInt128, CheckEvalZ3BitvectorToUInt128) {
  z3::context ctx;
  z3::solver solver(ctx);

  // Construct expressions.
  z3::expr expr1 = ctx.int_val(0);
  z3::expr expr2 = ctx.bv_val(0, 129);
  z3::expr expr3 = ctx.bv_val(0, 128);
  z3::expr expr4 = ctx.bv_val(42, 32);
  z3::expr expr5 = ctx.bv_val(42, 31);
  z3::expr expr6 = z3::shl(ctx.bv_val(1, 65), 64);

  z3::check_result check_result = solver.check();
  ASSERT_EQ(check_result, z3::sat);
  z3::model model = solver.get_model();

  // Check for evaluated values.
  EXPECT_THAT(EvalZ3BitvectorToUInt128(expr1, model),
              StatusIs(absl::StatusCode::kInvalidArgument));
  EXPECT_THAT(EvalZ3BitvectorToUInt128(expr2, model),
              StatusIs(absl::StatusCode::kInvalidArgument));
  ASSERT_OK_AND_ASSIGN(absl::uint128 ans3,
                       EvalZ3BitvectorToUInt128(expr3, model));
  EXPECT_EQ(ans3, absl::MakeUint128(0, 0));
  ASSERT_OK_AND_ASSIGN(absl::uint128 ans4,
                       EvalZ3BitvectorToUInt128(expr4, model));
  EXPECT_EQ(ans4, absl::MakeUint128(0, 42));
  ASSERT_OK_AND_ASSIGN(absl::uint128 ans5,
                       EvalZ3BitvectorToUInt128(expr5, model));
  EXPECT_EQ(ans5, absl::MakeUint128(0, 42));
  ASSERT_OK_AND_ASSIGN(absl::uint128 ans6,
                       EvalZ3BitvectorToUInt128(expr6, model));
  EXPECT_EQ(ans6, absl::MakeUint128(1, 0));
}

TEST(HexStringToZ3Bitvector, HexStringWithoutBitWidth) {
  z3::context ctx;
  z3::solver solver(ctx);

  // Construct expressions.
  ASSERT_OK_AND_ASSIGN(z3::expr bv1, HexStringToZ3Bitvector(ctx, "0x0001"));
  ASSERT_OK_AND_ASSIGN(z3::expr bv2, HexStringToZ3Bitvector(ctx, "0xdead"));

  z3::check_result check_result = solver.check();
  ASSERT_EQ(check_result, z3::sat);
  z3::model model = solver.get_model();

  // Check for expressions.
  ASSERT_TRUE(bv1.is_bv());
  ASSERT_TRUE(bv2.is_bv());
  EXPECT_EQ(bv1.get_sort().bv_size(), 1);
  EXPECT_EQ(bv2.get_sort().bv_size(), 16);
  ASSERT_OK_AND_ASSIGN(uint64_t ans1, EvalZ3BitvectorToUInt64(bv1, model));
  ASSERT_OK_AND_ASSIGN(uint64_t ans2, EvalZ3BitvectorToUInt64(bv2, model));
  EXPECT_EQ(ans1, 1);
  EXPECT_EQ(ans2, 0xdead);
}

TEST(HexStringToZ3Bitvector, HexStringWithBitWidth) {
  z3::context ctx;
  z3::solver solver(ctx);

  // Construct expressions.
  ASSERT_OK_AND_ASSIGN(z3::expr bv1, HexStringToZ3Bitvector(ctx, "0x0001", 16));
  ASSERT_OK_AND_ASSIGN(z3::expr bv2, HexStringToZ3Bitvector(ctx, "0xdead", 17));

  z3::check_result check_result = solver.check();
  ASSERT_EQ(check_result, z3::sat);
  z3::model model = solver.get_model();

  // Check for expressions.
  ASSERT_TRUE(bv1.is_bv());
  ASSERT_TRUE(bv2.is_bv());
  EXPECT_EQ(bv1.get_sort().bv_size(), 16);
  EXPECT_EQ(bv2.get_sort().bv_size(), 17);
  ASSERT_OK_AND_ASSIGN(uint64_t ans1, EvalZ3BitvectorToUInt64(bv1, model));
  ASSERT_OK_AND_ASSIGN(uint64_t ans2, EvalZ3BitvectorToUInt64(bv2, model));
  EXPECT_EQ(ans1, 1);
  EXPECT_EQ(ans2, 0xdead);
}

TEST(HexStringToZ3Bitvector, HexStringWithBitWidthThatIsTooShort) {
  z3::context ctx;
  z3::solver solver(ctx);

  // Construct expressions.
  ASSERT_OK_AND_ASSIGN(z3::expr bv1, HexStringToZ3Bitvector(ctx, "0xdead", 8));
  ASSERT_OK_AND_ASSIGN(z3::expr bv2, HexStringToZ3Bitvector(ctx, "0xbeef", 4));

  z3::check_result check_result = solver.check();
  ASSERT_EQ(check_result, z3::sat);
  z3::model model = solver.get_model();

  // Check for expressions.
  ASSERT_TRUE(bv1.is_bv());
  ASSERT_TRUE(bv2.is_bv());
  EXPECT_EQ(bv1.get_sort().bv_size(), 8);
  EXPECT_EQ(bv2.get_sort().bv_size(), 4);
  ASSERT_OK_AND_ASSIGN(uint64_t ans1, EvalZ3BitvectorToUInt64(bv1, model));
  ASSERT_OK_AND_ASSIGN(uint64_t ans2, EvalZ3BitvectorToUInt64(bv2, model));
  EXPECT_EQ(ans1, 0xad);
  EXPECT_EQ(ans2, 0xf);
}

TEST(Z3ValueStringToInt, WorksForBoolStrings) {
  EXPECT_EQ(Z3ValueStringToInt("true"), 1);
  EXPECT_EQ(Z3ValueStringToInt("false"), 0);
}

TEST(Z3ValueStringToInt, WorksForBinaryStrings) {
  EXPECT_EQ(Z3ValueStringToInt("#b10"), 2);
  EXPECT_EQ(Z3ValueStringToInt("#b01"), 1);
}

TEST(Z3ValueStringToInt, WorksForHexStrings) {
  EXPECT_EQ(Z3ValueStringToInt("#x10"), 16);
  EXPECT_EQ(Z3ValueStringToInt("#xff"), 255);
  EXPECT_EQ(Z3ValueStringToInt("#x9"), 9);
}

TEST(Z3ValueStringToInt, WorksForDecimalStrings) {
  EXPECT_EQ(Z3ValueStringToInt("10"), 10);
  EXPECT_EQ(Z3ValueStringToInt("900"), 900);
}

TEST(AppendZ3ValueStringToBitString, InvalidZ3BitvectorValue) {
  string_encodings::BitString bit_string;
  EXPECT_THAT(AppendZ3ValueStringToBitString(bit_string, "9527", 16),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(AppendZ3ValueStringToBitString, HexStringBitvector) {
  string_encodings::BitString bit_string;
  ASSERT_OK(AppendZ3ValueStringToBitString(bit_string, "#x9527", 16));
  ASSERT_OK_AND_ASSIGN(std::string hex_string, bit_string.ToHexString());
  EXPECT_EQ(hex_string, "0x9527");
}

TEST(AppendZ3ValueStringToBitString, BitStringBitvector) {
  string_encodings::BitString bit_string;
  ASSERT_OK(
      AppendZ3ValueStringToBitString(bit_string, "#b1001010100100111", 16));
  ASSERT_OK_AND_ASSIGN(std::string hex_string, bit_string.ToHexString());
  EXPECT_EQ(hex_string, "0x9527");
}

}  // namespace
}  // namespace p4_symbolic
