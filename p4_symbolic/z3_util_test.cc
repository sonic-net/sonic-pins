#include "p4_symbolic/z3_util.h"

#include "gmock/gmock.h"
#include "gtest/gtest.h"

namespace p4_symbolic {
namespace {

TEST(Z3ValueStringToInt, WorksForBoolStrings) {
  ASSERT_EQ(Z3ValueStringToInt("true"), 1);
  ASSERT_EQ(Z3ValueStringToInt("false"), 0);
}

TEST(Z3ValueStringToInt, WorksForBinaryStrings) {
  ASSERT_EQ(Z3ValueStringToInt("#b10"), 2);
  ASSERT_EQ(Z3ValueStringToInt("#b01"), 1);
}

TEST(Z3ValueStringToInt, WorksForHexStrings) {
  ASSERT_EQ(Z3ValueStringToInt("#x10"), 16);
  ASSERT_EQ(Z3ValueStringToInt("#xff"), 255);
  ASSERT_EQ(Z3ValueStringToInt("#x9"), 9);
}

TEST(Z3ValueStringToInt, WorksForDecimalStrings) {
  ASSERT_EQ(Z3ValueStringToInt("10"), 10);
  ASSERT_EQ(Z3ValueStringToInt("900"), 900);
}

}  // namespace
}  // namespace p4_symbolic
