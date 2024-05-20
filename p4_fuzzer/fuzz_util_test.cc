#include "p4_fuzzer/fuzz_util.h"

#include <memory>

#include "gtest/gtest.h"
#include "gutil/proto.h"
#include "p4_fuzzer/fuzzer.pb.h"
#include "p4_fuzzer/mutation.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/pd.h"

namespace p4_fuzzer {
namespace {

TEST(FuzzUtilTest, SetUnusedBitsToZeroInThreeBytes) {
  std::string data("\xff\xff\xff", 3);
  EXPECT_EQ(SetUnusedBitsToZero(24, data), std::string("\xff\xff\xff", 3));
  EXPECT_EQ(SetUnusedBitsToZero(23, data), std::string("\x7f\xff\xff", 3));
  EXPECT_EQ(SetUnusedBitsToZero(22, data), std::string("\x3f\xff\xff", 3));
  EXPECT_EQ(SetUnusedBitsToZero(21, data), std::string("\x1f\xff\xff", 3));
  EXPECT_EQ(SetUnusedBitsToZero(20, data), std::string("\x0f\xff\xff", 3));
  EXPECT_EQ(SetUnusedBitsToZero(16, data), std::string("\x00\xff\xff", 3));
  EXPECT_EQ(SetUnusedBitsToZero(15, data), std::string("\x00\x7f\xff", 3));
  EXPECT_EQ(SetUnusedBitsToZero(14, data), std::string("\x00\x3f\xff", 3));
  EXPECT_EQ(SetUnusedBitsToZero(13, data), std::string("\x00\x1f\xff", 3));
  EXPECT_EQ(SetUnusedBitsToZero(12, data), std::string("\x00\x0f\xff", 3));
  EXPECT_EQ(SetUnusedBitsToZero(3, data), std::string("\x00\x00\x07", 3));
  EXPECT_EQ(SetUnusedBitsToZero(2, data), std::string("\x00\x00\x03", 3));
  EXPECT_EQ(SetUnusedBitsToZero(1, data), std::string("\x00\x00\x01", 3));
  EXPECT_EQ(SetUnusedBitsToZero(0, data), std::string("\x00\x00\x00", 3));
}

TEST(FuzzUtilTest, SetUnusedBitsToZeroInNineBytes) {
  std::string data("\xff\xff\xff\xff\xff\xff\xff\xff\xff", 9);
  EXPECT_EQ(SetUnusedBitsToZero(72, data),
            std::string("\xff\xff\xff\xff\xff\xff\xff\xff\xff", 9));
  EXPECT_EQ(SetUnusedBitsToZero(71, data),
            std::string("\x7f\xff\xff\xff\xff\xff\xff\xff\xff", 9));
  EXPECT_EQ(SetUnusedBitsToZero(65, data),
            std::string("\x01\xff\xff\xff\xff\xff\xff\xff\xff", 9));
  EXPECT_EQ(SetUnusedBitsToZero(64, data),
            std::string("\x00\xff\xff\xff\xff\xff\xff\xff\xff", 9));
  EXPECT_EQ(SetUnusedBitsToZero(63, data),
            std::string("\x00\x7f\xff\xff\xff\xff\xff\xff\xff", 9));
  EXPECT_EQ(SetUnusedBitsToZero(33, data),
            std::string("\x00\x00\x00\x00\x01\xff\xff\xff\xff", 9));
  EXPECT_EQ(SetUnusedBitsToZero(32, data),
            std::string("\x00\x00\x00\x00\x00\xff\xff\xff\xff", 9));
  EXPECT_EQ(SetUnusedBitsToZero(31, data),
            std::string("\x00\x00\x00\x00\x00\x7f\xff\xff\xff", 9));
  EXPECT_EQ(SetUnusedBitsToZero(9, data),
            std::string("\x00\x00\x00\x00\x00\x00\x00\x01\xff", 9));
  EXPECT_EQ(SetUnusedBitsToZero(8, data),
            std::string("\x00\x00\x00\x00\x00\x00\x00\x00\xff", 9));
  EXPECT_EQ(SetUnusedBitsToZero(7, data),
            std::string("\x00\x00\x00\x00\x00\x00\x00\x00\x7f", 9));
  EXPECT_EQ(SetUnusedBitsToZero(0, data),
            std::string("\x00\x00\x00\x00\x00\x00\x00\x00\x00", 9));
}

TEST(FuzzUtilTest, BitsToUint64) {
  EXPECT_EQ(BitsToUint64(std::string("\0\0\0\0\0\0\0\x63", 8)), 0x63);
  EXPECT_EQ(BitsToUint64(std::string("\0\0\0\0\0\0\x30\x63", 8)), 0x3063);
  EXPECT_EQ(BitsToUint64(std::string("\x01\x02\x03\x04\x05\x06\x07\x08", 8)),
            0x0102030405060708);
}

TEST(FuzzUtilTest, FuzzBitsStringSize) {
  struct TestCase {
    int bits;
    int bytes;
  } test_cases[] = {{1, 1},  {5, 1},  {7, 1},  {8, 1},    {9, 2},
                    {10, 2}, {16, 2}, {17, 3}, {128, 16}, {129, 17}};

  absl::BitGen gen;
  for (auto test_case : test_cases) {
    std::string data = FuzzBits(&gen, test_case.bits);
    EXPECT_EQ(data.size(), test_case.bytes)
        << "bits: " << test_case.bits << " data: '" << data << "'";
  }
}

TEST(FuzzUtilTest, FuzzBitsStringPaddingWorks) {
  absl::BitGen gen;
  for (int i = 0; i < 100; ++i) {
    std::string data = FuzzBits(&gen, /*bits=*/3);
    ASSERT_EQ(data.size(), 1);
    EXPECT_EQ(data[0] & 0xf8, 0);
  }
}

TEST(FuzzUtilTest, FuzzUint64SmallInRange) {
  absl::BitGen gen;
  for (int i = 0; i < 10; ++i) {
    EXPECT_LE(FuzzUint64(&gen, /*bits=*/1), 1);
  }
}

TEST(FuzzUtilTest, FuzzUint64LargeInRange) {
  absl::BitGen gen;
  for (int i = 0; i < 10000; ++i) {
    EXPECT_LT(FuzzUint64(&gen, /*bits=*/10), 1024);
  }
}

}  // namespace
}  // namespace p4_fuzzer
