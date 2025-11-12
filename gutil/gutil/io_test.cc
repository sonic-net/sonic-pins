#include "gutil/gutil/io.h"

#include <cstdio>
#include <cstdlib>

#include "absl/strings/str_split.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status_matchers.h"

namespace gutil {
namespace {

const std::string& TestDir() {
  static const auto* const kTestDir =
      new std::string(std::getenv("TEST_TMPDIR"));
  return *kTestDir;
}

TEST(IoTest, CanReadAndWrite) {
  const std::string kFilename = TestDir() + "/can_read_and_write.txt";
  const std::string kInput = R"(
  hello, I am a string.
  I have words, I have breaks.
  I have punctuation.
  I am a very nice string.
  Please read me.
  )";
  ASSERT_OK(WriteFile(kInput, kFilename));
  ASSERT_THAT(ReadFile(kFilename), gutil::IsOkAndHolds(testing::Eq(kInput)));
}

TEST(IoTest, CanReadLines) {
  const std::string kFilename = TestDir() + "/can_read_lines.txt";
  const std::string kInput = R"(
  hello, I am a string.
  I have words, I have breaks.
  I have punctuation.
  I am a very nice string.
  Please read me.
  )";
  std::vector<std::string> expected_lines = absl::StrSplit(kInput, '\n');

  ASSERT_OK(WriteFile(kInput, kFilename));
  ASSERT_THAT(ReadFileLines(kFilename),
              gutil::IsOkAndHolds(testing::ElementsAreArray(expected_lines)));
}

TEST(IoTest, WriteFailsWithNonexistentDirectory) {
  const std::string kFilename =
      TestDir() + "/non_directory/write_fails_with_nonexistent_directory.txt";
  EXPECT_FALSE(WriteFile("text", kFilename).ok());
}

TEST(IoTest, ReadFailsWithNonexistentFile) {
  const std::string kFilename =
      TestDir() + "/read_fails_with_nonexistent_file.txt";
  EXPECT_FALSE(ReadFile(kFilename).ok());
  EXPECT_FALSE(ReadFileLines(kFilename).ok());
}

}  // namespace
}  // namespace gutil
