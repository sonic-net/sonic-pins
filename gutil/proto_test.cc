#include "gutil/proto.h"

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/proto_test.pb.h"
#include "gutil/status_matchers.h"

namespace gutil {
namespace {

using ::testing::Not;

TEST(ParseTextProto, EmptyTextProtoIsOk) {
  EXPECT_THAT(ParseTextProto<TestMessage>(""), IsOk());
}

TEST(ParseTextProto, InvalidTextProtoIsNotOk) {
  EXPECT_THAT(ParseTextProto<TestMessage>("bool_field: true"), Not(IsOk()));
}

TEST(ParseTextProto, NonEmptyValidTextProtoIsParsedCorrectly) {
  auto proto = ParseTextProto<TestMessage>(R"pb(
    int_field: 42
    string_field: "hello!"
  )pb");
  ASSERT_THAT(proto, IsOk());
  EXPECT_EQ(proto->int_field(), 42);
  EXPECT_EQ(proto->string_field(), "hello!");
}

}  // namespace
}  // namespace gutil
