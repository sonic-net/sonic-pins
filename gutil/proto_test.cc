#include "gutil/proto.h"

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/proto_matchers.h"
#include "gutil/proto_test.pb.h"
#include "gutil/status_matchers.h"

namespace gutil {
namespace {

using ::gutil::IsOkAndHolds;
using ::gutil::StatusIs;
using ::testing::Eq;
using ::testing::IsEmpty;
using ::testing::Not;
using ::testing::ResultOf;

TEST(IsEmptyProto, ReturnsTrueForEmptyProto) {
  EXPECT_TRUE(IsEmptyProto(TestMessage()));

  // Same things, but a bit more convoluted.
  TestMessage message;
  message.set_int_field(42);
  message.set_int_field(0);
  EXPECT_TRUE(IsEmptyProto(message))
      << "where message = " << message.DebugString();
}

TEST(IsEmptyProto, ReturnsFalseForNonEmptyProto) {
  EXPECT_THAT(ParseTextProto<TestMessage>("int_field: 42"),
              IsOkAndHolds(ResultOf(IsEmptyProto, Eq(false))));
}

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

TEST(ProtoDiff, ReturnsErrorForIncompatibleMessages) {
  ASSERT_OK_AND_ASSIGN(auto message1, ParseTextProto<TestMessage>(R"pb(
                         int_field: 42
                         string_field: "hello!"
                       )pb"));
  ASSERT_OK_AND_ASSIGN(auto message2, ParseTextProto<AnotherTestMessage>(R"pb(
                         int_field: 42
                         string_field: "hello!"
                       )pb"));
  EXPECT_THAT(ProtoDiff(message1, message2).status(),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(ProtoDiff, ReturnsEmptyDiffForEqualMessages) {
  ASSERT_OK_AND_ASSIGN(auto message1, ParseTextProto<TestMessage>(R"pb(
                         int_field: 42
                         string_field: "hello!"
                       )pb"));
  EXPECT_THAT(ProtoDiff(message1, message1), IsOkAndHolds(IsEmpty()));
}

TEST(ProtoDiff, ReturnsNonEmptyDiffForUnequalMessages) {
  ASSERT_OK_AND_ASSIGN(auto message1, ParseTextProto<TestMessage>(R"pb(
                         int_field: 42
                         string_field: "hello!"
                       )pb"));
  ASSERT_OK_AND_ASSIGN(auto message2, ParseTextProto<TestMessage>(R"pb(
                         int_field: 43
                         string_field: "bye"
                       )pb"));
  EXPECT_THAT(ProtoDiff(message1, message2), IsOkAndHolds(Not(IsEmpty())));
}

TEST(TextProtoHelpers, PrintTextProto) {
  TestMessage message;
  message.set_int_field(42);
  message.set_string_field("bye");
  EXPECT_THAT(PrintTextProto(message),
              "int_field: 42\nstring_field: \"bye\"\n");
}

TEST(TextProtoHelpers, PrintShortTextProto) {
  TestMessage message;
  message.set_int_field(42);
  message.set_string_field("bye");
  EXPECT_THAT(PrintShortTextProto(message),
              "int_field: 42 string_field: \"bye\"");
}

TEST(ParseJsonAsProto, ParsesTestMessage) {
  EXPECT_THAT(ParseJsonAsProto<TestMessage>(R"json({
                                              "int_field" : 42,
                                              "string_field" : "bye"
                                            })json"),
              IsOkAndHolds(EqualsProto(R"pb(
                int_field: 42 string_field: "bye"
              )pb")));
}

TEST(ParseJsonAsProto, CanIgnoreUnknownFields) {
  EXPECT_THAT(ParseJsonAsProto<TestMessage>(R"json({
                                              "int_field" : 42,
                                              "string_field" : "bye",
                                              "unknown_field": "please ignore"
                                            })json",
                                            /*ignore_unknown_field=*/false),
              Not(IsOk()));
  EXPECT_THAT(ParseJsonAsProto<TestMessage>(R"json({
                                              "int_field" : 42,
                                              "string_field" : "bye",
                                              "unknown_field": "please ignore"
                                            })json",
                                            /*ignore_unknown_field=*/true),
              IsOkAndHolds(EqualsProto(R"pb(
                int_field: 42 string_field: "bye"
              )pb")));
}

TEST(SerializeProtoAsJson, RoundTripsWithParseJsonAsProto) {
  ASSERT_OK_AND_ASSIGN(auto proto, ParseTextProto<TestMessage>(R"pb(
                         int_field: 42
                         string_field: "hello!"
                       )pb"));
  ASSERT_OK_AND_ASSIGN(std::string json, SerializeProtoAsJson(proto));
  EXPECT_THAT(ParseJsonAsProto<TestMessage>(json),
              IsOkAndHolds(EqualsProto(proto)));
}

}  // namespace
}  // namespace gutil
