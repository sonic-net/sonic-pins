#include "gutil/gutil/proto_ordering.h"

#include <vector>

#include "gmock/gmock.h"
#include "google/protobuf/repeated_ptr_field.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto_matchers.h"
#include "gutil/gutil/proto_test.pb.h"
#include "gutil/gutil/testing.h"

namespace gutil {
namespace {

using ::testing::Not;
using ::testing::UnorderedElementsAre;

// Returns a `TestMessage` protobuf that is distinct from
// `ArbitraryProtoMessage2()` and `ArbitraryProtoMessage3()` but otherwise
// arbitrary.
TestMessage ArbitraryProtoMessage1() {
  return ParseProtoOrDie<TestMessage>(R"pb(
    int_field: 42 string_field: "hello!"
  )pb");
}

// Returns a `TestMessage` protobuf that is distinct from
// `ArbitraryProtoMessage1()` and `ArbitraryProtoMessage3()` but otherwise
// arbitrary.
TestMessage ArbitraryProtoMessage2() {
  return ParseProtoOrDie<TestMessage>(R"pb(
    int_field: 42 string_field: "bye"
  )pb");
}

// Returns a `TestMessage` protobuf that is distinct from
// `ArbitraryProtoMessage1()` and `ArbitraryProtoMessage2()` but otherwise
// arbitrary.
TestMessage ArbitraryProtoMessage3() {
  return ParseProtoOrDie<TestMessage>(R"pb(
    int_field: 12 string_field: "ciao"
  )pb");
}

TEST(InefficientProtoLessThan, ReturnsFalseForEqualMessages) {
  EXPECT_FALSE(InefficientProtoLessThan(ArbitraryProtoMessage1(),
                                        ArbitraryProtoMessage1()));
  EXPECT_FALSE(InefficientProtoLessThan(ArbitraryProtoMessage2(),
                                        ArbitraryProtoMessage2()));
  EXPECT_FALSE(InefficientProtoLessThan(ArbitraryProtoMessage3(),
                                        ArbitraryProtoMessage3()));
}

TEST(InefficientProtoLessThan, ReturnsTrueAndFalseForUnequalMessages) {
  EXPECT_THAT((std::vector<bool>{
                  InefficientProtoLessThan(ArbitraryProtoMessage1(),
                                           ArbitraryProtoMessage2()),
                  InefficientProtoLessThan(ArbitraryProtoMessage2(),
                                           ArbitraryProtoMessage1()),
              }),
              UnorderedElementsAre(true, false));
  EXPECT_THAT((std::vector<bool>{
                  InefficientProtoLessThan(ArbitraryProtoMessage1(),
                                           ArbitraryProtoMessage3()),
                  InefficientProtoLessThan(ArbitraryProtoMessage3(),
                                           ArbitraryProtoMessage1()),
              }),
              UnorderedElementsAre(true, false));
  EXPECT_THAT((std::vector<bool>{
                  InefficientProtoLessThan(ArbitraryProtoMessage2(),
                                           ArbitraryProtoMessage3()),
                  InefficientProtoLessThan(ArbitraryProtoMessage3(),
                                           ArbitraryProtoMessage2()),
              }),
              UnorderedElementsAre(true, false));
}

// `InefficientProtoLessThan` promises to be stable over time. Here, we
// hard-code some input-output pairs of the function to catch changes in
// behavior.
TEST(InefficientProtoLessThan, OrderIsStable) {
  EXPECT_TRUE(
      InefficientProtoLessThan(ParseProtoOrDie<TestMessage>("int_field: 1"),
                               ParseProtoOrDie<TestMessage>("int_field: 2")));
  EXPECT_TRUE(InefficientProtoLessThan(
      ParseProtoOrDie<TestMessage>("int_field: 42"),
      ParseProtoOrDie<TestMessage>("string_field: \"hello!\"")));
}

TEST(InefficientProtoSort, AllPermutationsOfThreeGetOrderedTheSameWay) {
  std::vector<TestMessage> x1, x2, x3, x4, x5, x6;
  x1 = {ArbitraryProtoMessage1(), ArbitraryProtoMessage2(),
        ArbitraryProtoMessage3()};
  x2 = {ArbitraryProtoMessage1(), ArbitraryProtoMessage3(),
        ArbitraryProtoMessage2()};
  x3 = {ArbitraryProtoMessage2(), ArbitraryProtoMessage1(),
        ArbitraryProtoMessage3()};
  x4 = {ArbitraryProtoMessage2(), ArbitraryProtoMessage3(),
        ArbitraryProtoMessage1()};
  x5 = {ArbitraryProtoMessage2(), ArbitraryProtoMessage3(),
        ArbitraryProtoMessage1()};
  x6 = {ArbitraryProtoMessage2(), ArbitraryProtoMessage3(),
        ArbitraryProtoMessage1()};
  EXPECT_THAT(x2, Not(EqualsProtoSequence(x1)));
  EXPECT_THAT(x3, Not(EqualsProtoSequence(x1)));
  EXPECT_THAT(x4, Not(EqualsProtoSequence(x1)));
  EXPECT_THAT(x5, Not(EqualsProtoSequence(x1)));
  EXPECT_THAT(x6, Not(EqualsProtoSequence(x1)));
  InefficientProtoSort(x1);
  InefficientProtoSort(x2);
  InefficientProtoSort(x3);
  InefficientProtoSort(x4);
  InefficientProtoSort(x5);
  InefficientProtoSort(x6);
  EXPECT_THAT(x2, EqualsProtoSequence(x1));
  EXPECT_THAT(x3, EqualsProtoSequence(x1));
  EXPECT_THAT(x4, EqualsProtoSequence(x1));
  EXPECT_THAT(x5, EqualsProtoSequence(x1));
  EXPECT_THAT(x6, EqualsProtoSequence(x1));
}

TEST(InefficientProtoSortAndDedupTest, RemovesDuplicates) {
  std::vector<TestMessage> messages;

  messages = {ArbitraryProtoMessage1(), ArbitraryProtoMessage1(),
              ArbitraryProtoMessage1()};
  InefficientProtoSortAndDedup(messages);
  EXPECT_THAT(messages,
              UnorderedElementsAre(EqualsProto(ArbitraryProtoMessage1())));

  messages = {ArbitraryProtoMessage1(), ArbitraryProtoMessage2(),
              ArbitraryProtoMessage2()};
  InefficientProtoSortAndDedup(messages);
  EXPECT_THAT(messages,
              UnorderedElementsAre(EqualsProto(ArbitraryProtoMessage1()),
                                   EqualsProto(ArbitraryProtoMessage2())));

  messages = {
      ArbitraryProtoMessage1(), ArbitraryProtoMessage2(),
      ArbitraryProtoMessage2(), ArbitraryProtoMessage3(),
      ArbitraryProtoMessage3(), ArbitraryProtoMessage3(),
  };
  InefficientProtoSortAndDedup(messages);
  EXPECT_THAT(messages,
              UnorderedElementsAre(EqualsProto(ArbitraryProtoMessage1()),
                                   EqualsProto(ArbitraryProtoMessage2()),
                                   EqualsProto(ArbitraryProtoMessage3())));
}

TEST(InefficientProtoSortAndDedupTest,
     RepeatedPtrFieldSpecializationRemovesDuplicates) {
  google::protobuf::RepeatedPtrField<TestMessage> messages;

  messages.Add(ArbitraryProtoMessage1());
  messages.Add(ArbitraryProtoMessage1());
  messages.Add(ArbitraryProtoMessage1());
  InefficientProtoSortAndDedup(messages);
  EXPECT_THAT(messages,
              UnorderedElementsAre(EqualsProto(ArbitraryProtoMessage1())));

  messages.Add(ArbitraryProtoMessage2());
  messages.Add(ArbitraryProtoMessage2());
  InefficientProtoSortAndDedup(messages);
  EXPECT_THAT(messages,
              UnorderedElementsAre(EqualsProto(ArbitraryProtoMessage1()),
                                   EqualsProto(ArbitraryProtoMessage2())));

  messages.Add(ArbitraryProtoMessage1());
  messages.Add(ArbitraryProtoMessage2());
  messages.Add(ArbitraryProtoMessage2());
  messages.Add(ArbitraryProtoMessage3());
  messages.Add(ArbitraryProtoMessage3());
  messages.Add(ArbitraryProtoMessage3());
  InefficientProtoSortAndDedup(messages);
  EXPECT_THAT(messages,
              UnorderedElementsAre(EqualsProto(ArbitraryProtoMessage1()),
                                   EqualsProto(ArbitraryProtoMessage2()),
                                   EqualsProto(ArbitraryProtoMessage3())));
}

TEST(InefficientProtoSortAndDedupTest, Sorts) {
  std::vector<TestMessage> messages, deduped_messages;

  messages = {ArbitraryProtoMessage1(), ArbitraryProtoMessage2(),
              ArbitraryProtoMessage1(), ArbitraryProtoMessage3(),
              ArbitraryProtoMessage3(), ArbitraryProtoMessage3()};
  deduped_messages = {ArbitraryProtoMessage3(), ArbitraryProtoMessage2(),
                      ArbitraryProtoMessage1()};
  InefficientProtoSortAndDedup(messages);
  InefficientProtoSort(deduped_messages);
  EXPECT_THAT(messages, EqualsProtoSequence(deduped_messages));
}

}  // namespace
}  // namespace gutil
