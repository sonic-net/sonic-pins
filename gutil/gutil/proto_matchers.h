// Copyright 2020 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#ifndef PINS_GUTIL_PROTO_MATCHERS_H_
#define PINS_GUTIL_PROTO_MATCHERS_H_

#include <memory>
#include <ostream>
#include <string>

#include "absl/log/log.h"
#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "google/protobuf/descriptor.h"
#include "google/protobuf/message.h"
#include "google/protobuf/util/message_differencer.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto.h"

namespace gutil {

// -- EqualsProto matcher ------------------------------------------------------

// Implements a protobuf matcher interface that verifies 2 protobufs are equal
// while ignoring the repeated field ordering.
//
// Sample usage:
//   EXPECT_THAT(MyCall(), EqualsProto<pdpi::IrTableEntry>(R"pb(
//                 table_name: "ROUTER_INTERFACE_TABLE"
//                 priority: 123
//                 matches {
//                   name: "router_interface_id"
//                   exact { str: "16" }
//                 }
//               )pb"));
//
// Sample output on failure:
//   Value of: MyCall()
//   Expected:
//   table_name: "ROUTER_INTERFACE_TABLE"
//   matches {
//     name: "router_interface_id"
//     exact {
//       str: "16"
//     }
//   }
//   priority: 123
//
//     Actual: 96-byte object <58-AC 77-4D 5C-55 00-00 00-00 00-00 00-00 00-00
//   00-00 00-00 00-00 00-00 01-00 00-00 04-00 00-00 30-8D 80-4D 5C-55 00-00
//   30-55 80-4D 5C-55 00-00 20-25 79-4D 5C-55 00-00 00-00 00-00 00-00 00-00
//   00-00 00-00 00-00 00-00 C8-01 00-00 5C-55 00-00 00-E6 12-7F 70-7F 00-00
//   00-00 00-00 00-00 00-00> (of type pdpi::IrTableEntry),
//   table_name: "ROUTER_INTERFACE_TABLE"
//   matches {
//     name: "router_interface_id"
//     exact {
//       str: "16"
//     }
//   }
//   priority: 456
class ProtobufEqMatcher {
 public:
  ProtobufEqMatcher(const google::protobuf::Message& expected)
      : expected_(expected.New()), expected_text_(PrintTextProto(expected)) {
    expected_->CopyFrom(expected);
  }
  ProtobufEqMatcher(absl::string_view expected_text)
      : expected_text_{expected_text} {}

  void DescribeTo(std::ostream* os, bool negated) const {
    *os << "is " << (negated ? "not " : "") << "equal to "
        << (expected_ == nullptr ? ""
                                 : absl::StrCat(expected_->GetTypeName(), " "))
        << "<\n"
        << expected_text_ << ">";
  }
  void DescribeTo(std::ostream* os) const { return DescribeTo(os, false); }
  void DescribeNegationTo(std::ostream* os) const {
    return DescribeTo(os, true);
  }

  template <typename ProtoType>
  bool MatchAndExplain(const ProtoType& actual,
                       ::testing::MatchResultListener* listener) const {
    std::string diff;
    google::protobuf::util::MessageDifferencer differ;
    differ.set_scope(comparison_scope_);
    differ.ReportDifferencesToString(&diff);
    // Order does not matter for repeated fields.
    differ.set_repeated_field_comparison(
        google::protobuf::util::MessageDifferencer::RepeatedFieldComparison::
            AS_SET);

    // When parsing from a proto text string we must first create a temporary
    // with the same proto type as the "acutal" argument.
    if (expected_ == nullptr) {
      absl::StatusOr<ProtoType> expected =
          gutil::ParseTextProto<ProtoType>(expected_text_);
      if (expected.ok()) {
        expected_ = std::make_shared<ProtoType>(std::move(*expected));
      } else {
        *listener << "where the expected proto " << expected.status().message();
        return false;
      }
    }

    // Otherwise we can compare directly with the passed protobuf message.
    bool equal = differ.Compare(*expected_, actual);
    if (!equal) {
      *listener << "with diff:\n" << diff;
    }
    return equal;
  }
  void SetComparePartially() {
    comparison_scope_ = google::protobuf::util::MessageDifferencer::PARTIAL;
  }

 private:
  mutable std::shared_ptr<google::protobuf::Message> expected_;
  std::string expected_text_;
  google::protobuf::util::MessageDifferencer::Scope comparison_scope_ =
      google::protobuf::util::MessageDifferencer::FULL;
};

inline ::testing::PolymorphicMatcher<ProtobufEqMatcher> EqualsProto(
    const google::protobuf::Message& proto) {
  return ::testing::MakePolymorphicMatcher(ProtobufEqMatcher(proto));
}

inline ::testing::PolymorphicMatcher<ProtobufEqMatcher> EqualsProto(
    absl::string_view proto_text) {
  return ::testing::MakePolymorphicMatcher(ProtobufEqMatcher(proto_text));
}

// Checks that a pair of protos are equal. Useful in combination with
// `Pointwise`.
MATCHER(EqualsProto, "is a pair of equal protobufs") {
  const auto& [x, y] = arg;
  return testing::ExplainMatchResult(EqualsProto(x), y, result_listener);
}

// Checks that a sequences of protos is equal to a given sequence.
template <class T>
auto EqualsProtoSequence(T&& sequence) {
  return testing::Pointwise(EqualsProto(), std::forward<T>(sequence));
}

// -- HasOneofCaseMatcher matcher ----------------------------------------------

template <class ProtoMessage>
class HasOneofCaseMatcher {
 public:
  using is_gtest_matcher = void;
  using OneofCase = int;
  HasOneofCaseMatcher(absl::string_view oneof_name,
                      OneofCase expected_oneof_case)
      : oneof_name_{oneof_name}, expected_oneof_case_(expected_oneof_case) {}

  void DescribeTo(std::ostream* os, bool negate) const {
    if (os == nullptr) return;
    *os << "is a `" << GetMessageDescriptor().full_name()
        << "` protobuf message whose oneof field `" << oneof_name_ << "`";
    if (negate) {
      *os << " does not have case ";
    } else {
      *os << " has case ";
    }
    *os << "`" << GetOneofCaseName(expected_oneof_case_) << "`";
  }
  void DescribeTo(std::ostream* os) const { DescribeTo(os, false); }
  void DescribeNegationTo(std::ostream* os) const { DescribeTo(os, true); }

  bool MatchAndExplain(const ProtoMessage& message,
                       testing::MatchResultListener* listener) const {
    const google::protobuf::Message& m = message;
    const google::protobuf::FieldDescriptor* set_oneof_field =
        m.GetReflection()->GetOneofFieldDescriptor(m, GetOneofDescriptor());
    *listener << "the oneof `" << oneof_name_ << "` is ";
    if (set_oneof_field == nullptr) {
      *listener << "unset";
      return false;
    } else {
      *listener << "set to `" << set_oneof_field->name() << "`";
      return set_oneof_field->number() == expected_oneof_case_;
    }
  }

 private:
  std::string oneof_name_;
  OneofCase expected_oneof_case_;

  const google::protobuf::Descriptor& GetMessageDescriptor() const {
    auto* descriptor = ProtoMessage::descriptor();
    if (descriptor == nullptr) {
      LOG(FATAL)  // Crash ok: test
          << "ProtoMessage::descriptor() returned null.";
    }
    return *descriptor;
  }
  const google::protobuf::OneofDescriptor* GetOneofDescriptor() const {
    return GetMessageDescriptor().FindOneofByName(oneof_name_);
  }
  const google::protobuf::FieldDescriptor* GetOneofCaseDescriptor(
      OneofCase oneof_case) const {
    return GetMessageDescriptor().FindFieldByNumber(oneof_case);
  }
  std::string GetOneofCaseName(OneofCase oneof_case) const {
    const google::protobuf::FieldDescriptor* descriptor =
        GetOneofCaseDescriptor(oneof_case);
    return descriptor == nullptr ? "<unknown case>"
                                 : std::string(descriptor->name());
  }
};

// Protobuf matcher that checks if the oneof field with the given `oneof_name`
// is set to the given `expected_oneof_case`.
// That is, checks `proto.oneof_name_case() == expected_oneof_case`.
//
// Sample usage:
// ```
//     EXPECT_THAT(packet.headers(0),
//                 HasOneofCase<packetlib::Header>(
//                     "header", packetlib::Header::kIpv4Header));
// ```
template <class ProtoMessage>
HasOneofCaseMatcher<ProtoMessage> HasOneofCase(absl::string_view oneof_name,
                                               int expected_oneof_case) {
  return HasOneofCaseMatcher<ProtoMessage>(oneof_name, expected_oneof_case);
}

// Partially(m) returns a matcher that is the same as m, except that
// only fields present in the expected protobuf are considered (using
// google::protobuf::util::MessageDifferencer's PARTIAL comparison option).  For
// example, Partially(EqualsProto(p)) will ignore any field that's
// not set in p when comparing the protobufs. The inner matcher m can
// be any of the Equals* and EquivTo* protobuf matchers above.
template <class InnerProtoMatcher>
inline InnerProtoMatcher Partially(InnerProtoMatcher inner_proto_matcher) {
  inner_proto_matcher.mutable_impl().SetComparePartially();
  return inner_proto_matcher;
}

}  // namespace gutil

#endif  // PINS_GUTIL_PROTO_MATCHERS_H_
