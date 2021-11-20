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

#ifndef GUTIL_PROTO_MATCHERS_H
#define GUTIL_PROTO_MATCHERS_H

#include <memory>
#include <ostream>
#include <string>

#include "google/protobuf/message.h"
#include "google/protobuf/text_format.h"
#include "google/protobuf/util/message_differencer.h"
#include "gtest/gtest.h"

namespace gutil {

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
      : expected_(expected.New()) {
    expected_->CopyFrom(expected);
  }

  ProtobufEqMatcher(const std::string& expected_text)
      : expected_text_(expected_text) {}

  ProtobufEqMatcher(const ProtobufEqMatcher& other)
      : expected_text_(other.expected_text_) {
    if (other.expected_ != nullptr) {
      expected_.reset(other.expected_->New());
      expected_->CopyFrom(*other.expected_);
    }
  }

  void DescribeTo(std::ostream* os) const {
    if (expected_ == nullptr) {
      *os << "\n" << expected_text_;
    } else {
      *os << "\n" << expected_->DebugString();
    }
  }
  void DescribeNegationTo(std::ostream* os) const {
    *os << "not";
    DescribeTo(os);
  }

  template <typename ProtoType>
  bool MatchAndExplain(const ProtoType& actual,
                       ::testing::MatchResultListener* listener) const {
    // Order does not matter for repeated fields.
    google::protobuf::util::MessageDifferencer diff;
    diff.set_repeated_field_comparison(
        google::protobuf::util::MessageDifferencer::RepeatedFieldComparison::
            AS_SET);

    // TODO: remove listener
    // output once this is resolved.
    *listener << "\n" << actual.DebugString();

    // When parsing from a proto text string we must first create a temporary
    // with the same proto type as the "acutal" argument.
    if (expected_ == nullptr) {
      ProtoType expected_proto;
      if (!google::protobuf::TextFormat::ParseFromString(expected_text_,
                                                         &expected_proto)) {
        *listener << "\nCould not parse expected proto text as "
                  << expected_proto.GetTypeName();
        return false;
      }
      return diff.Compare(actual, expected_proto);
    }

    // Otherwise we can compare directly with the passed protobuf message.
    return diff.Compare(actual, *expected_);
  }

 private:
  std::unique_ptr<google::protobuf::Message> expected_ = nullptr;
  const std::string expected_text_ = "";
};

inline ::testing::PolymorphicMatcher<ProtobufEqMatcher> EqualsProto(
    const google::protobuf::Message& proto) {
  return ::testing::MakePolymorphicMatcher(ProtobufEqMatcher(proto));
}

inline ::testing::PolymorphicMatcher<ProtobufEqMatcher> EqualsProto(
    const std::string& proto_text) {
  return ::testing::MakePolymorphicMatcher(ProtobufEqMatcher(proto_text));
}

}  // namespace gutil

#endif  // GUTIL_PROTO_MATCHERS_H
