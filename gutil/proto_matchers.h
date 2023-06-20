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

#include "absl/strings/string_view.h"
#include "google/protobuf/message.h"
#include "google/protobuf/util/message_differencer.h"
#include "gtest/gtest.h"
#include "gutil/proto.h"

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

 private:
  mutable std::shared_ptr<google::protobuf::Message> expected_;
  std::string expected_text_;
};

inline ::testing::PolymorphicMatcher<ProtobufEqMatcher> EqualsProto(
    const google::protobuf::Message& proto) {
  return ::testing::MakePolymorphicMatcher(ProtobufEqMatcher(proto));
}

inline ::testing::PolymorphicMatcher<ProtobufEqMatcher> EqualsProto(
    absl::string_view proto_text) {
  return ::testing::MakePolymorphicMatcher(ProtobufEqMatcher(proto_text));
}

}  // namespace gutil

#endif  // GUTIL_PROTO_MATCHERS_H
