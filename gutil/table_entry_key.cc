// Copyright 2021 Google LLC
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
#include "gutil/table_entry_key.h"

#include <algorithm>
#include <string>

#include "glog/logging.h"
#include "google/protobuf/message.h"
#include "google/protobuf/util/message_differencer.h"

namespace gutil {
namespace {

// Deterministically serializes a given `proto` to a returned string.
// Note: This won't necessarily be fully deterministic across builds or proto
// changes, but hopefully it is close enough to ensure reproducability.
std::string DeterministicallySerializeProtoToString(
    const google::protobuf::Message& proto) {
  std::string output_string;
  google::protobuf::io::StringOutputStream stream(&output_string);
  google::protobuf::io::CodedOutputStream coded_stream(&stream);
  coded_stream.SetSerializationDeterministic(true);
  CHECK(proto.SerializeToCodedStream(&coded_stream))  // Crash OK
      << "Serialization of a p4::v1::FieldMatch failed. Proto was: "
      << proto.DebugString();

  return output_string;
}
}  // namespace

using ::p4::v1::FieldMatch;

TableEntryKey::TableEntryKey(const p4::v1::TableEntry& entry) {
  table_id_ = entry.table_id();
  priority_ = entry.priority();

  auto match = entry.match();
  matches_ = std::vector<FieldMatch>(match.begin(), match.end());
  // Sort matches by field to ensure consistent keys.
  std::sort(matches_.begin(), matches_.end(),
            [](const FieldMatch& a, const FieldMatch& b) {
              return a.field_id() < b.field_id();
            });
}

bool TableEntryKey::operator==(const TableEntryKey& other) const {
  // Note: this must match the implementation of hash value below.
  if ((table_id_ != other.table_id_) || (priority_ != other.priority_) ||
      matches_.size() != other.matches_.size()) {
    return false;
  }

  for (int i = 0; i < matches_.size(); i++) {
    if (!google::protobuf::util::MessageDifferencer::Equals(
            matches_[i], other.matches_[i])) {
      return false;
    }
  }
  return true;
}

bool TableEntryKey::operator<(const TableEntryKey& other) const {
  if (table_id_ != other.table_id_) return table_id_ < other.table_id_;
  if (priority_ != other.priority_) return priority_ < other.priority_;
  if (matches_.size() != other.matches_.size())
    return matches_.size() < other.matches_.size();

  for (int i = 0; i < matches_.size(); i++) {
    if (!google::protobuf::util::MessageDifferencer::Equals(
            matches_[i], other.matches_[i])) {
      return DeterministicallySerializeProtoToString(matches_[i]) <
             DeterministicallySerializeProtoToString(other.matches_[i]);
    }
  }
  return false;
}

}  // namespace gutil
