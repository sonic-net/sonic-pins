// Copyright 2023 Google LLC
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
#include "p4_infra/p4_pdpi/entity_keys.h"

#include <algorithm>
#include <string>
#include <string_view>
#include <vector>

#include "absl/log/check.h"
#include "absl/status/statusor.h"
#include "google/protobuf/io/zero_copy_stream_impl_lite.h"
#include "google/protobuf/message.h"
#include "google/protobuf/util/message_differencer.h"
#include "gutil/gutil/status.h"

namespace pdpi {

namespace {

using ::p4::v1::FieldMatch;

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

// LINT.IfChange(make_entity_key)
absl::StatusOr<EntityKey> EntityKey::MakeEntityKey(
    const p4::v1::Entity& entity) {
  switch (entity.entity_case()) {
    case p4::v1::Entity::kTableEntry:
      return EntityKey(entity);
      break;
    case p4::v1::Entity::kPacketReplicationEngineEntry:
      return EntityKey(entity);
      break;
    default:
      break;
  }
  return gutil::InvalidArgumentErrorBuilder()
         << "[P4RT App] Entity key cannot be constructed from entity type '"
         << entity.entity_case();
}
// LINT.ThenChange(:entity_key_private_constructor)

// LINT.IfChange(entity_key_private_constructor)
EntityKey::EntityKey(const p4::v1::Entity& entity) {
  switch (entity.entity_case()) {
    case p4::v1::Entity::kTableEntry:
      key_ = TableEntryKey(entity.table_entry());
      break;
    case p4::v1::Entity::kPacketReplicationEngineEntry:
      key_ =
          PacketReplicationEntryKey(entity.packet_replication_engine_entry());
      break;
    default:  // Disallowed by MakeEntityKey
      break;
  }
}
// LINT.ThenChange(:make_entity_key)

// Have the default constructor create an empty TableEntryKey.
EntityKey::EntityKey() {
  p4::v1::TableEntry entry;
  key_ = TableEntryKey(entry);
}

EntityKey::EntityKey(const p4::v1::TableEntry& entry) {
  key_ = TableEntryKey(entry);
}

bool EntityKey::operator==(const EntityKey& other) const {
  return key_ == other.key_;
}

bool EntityKey::operator!=(const EntityKey& other) const {
  return key_ != other.key_;
}

bool EntityKey::operator<(const EntityKey& other) const {
  return key_ < other.key_;
}

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

bool TableEntryKey::operator!=(const TableEntryKey& other) const {
  return !(*this == other);
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

std::vector<std::string_view> TableEntryKey::NonKeyFieldPaths() {
  return {
      "p4.v1.TableEntry.action",
      "p4.v1.TableEntry.controller_metadata",
      "p4.v1.TableEntry.meter_config",
      "p4.v1.TableEntry.meter_counter_data",
      "p4.v1.TableEntry.is_default_action",
      "p4.v1.TableEntry.idle_timeout_ns",
      "p4.v1.TableEntry.time_since_last_hit",
      "p4.v1.TableEntry.metadata",
  };
}

PacketReplicationEntryKey::PacketReplicationEntryKey(
    const p4::v1::PacketReplicationEngineEntry& entry) {
  replication_type_ = entry.type_case();
  switch (entry.type_case()) {
    case p4::v1::PacketReplicationEngineEntry::kMulticastGroupEntry:
      id_ = entry.multicast_group_entry().multicast_group_id();
      break;
    case p4::v1::PacketReplicationEngineEntry::kCloneSessionEntry:
      id_ = entry.clone_session_entry().session_id();
      break;
    default:
      id_ = 0;
      break;
  }
}

bool PacketReplicationEntryKey::operator==(
    const PacketReplicationEntryKey& other) const {
  return replication_type_ == other.replication_type_ && id_ == other.id_;
}

bool PacketReplicationEntryKey::operator!=(
    const PacketReplicationEntryKey& other) const {
  return replication_type_ != other.replication_type_ || id_ != other.id_;
}

bool PacketReplicationEntryKey::operator<(
    const PacketReplicationEntryKey& other) const {
  if (replication_type_ == other.replication_type_) {
    return id_ < other.id_;
  }
  return replication_type_ < other.replication_type_;
}

}  // namespace pdpi
