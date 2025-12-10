// Copyright 2025 Google LLC
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

#ifndef PINS_P4_INFRA_P4_PDPI_ENTITY_KEYS_H_
#define PINS_P4_INFRA_P4_PDPI_ENTITY_KEYS_H_

#include <algorithm>
#include <ostream>
#include <string>
#include <string_view>
#include <vector>

#include "absl/hash/hash.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "gutil/gutil/status.h"
#include "p4/v1/p4runtime.pb.h"

namespace pdpi {

class TableEntryKey {
 public:
  TableEntryKey(const p4::v1::TableEntry& entry);
  TableEntryKey() = default;

  template <typename H>
  friend H AbslHashValue(H h, const TableEntryKey& key);

  // Only intended for debugging purposes.  Do not assume output consistency.
  template <typename Sink>
  friend inline void AbslStringify(Sink& sink, const TableEntryKey& key) {
    absl::Format(&sink, "id: %d priority: %d matches(%d)", key.table_id_,
                 key.priority_, key.matches_.size());
    for (auto& m : key.matches_) {
      absl::Format(&sink, " %d", m.field_id());
    }
  }
  friend std::ostream& operator<<(std::ostream& stream,
                                  const TableEntryKey key) {
    return stream << absl::StrCat(key);
  }

  bool operator==(const TableEntryKey& other) const;
  bool operator!=(const TableEntryKey& other) const;
  bool operator<(const TableEntryKey& other) const;

  // Returns vector of non-key field paths in PI TableEntry proto.
  static std::vector<std::string_view> NonKeyFieldPaths();

 private:
  uint32_t table_id_;
  int32_t priority_;
  std::vector<p4::v1::FieldMatch> matches_;
};

template <typename H>
H AbslHashValue(H h, const TableEntryKey& key) {
  h = H::combine(std::move(h), key.table_id_, key.priority_);

  for (const auto& field : key.matches_) {
    // Since protobufs yield a default value for an unset field and since {
    // exact, ternary, lpm, range, optional } are all part of the oneof
    // directive (i,e only one of them will be set at a given time), we can get
    // a correct hash by combining all fields without checking which one is set.
    h = H::combine(std::move(h), field.field_id(), field.exact().value(),
                   field.ternary().value(), field.ternary().mask(),
                   field.lpm().value(), field.lpm().prefix_len(),
                   field.range().low(), field.range().high(),
                   field.optional().value());
  }
  return h;
}

// PacketReplicationEntryKey provides a unique key that can be used in maps
// that will hold the PacketReplicationEngineEntry entity type.
class PacketReplicationEntryKey {
 public:
  explicit PacketReplicationEntryKey(
      const p4::v1::PacketReplicationEngineEntry& entry);
  PacketReplicationEntryKey() = default;

  template <typename H>
  friend H AbslHashValue(H h, const PacketReplicationEntryKey& key);

  // Only intended for debugging purposes.  Do not assume output consistency.
  template <typename Sink>
  friend inline void AbslStringify(Sink& sink,
                                   const PacketReplicationEntryKey& key) {
    absl::Format(&sink, "id: %d", key.id_);
  }
  friend std::ostream& operator<<(std::ostream& stream,
                                  const PacketReplicationEntryKey key) {
    return stream << absl::StrCat(key);
  }

  bool operator==(const PacketReplicationEntryKey& other) const;
  bool operator!=(const PacketReplicationEntryKey& other) const;
  bool operator<(const PacketReplicationEntryKey& other) const;

 private:
  p4::v1::PacketReplicationEngineEntry::TypeCase replication_type_;
  uint32_t id_ = 0;
};

template <typename H>
H AbslHashValue(H h, const PacketReplicationEntryKey& key) {
  h = H::combine(std::move(h), key.id_);
  return h;
}

// EntityKey is a top-level unique key that can be used in maps that need to
// store P4 entries that may hold different entity types.
// Currently, we only need to support PacketReplicationEngineEntry and
// TableEntry, but the oneof structure supports many types.
// See the P4 V1 p4runtime.proto for a list of the available entity types.
class EntityKey {
 public:
  static absl::StatusOr<EntityKey> MakeEntityKey(const p4::v1::Entity& entity);
  explicit EntityKey(const p4::v1::TableEntry& entry);

  template <typename H>
  friend H AbslHashValue(H h, const EntityKey& key);

  // Only intended for debugging purposes.  Do not assume output consistency.
  template <typename Sink>
  friend void AbslStringify(Sink& sink, const EntityKey& key) {
    if (std::get_if<TableEntryKey>(&key.key_) != nullptr) {
      absl::Format(&sink, "%s",
                   absl::StrCat(std::get<TableEntryKey>(key.key_)));
    } else if (std::get_if<PacketReplicationEntryKey>(&key.key_) != nullptr) {
      absl::Format(&sink, "%s",
                   absl::StrCat(std::get<PacketReplicationEntryKey>(key.key_)));
    }
  }
  friend std::ostream& operator<<(std::ostream& stream, const EntityKey key) {
    return stream << absl::StrCat(key);
  }

  bool operator==(const EntityKey& other) const;
  bool operator!=(const EntityKey& other) const;
  bool operator<(const EntityKey& other) const;
  // A supported key_ must be created by the default constructor, so this will
  // create an empty TableEntryKey.
  EntityKey();
  ~EntityKey() = default;

 private:
  explicit EntityKey(const p4::v1::Entity& entity);
  std::variant<TableEntryKey, PacketReplicationEntryKey> key_;
};

template <typename H>
H AbslHashValue(H h, const EntityKey& key) {
  return AbslHashValue(std::move(h), key.key_);
}

}  // namespace pdpi

#endif  // PINS_P4_INFRA_P4_PDPI_ENTITY_KEYS_H_
