// Copyright 2024 Google LLC
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

#ifndef PINS_P4_PDPI_REFERENCES_H_
#define PINS_P4_PDPI_REFERENCES_H_

#include <algorithm>
#include <string>
#include <utility>
#include <vector>

#include "absl/container/btree_set.h"
#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "google/protobuf/repeated_ptr_field.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"

namespace pdpi {

// Corresponds to a concrete instance of `IrTableReference::FieldReference` in
// ir.proto where a value is provided for the reference.
struct ConcreteFieldReference {
  // String representation of `source` in `FieldReference`.
  std::string source_field;
  // String representation of `destination` in `FieldReference`.
  std::string destination_field;
  std::string value;
};

// Corresponds to a concrete instance of `IrTableReference` in ir.proto where an
// entry's values are provided for the reference. This allows us to check
// dependencies in the following way:
//  - We have a table entry from `source_table` S
//  - We have a table entry from `destination_table` D
//  - S produces a set of Concrete Table Entry References (STER)
//  - D can be referenced by a set of Concrete Table Entry References (DTER)
//  - If the intersection of STER and DTER is not empty, then S depends on D
struct ConcreteTableReference {
  std::string source_table;
  std::string destination_table;
  absl::btree_set<ConcreteFieldReference> fields;
};

// Returns ConcreteTableReferences from `entity` to `destination_table` in
// `reference_info`. Returns error if:
//  - `entity` is not a table entry or multicast group entry
//  - `entity` does not belong to `source_table` in `reference_info`
//  - `entity` is missing one or more match fields/action parameters associated
//    with `field_references` in `reference_info`
//  - `reference_info` contains an unknown/unsupported built_in table/field
//  - there is an unsupported reference type (i.e.action param-to-action param)
//
// ASSUMPTIONS about `reference_info`:
//  - All source fields present in `reference_info` are fields that `entity` can
//    have.
// If these assumptions are not met, concrete table references may not be
// considered valid. Ideally `reference_info` should come from an IR p4 info
// created using `CreateIrP4Info` which respects these assumptions.
absl::StatusOr<absl::flat_hash_set<ConcreteTableReference>>
OutgoingConcreteTableReferences(const IrTableReference &reference_info,
                                const ::p4::v1::Entity &entity);

// Returns all possible concrete table references from some entry in
// `source_table` in `reference_info` to `entity`. Returns error if:
//  - `entity` is not a table entry or multicast group entry
//  - `entity` does not belong to `destination_table` in `reference_info`
//  - `entity` is missing one or more match fields associated with
//    `field_references` in `reference_info`
//  - `reference_info` contains an unknown/unsupported built_in table/field
//  - there is an unsupported reference type (i.e.action param-to-action param)
//
// ASSUMPTIONS about `reference_info`:
//  - All destination fields present in `reference_info` are fields that an
//    entry from the destination table can have.
// If these assumptions are not met, reference entries may not be considered
// valid. Ideally `reference_info` should come from an ir p4 info created using
// `CreateIrP4Info` which respects these assumptions.
absl::StatusOr<absl::flat_hash_set<ConcreteTableReference>>
PossibleIncomingConcreteTableReferences(const IrTableReference &reference_info,
                                        const ::p4::v1::Entity &entity);

// Represents an entity whose references were not satisfied. "Satisfied" is
// relative to a group of entities and whether the entity has outgoing or
// incoming references.
// Outgoing: The entity is referring to an entity that does not exist.
// Incoming: The entity is being referenced by an entity that does not exist.
struct EntityWithUnsatisfiedReferences {
  // Entity that has unsatisfied references.
  ::p4::v1::Entity entity;
  // Concrete table references that are unsatisfied.
  std::vector<ConcreteTableReference> unsatisfied_references;
};

// Returns list of `UnsatisfiedReference`s. An unsatisfied reference is an
// outgoing reference from an entity in `entities` that does not refer to any
// entity in `entities`. Returns error if `entities` or `info` are malformed.
absl::StatusOr<std::vector<EntityWithUnsatisfiedReferences>>
UnsatisfiedOutgoingReferences(const std::vector<::p4::v1::Entity>& pi_entities,
                              const pdpi::IrP4Info& info);

// Returns outgoing table references from `info` that are associated with
// `entity`. Returns error if `entity` is unsupported or unknown.
absl::StatusOr<google::protobuf::RepeatedPtrField<IrTableReference>>
GetOutgoingTableReferences(const IrP4Info& info, const p4::v1::Entity& entity);

// Reference Field operators.
bool operator==(const ConcreteFieldReference &lhs,
                const ConcreteFieldReference &rhs);
bool operator!=(const ConcreteFieldReference &lhs,
                const ConcreteFieldReference &rhs);
bool operator<(const ConcreteFieldReference &lhs,
               const ConcreteFieldReference &rhs);

// Reference Entry operators.
bool operator==(const ConcreteTableReference &lhs,
                const ConcreteTableReference &rhs);
bool operator!=(const ConcreteTableReference &lhs,
                const ConcreteTableReference &rhs);
bool operator<(const ConcreteTableReference &lhs,
               const ConcreteTableReference &rhs);

// -- END OF PUBLIC INTERFACE -- implementation details follow -----------------

template <typename Sink>
void AbslStringify(Sink &sink, const ConcreteFieldReference &field) {
  absl::Format(
      &sink,
      "ConcreteFieldReference{ source field: '%v', destination field: '%v', "
      "value: '%v' }",
      field.source_field, field.destination_field, field.value);
}
template <typename H>
H AbslHashValue(H h, const ConcreteFieldReference &field) {
  return H::combine(std::move(h), field.source_field, field.destination_field,
                    field.value);
}
template <typename Sink>
void AbslStringify(Sink &sink, const ConcreteTableReference &entry) {
  std::string string_entry = "ConcreteTableReference{\n";
  absl::StrAppend(&string_entry, std::string(2, ' '), "source table: '",
                  entry.source_table, "'\n");
  absl::StrAppend(&string_entry, std::string(2, ' '), "destination table: '",
                  entry.destination_table, "'\n");
  absl::StrAppend(&string_entry, std::string(2, ' '), "fields: {\n");
  for (const ConcreteFieldReference &field : entry.fields) {
    absl::StrAppend(&string_entry, std::string(4, ' '), field, ",\n");
  }
  absl::StrAppend(&string_entry, std::string(2, ' '), "}\n");
  absl::StrAppend(&string_entry, "}\n");
  absl::Format(&sink, "%v", string_entry);
}
template <typename H>
H AbslHashValue(H h, const ConcreteTableReference &entry) {
  h = H::combine(std::move(h), entry.source_table, entry.destination_table);
  for (const ConcreteFieldReference &field : entry.fields) {
    h = H::combine(std::move(h), field.source_field, field.destination_field,
                   field.value);
  }
  return h;
}

} // namespace pdpi

#endif // PINS_P4_PDPI_REFERENCE_UTIL_H_
