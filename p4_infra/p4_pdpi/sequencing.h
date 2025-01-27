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

#ifndef PINS_P4_INFRA_P4_PDPI_SEQUENCING_H_
#define PINS_P4_INFRA_P4_PDPI_SEQUENCING_H_

#include <optional>
#include <vector>

#include "absl/base/attributes.h"
#include "absl/functional/function_ref.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/types/span.h"
#include "google/protobuf/repeated_ptr_field.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"

namespace pdpi {

// Sequencing functionality, see go/p4-sequencing for details. All APIs are
// stable, i.e. for entries without constraint that could appear in any order,
// the input order is preserved.

// Returns a list of write requests, such that updates are sequenced correctly
// when the write requests are sent in order. Order within a write request is
// stable, i.e. the same as in the input.
//
// Optionally, `max_batch_size` can be used to limit the number of updates in a
// single write request. Sending too many updates in a single write request will
// return a RESOURCE EXHAUSTED error due to the amount of metadata in the
// response. The P4 Runtime specification states that a good rule of thumb for
// the size of request is "8192 + MAX_UPDATES_PER_WRITE * 100 bytes of
// metadata". P4RuntimeSession uses a 1MB limit and 5000 updates falls safely
// within those limits and is simultaneously more than we ever tend to send.
absl::StatusOr<std::vector<p4::v1::WriteRequest>>
SequencePiUpdatesIntoWriteRequests(const IrP4Info& info,
                                   absl::Span<const p4::v1::Update> updates,
                                   std::optional<int> max_batch_size = 5000);

// Extracts updates in `write_request` and form
// ceil(write_request.update_size() / max_write_request_size) number of
// p4::WriteRequest(s). The order of updates across the resulting WriteRequests
// remains the same as the order of updates in `write_request`.
absl::StatusOr<std::vector<p4::v1::WriteRequest>> ExtractWriteRequests(
    p4::v1::WriteRequest&& write_request,
    std::optional<int> max_write_request_size = 5000);

// Returns a vector of batches, where each batch is given by a vector of indices
// into the input vector, such that updates are sequenced correctly when sent
// batched in the order indicated. Order within a write request is stable, i.e.
// the same as in the input.
absl::StatusOr<std::vector<std::vector<int>>> SequencePiUpdatesInPlace(
    const IrP4Info& info, absl::Span<const p4::v1::Update> updates);

// Stably sorts the entities such that entities that may be depended on come
// first. That is, two entities x and y where x could refer to y will be sorted
// as [y, x]. This is done based on the dependency ranks given in the IrP4Info.
// Any entities with the same dependency rank remain in the same relative order.
absl::Status StableSortEntities(const IrP4Info& info,
                                std::vector<p4::v1::Entity>& entities);

// Same as StableSortEntities but sorts the repeated `Update` message.
absl::Status StableSortUpdates(
    const IrP4Info& info,
    google::protobuf::RepeatedPtrField<p4::v1::Update>& updates,
    bool reverse_ordering = false);

// Returns the subset of Entities in `entities` that is not reachable from any
// root entity in `entities`, where a root entity is determined by the
// `is_root_entity` function. An entity `e` is reachable from a root entity `r`
// if and only if `r` refers to `e`, directly or transitively. The reference
// info comes from `ir_p4info`. Returns invalid argument error if root entities
// are not a `table_entry` or `multicast_group_entry` and non-root entities are
// not a `table_entry`.
absl::StatusOr<std::vector<p4::v1::Entity>> GetEntitiesUnreachableFromRoots(
    absl::Span<const p4::v1::Entity> entities,
    absl::FunctionRef<absl::StatusOr<bool>(const p4::v1::Entity&)>
        is_root_entity,
    const IrP4Info& ir_p4info);

}  // namespace pdpi

#endif  // PINS_P4_INFRA_P4_PDPI_SEQUENCING_H_
