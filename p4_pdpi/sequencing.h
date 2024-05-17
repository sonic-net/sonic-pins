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

#ifndef PINS_P4_PDPI_SEQUENCING_H_
#define PINS_P4_PDPI_SEQUENCING_H_

#include <functional>
#include <optional>
#include <vector>

#include "absl/functional/function_ref.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/types/span.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"

namespace pdpi {

// Sequencing functionality, see go/p4-sequencing for details. All APIs are
// stable, i.e. for entries without constraint that could appear in any order,
// the input order is preserved.

// Returns a list of write requests, such that updates are sequenced correctly
// when the write requests are sent in order. Order within a write request is
// stable, i.e. the same as in the input. Optionally, `max_batch_size` can be
// used to limit the number of updates in a single write request.
absl::StatusOr<std::vector<p4::v1::WriteRequest>>
SequencePiUpdatesIntoWriteRequests(
    const IrP4Info& info, absl::Span<const p4::v1::Update> updates,
    std::optional<int> max_batch_size = std::nullopt);

// Returns a vector of batches, where each batch is given by a vector of indices
// into the input vector, such that updates are sequenced correctly when sent
// batched in the order indicated. Order within a write request is stable, i.e.
// the same as in the input.
absl::StatusOr<std::vector<std::vector<int>>> SequencePiUpdatesInPlace(
    const IrP4Info& info, absl::Span<const p4::v1::Update> updates);

// Sorts the table entries such that entries that are depended on come first.
// That is, two entries x and y where x refers to y will be sorted as [y, x].
absl::Status SortTableEntries(const IrP4Info& info,
                              std::vector<p4::v1::TableEntry>& entries);

// Returns the subset of TableEntry in `entries` that is not reachable from any
// root entry in `entries`, where a root entry is determined by the
// `is_root_entry` function. An entry `e` is reachable from a root entry `r`
// if and only if `r` refers to `e`, directly or transitively. The reference
// graph is computed based on `ir_p4info`.
absl::StatusOr<std::vector<p4::v1::TableEntry>> GetEntriesUnreachableFromRoots(
    absl::Span<const p4::v1::TableEntry> entries,
    absl::FunctionRef<absl::StatusOr<bool>(const p4::v1::TableEntry&)>
        is_root_entry,
    const IrP4Info& ir_p4info);

}  // namespace pdpi

#endif  // PINS_P4_PDPI_SEQUENCING_H_
