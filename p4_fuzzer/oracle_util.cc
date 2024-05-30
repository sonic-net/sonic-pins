#include "p4_fuzzer/oracle_util.h"

#include <algorithm>
#include <numeric>

#include "absl/algorithm/container.h"
#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/types/optional.h"
#include "gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_fuzzer/switch_state.h"
#include "p4_fuzzer/table_entry_key.h"
#include "p4_pdpi/ir.h"

namespace p4_fuzzer {

using absl::StatusCode;
using ::p4::v1::Error;
using ::p4::v1::TableEntry;
using ::p4::v1::Update;
using ::p4::v1::WriteRequest;

absl::Status IsWellformedUpdate(const pdpi::IrP4Info& ir_p4_info,
                                const Update& update) {
  // Check by converting to PD
  TableEntry table_entry = update.entity().table_entry();

  ASSIGN_OR_RETURN(pdpi::IrTableEntry ir_entry,
                   pdpi::PiTableEntryToIr(ir_p4_info, table_entry));

  // TODO: check table constraints.
  return absl::OkStatus();
}

absl::Status UpdateOracle(const pdpi::IrP4Info& ir_p4_info,
                          const Update& update, const Error& status,
                          const SwitchState& state) {
  StatusCode code = static_cast<StatusCode>(status.canonical_code());
  absl::Status invalid_reason = IsWellformedUpdate(ir_p4_info, update);
  if (!invalid_reason.ok()) {
    if (code != StatusCode::kInvalidArgument) {
      return absl::InvalidArgumentError(absl::StrCat(
          "Invalid entries must be rejected with StatusCode::kInvalidArgument. "
          "Reason the entry is invalid: ",
          invalid_reason.message()));
    }
  } else {
    const TableEntry& table_entry = update.entity().table_entry();
    const absl::optional<TableEntry>& previous =
        state.GetTableEntry(table_entry);
    bool exists = previous.has_value();
    switch (update.type()) {
      case p4::v1::Update::DELETE:
        if (exists) {
          if (code != StatusCode::kOk) {
            return absl::InvalidArgumentError(
                "Deleting an existing entry must succeed.");
          }
        } else {
          if (code != StatusCode::kNotFound) {
            return absl::InvalidArgumentError(
                "Deleting a non-existing entry must fail with "
                "StatusCode::kNotFound.");
          }
        }
        break;
      case p4::v1::Update::INSERT:
        if (exists) {
          if (code != StatusCode::kAlreadyExists) {
            return absl::InvalidArgumentError(
                "Inserting an existing entry must fail with "
                "tatusCode::kAlreadyExists.");
          }
        } else {
          if (code == StatusCode::kResourceExhausted) {
            if (!state.IsTableFull(table_entry.table_id())) {
              return absl::InvalidArgumentError(
                  "Inserting an entry into a table that is not full must "
                  "succeed.");
            }
          } else {
            if (code != StatusCode::kOk) {
              return absl::InvalidArgumentError(
                  "Inserting a non-existing entry must succeed.");
            }
          }
        }
        break;
      default:
        // TODO: Support MODIFY here once b/126750297 has been fixed.
        CHECK(false) << "Update type not supported: " << update.type();
    }
  }
  return absl::OkStatus();
}

// Verify if a sequence of updates with their associated statuses is valid in a
// given switch state.  Returns nullopt if everything is valid, and a
// description of why this sequence is not valid otherwise.
absl::optional<std::string> SequenceOfUpdatesOracle(
    const pdpi::IrP4Info& ir_p4_info,
    const std::vector<IndexUpdateStatus>& updates,
    const SwitchState& initial_state) {
  std::vector<absl::Status> oracle_failures;

  // Create a copy of the state.
  SwitchState state = initial_state;

  // Go through all updates and check if the status makes sense in the current
  // state.
  std::string error = "";
  for (int i = 0; i < updates.size(); i++) {
    int index = updates[i].index;
    const Update& update = updates[i].update;
    const Error& status = updates[i].status;

    const auto& update_oracle_result =
        UpdateOracle(ir_p4_info, update, status, state);
    if (!update_oracle_result.ok()) {
      error += absl::StrCat(
          "\n- ", "The update with id=", index,
          " was not processed correctly by the switch. The problem was: ",
          update_oracle_result.message());
    }

    // Update the state
    if (status.canonical_code() == 0) {
      state.ApplyUpdate(update);
    }
  }

  if (error.empty()) return absl::nullopt;
  return error.substr(1);
}

// See go/p4-fuzzing for more info on the design.
absl::optional<std::vector<std::string>> WriteRequestOracle(
    const pdpi::IrP4Info& ir_p4_info, const WriteRequest& request,
    const absl::Span<const Error>& statuses, const SwitchState& state) {
  // For now, we only support checking requests with table entries.
  CHECK(absl::c_all_of(request.updates(), [](const Update& update) {
    return update.entity().has_table_entry();
  }));

  std::vector<std::string> problems;

  // Match updates with status codes.
  CHECK_EQ(request.updates_size(), statuses.size());
  std::vector<IndexUpdateStatus> updates;
  for (int i = 0; i < request.updates().size(); i++) {
    const Update& update = request.updates(i);
    const Error& status = statuses[i];
    updates.push_back({i, update, status});
  }

  // Group by flow key.
  absl::flat_hash_map<TableEntryKey, std::vector<IndexUpdateStatus>>
      flowkey_to_updates;
  for (const auto& update : updates) {
    // Filter out any resource exhausted errors.
    StatusCode code = static_cast<StatusCode>(update.status.canonical_code());
    if (code == StatusCode::kResourceExhausted) continue;

    flowkey_to_updates[TableEntryKey(update.update.entity().table_entry())]
        .push_back(update);
  }

  // Check each flow key individually.
  for (auto& [key, updates] : flowkey_to_updates) {
    // Go over all possible permutations to handle the updates for this key.
    std::string first_failure = "";
    bool found_legal_permutation = false;
    do {
      absl::optional<std::string> res = absl::nullopt;
      // Optimization: If there is just a single update, we don't need to invoke
      // SequenceOfUpdatesOracle and can avoid the state copy.
      if (updates.size() == 1) {
        const auto& update_oracle_result = UpdateOracle(
            ir_p4_info, updates[0].update, updates[0].status, state);
        if (!update_oracle_result.ok()) {
          res = absl::StrCat(
              "The update with id=", updates[0].index,
              " was not processed correctly by the switch. The problem was: ",
              update_oracle_result.message());
        }
      } else {
        res = SequenceOfUpdatesOracle(ir_p4_info, updates, state);
      }

      if (!res.has_value()) {
        found_legal_permutation = true;
        break;
      } else if (first_failure.empty()) {
        first_failure = res.value();
      }
    } while (absl::c_next_permutation(
        updates, [](const IndexUpdateStatus& a, const IndexUpdateStatus& b) {
          return a.index < b.index;
        }));

    // Report error if all permutations are invalid.
    if (!found_legal_permutation) {
      int n = updates.size();
      std::string explanation;
      if (n == 1) {
        explanation = absl::StrCat("Flow #", updates[0].index,
                                   " was not handeled correctly. Flow:", "\n\n",
                                   updates[0].update.DebugString(), "\n\n",
                                   "Response by switch:", "\n\n",
                                   updates[0].status.DebugString(), "\n\n",
                                   "Problems:", "\n\n", first_failure);
      } else {
        explanation =
            absl::StrCat("A group of ", n,
                         " flows were not handled correctly.  All flows have "
                         "the same flow key.",
                         "\n\n", "The actual flows are:");
        for (const auto& update : updates) {
          explanation += absl::StrCat("\n\n", "Flow #", update.index, ":", "\n",
                                      update.update.DebugString());
          explanation += absl::StrCat("\n\n", "Response by switch:", "\n",
                                      update.status.DebugString());
        }
        explanation += absl::StrCat(
            "\n\n",
            "These group of flows can be processed in any order, but no "
            "permutation was found to be legal.  If they were processed in "
            "order, then these were the problems:",
            "\n", first_failure);
      }

      problems.push_back(explanation);
    }
  }

  // Check resource errors.  First, count number of successful inserts per
  // table.
  absl::flat_hash_map<int, int> table_id_to_num_inserts;
  for (const auto& update : updates) {
    StatusCode code = static_cast<StatusCode>(update.status.canonical_code());
    const auto& p4update = update.update;

    // Not successful, skip.
    if (code != StatusCode::kOk) continue;

    // Not an insert, skip.
    if (p4update.type() != p4::v1::Update::INSERT) continue;

    auto table_id = p4update.entity().table_entry().table_id();
    table_id_to_num_inserts[table_id] += 1;
  }
  // Then, assume all inserts happen first, and check if resource exhaustion is
  // okay.
  for (const auto& update : updates) {
    StatusCode code = static_cast<StatusCode>(update.status.canonical_code());
    const auto& p4update = update.update;
    auto table_id = p4update.entity().table_entry().table_id();
    if (code != StatusCode::kResourceExhausted) continue;

    int num_inserts = table_id_to_num_inserts[table_id];
    if (state.CanAccommodateInserts(table_id, num_inserts + 1)) {
      std::string explanation = absl::StrCat(
          "Flow #", update.index, " was not handeled correctly. Flow:", "\n\n",
          update.update.DebugString(), "\n\n", "Response by switch:", "\n\n",
          update.status.DebugString(), "\n\n",
          "The switch rejected the flow with RESOURCE_EXHAUSTED, but the "
          "table ",
          table_id, " is not full yet.  There are ",
          state.GetNumTableEntries(table_id),
          " entries in the table before the batch, and ", num_inserts,
          " inserts in this same batch were successful.");
      problems.push_back(explanation);
    }
  }

  if (problems.empty()) return absl::nullopt;
  return problems;
}

}  // namespace p4_fuzzer
