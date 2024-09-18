// Copyright 2022 Google LLC
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
#include <iostream>
#include <memory>
#include <string>
#include <vector>

#include "absl/container/flat_hash_set.h"
#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "absl/log/initialize.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/ascii.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_split.h"
#include "grpcpp/security/credentials.h"
#include "gutil/status.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4rt_app/scripts/p4rt_tool_helpers.h"

// Flags to read table entries.
ABSL_FLAG(bool, compact, true, "Prints each table entry on a single line.");
ABSL_FLAG(std::string, format, "IR",
          "Prints the table entries as: 'IR'=pdpi::IrTableEntry, "
          "'PI'=p4::v1::TableEntry.");

// Flags to filter by specific table values.
ABSL_FLAG(std::string, table_ids, "",
          "Comma separated list of table IDs. The IDs will be used to "
          "filter entries based on the PI table_id field.");

namespace p4rt_app {
namespace {

absl::StatusOr<pdpi::IrP4Info> GetIrP4infoFromSwitch(
    pdpi::P4RuntimeSession& session) {
  ASSIGN_OR_RETURN(p4::v1::GetForwardingPipelineConfigResponse response,
                   pdpi::GetForwardingPipelineConfig(&session));
  return pdpi::CreateIrP4Info(response.config().p4info());
}

absl::flat_hash_set<uint32_t> GetTableIdFilers() {
  std::string table_ids_flag = absl::GetFlag(FLAGS_table_ids);

  // Go through the comma separated list of 'table_ids' values and add them to
  // the set.
  absl::flat_hash_set<uint32_t> table_ids;
  for (const auto& id_str : absl::StrSplit(table_ids_flag, ',')) {
    if (id_str.empty()) continue;

    uint32_t id;
    if (!absl::SimpleAtoi(id_str, &id)) {
      Warning(absl::StrCat("Could not convert table_id '", id_str,
                           "' to a uint32_t."));
      continue;
    }
    table_ids.insert(id);
  }
  return table_ids;
}

void FilterByTableId(std::vector<p4::v1::TableEntry>& pi_table_entries) {
  absl::flat_hash_set<uint32_t> table_ids = GetTableIdFilers();
  if (table_ids.empty()) return;

  std::vector<p4::v1::TableEntry> filtered_results;
  for (const auto& entry : pi_table_entries) {
    if (table_ids.contains(entry.table_id())) {
      filtered_results.push_back(entry);
    }
  }

  std::swap(pi_table_entries, filtered_results);
}

absl::Status PrintAsIr(
    pdpi::IrP4Info ir_p4info,
    const std::vector<p4::v1::TableEntry>& pi_table_entries) {
  bool compact_output = absl::GetFlag(FLAGS_compact);
  for (const auto& pi_table_entry : pi_table_entries) {
    ASSIGN_OR_RETURN(pdpi::IrTableEntry ir_table_entry,
                     pdpi::PiTableEntryToIr(ir_p4info, pi_table_entry));
    if (compact_output) {
      Info(ir_table_entry.ShortDebugString());
    } else {
      Info(ir_table_entry.DebugString());
    }
  }
  return absl::OkStatus();
}

absl::Status PrintAsPi(
    const std::vector<p4::v1::TableEntry>& pi_table_entries) {
  bool compact_output = absl::GetFlag(FLAGS_compact);
  for (const auto& pi_table_entry : pi_table_entries) {
    if (compact_output) {
      Info(pi_table_entry.ShortDebugString());
    } else {
      Info(pi_table_entry.DebugString());
    }
  }
  return absl::OkStatus();
}

absl::Status Main() {
  // Connect to the P4RT server.
  ASSIGN_OR_RETURN(std::unique_ptr<pdpi::P4RuntimeSession> session,
                   CreateP4rtSession());
  ASSIGN_OR_RETURN(std::vector<p4::v1::TableEntry> pi_table_entries,
                   pdpi::ReadPiTableEntries(session.get()));

  // Filter any entries based on PI values.
  FilterByTableId(pi_table_entries);

  std::string format_as = absl::GetFlag(FLAGS_format);
  absl::AsciiStrToUpper(&format_as);
  if (format_as == "IR") {
    ASSIGN_OR_RETURN(pdpi::IrP4Info ir_p4info, GetIrP4infoFromSwitch(*session));
    RETURN_IF_ERROR(PrintAsIr(ir_p4info, pi_table_entries));
  } else if (format_as == "PI") {
    RETURN_IF_ERROR(PrintAsPi(pi_table_entries));
  } else {
    return gutil::InvalidArgumentErrorBuilder()
           << "Unsuported --format_as flag format '" << format_as << "'.";
  }

  return absl::OkStatus();
}

}  // namespace
}  // namespace p4rt_app

int main(int argc, char** argv) {
  absl::InitializeLog();
  absl::ParseCommandLine(argc, argv);

  absl::Status status = p4rt_app::Main();
  if (!status.ok()) {
    p4rt_app::Error(status.ToString());
    return status.raw_code();
  }

  p4rt_app::Info("Completed successfully.");
  return 0;
}
