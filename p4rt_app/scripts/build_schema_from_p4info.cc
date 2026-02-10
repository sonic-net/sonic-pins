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

// This program produces a p4rt_app::P4InfoVerificationSchema from a provided
// P4Info.

#include <iostream>
#include <string>

#include "absl/container/btree_map.h"
#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "absl/log/initialize.h"
#include "absl/log/log.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/substitute.h"
#include "google/protobuf/text_format.h"
#include "gutil/gutil/io.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_infra/p4_pdpi/ir.h"
#include "p4rt_app/p4runtime/p4info_verification_schema.h"
#include "p4rt_app/p4runtime/p4info_verification_schema.pb.h"

ABSL_FLAG(std::string, p4info, "",
          "The source p4info file. If not provided, the p4info will be "
          "read from stdin.");
ABSL_FLAG(std::string, output, "",
          "The output file to store the schema. If not provided, the "
          "schema will be written to stdout.");

namespace {
constexpr int kTabWidth = 2;

std::string Prefix(int tab_depth) {
  return std::string(kTabWidth * tab_depth, ' ');
}

// Produces the P4Info from the --p4info flag or from stdin. Logs an error and
// returns false if the P4Info cannot be produces.
bool GetP4Info(p4::config::v1::P4Info& p4info) {
  const std::string& input_filename = absl::GetFlag(FLAGS_p4info);
  if (input_filename.empty()) {
    std::string p4info_string;
    std::string line;
    while (std::getline(std::cin, line)) {
      absl::StrAppend(&p4info_string, line);
    }
    auto status = gutil::ReadProtoFromString(p4info_string, &p4info);
    if (!status.ok()) {
      LOG(ERROR) << "Failed to parse input as p4::config::v1::P4Info: "
                 << status.message();
      return false;
    }
  } else {
    auto status = gutil::ReadProtoFromFile(input_filename, &p4info);
    if (!status.ok()) {
      LOG(ERROR) << "Failed to read input file (" << input_filename
                 << ") as p4::config::v1::P4Info: " << status.message();
      return false;
    }
  }
  return true;
}

absl::StatusOr<std::string> ActionSchemaString(
    const p4rt_app::ActionSchema& action_schema, int tab_depth) {
  // We only support name and parameters.
  if (action_schema.GetDescriptor()->field_count() > 2) {
    return gutil::UnknownErrorBuilder()
           << "build_schema_from_p4info must be updated to support new "
              "field(s) in ActionSchema.";
  }

  // This is going to be within a short nest, so we don't worry about tab depth.
  if (action_schema.parameters().empty()) {
    std::string action_string;
    google::protobuf::TextFormat::Printer printer;
    printer.SetSingleLineMode(true);
    if (!printer.PrintToString(action_schema, &action_string)) {
      return gutil::InternalErrorBuilder()
             << "Failed to convert action schema to string.";
    }
    // Remove the extra whitespace at the end.
    if (action_string.back() == ' ') action_string.pop_back();
    return action_string;
  }

  std::string prefix = Prefix(tab_depth);
  absl::btree_map<std::string, std::string> parameter_strings;
  google::protobuf::TextFormat::Printer printer;
  printer.SetSingleLineMode(true);
  for (const auto& parameter : action_schema.parameters()) {
    if (!printer.PrintToString(parameter,
                               &parameter_strings[parameter.name()])) {
      return gutil::InternalErrorBuilder()
             << "Failed to convert action schema parameter ["
             << parameter.name() << "] to string.";
    }
  }
  std::string action_string =
      absl::Substitute("$0name: \"$1\"", prefix, action_schema.name());
  for (const auto& [parameter_name, parameter_string] : parameter_strings) {
    absl::StrAppendFormat(&action_string, "\n%sparameters { %s}", prefix,
                          parameter_string);
  }

  return action_string;
}

// Returns a readable string representation of the P4InfoVerificationSchema.
// This produces the same information as schema.DebugString() but prints
// repeated fields in a deterministic order (alphabetically by name).
absl::StatusOr<std::string> BuildTextSchema(
    const p4rt_app::P4InfoVerificationSchema& schema) {
  // We only support name, match_fields, and actions.
  if (schema.GetDescriptor()->field_count() > 1) {
    return gutil::UnknownErrorBuilder()
           << "build_schema_from_p4info must be updated to support new "
              "field(s) in P4InfoVerificationSchema.";
  }

  absl::btree_map<std::string, const p4rt_app::FixedTableSchema*> table_map;
  for (const auto& table : schema.tables()) {
    table_map[table.name()] = &table;
  }

  google::protobuf::TextFormat::Printer printer;
  printer.SetSingleLineMode(true);
  std::vector<std::string> table_strings;
  int tab_depth = 1;  // within tables { ... }
  for (const auto& [table_name, table] : table_map) {
    std::string prefix = Prefix(tab_depth);
    std::string table_string =
        absl::Substitute("$0name: \"$1\"\n", prefix, table_name);
    // We only support name, match_fields, and actions.
    if (table->GetDescriptor()->field_count() > 3) {
      return gutil::UnknownErrorBuilder()
             << "build_schema_from_p4info must be updated to support new "
                "field(s) in FixedTableSchema.";
    }

    absl::btree_map<std::string, std::string> match_map;
    for (const auto& match : table->match_fields()) {
      if (!printer.PrintToString(match, &match_map[match.name()])) {
        return gutil::InternalErrorBuilder()
               << "Unable to convert match_field [" << match.name()
               << "] to string.";
      }
    }
    for (const auto& [match_name, match_string] : match_map) {
      absl::StrAppendFormat(&table_string, "%smatch_fields { %s}\n", prefix,
                            match_string);
    }

    absl::btree_map<std::string, std::string> action_map;
    for (const auto& action : table->actions()) {
      ASSIGN_OR_RETURN(action_map[action.name()],
                       ActionSchemaString(action, tab_depth + 1));
    }
    for (const auto& [action_name, action_string] : action_map) {
      if (absl::StrContains(action_string, "parameters")) {
        absl::StrAppendFormat(&table_string, "%sactions {\n%s\n%s}\n", prefix,
                              action_string, prefix);
      } else {
        absl::StrAppendFormat(&table_string, "%sactions { %s }\n", prefix,
                              action_string);
      }
    }
    table_strings.push_back(table_string);
  }

  std::string schema_string;
  for (const std::string& table_string : table_strings) {
    absl::StrAppendFormat(&schema_string, "tables {\n%s}\n", table_string);
  }
  return schema_string;
}
}  // namespace

int main(int argc, char** argv) {
  absl::InitializeLog();
  absl::ParseCommandLine(argc, argv);

  // Get the P4Info.
  p4::config::v1::P4Info p4info;
  if (!GetP4Info(p4info)) return 1;

  // Create the IrP4Info from the P4Info.
  auto ir_result = pdpi::CreateIrP4Info(p4info);
  if (!ir_result.ok()) {
    LOG(ERROR) << "Failed to translate P4Info to IrP4Info: "
               << ir_result.status().message();
    return 1;
  }

  // Create the P4InfoVerificationSchema from the IrP4Info.
  auto schema_result = p4rt_app::ConvertToSchema(*ir_result);
  if (!schema_result.ok()) {
    LOG(ERROR) << "Failed to produce schema: "
               << schema_result.status().message();
    return 1;
  }

  // Output the schema.
  auto schema_string = BuildTextSchema(*schema_result);
  if (!schema_string.ok()) {
    LOG(ERROR) << schema_string.status().message();
    return 1;
  }

  std::string outfile = absl::GetFlag(FLAGS_output);
  if (outfile.empty()) {
    std::cout << *schema_string;
  } else {
    auto status = gutil::WriteFile(*schema_string, outfile);
    if (!status.ok()) {
      LOG(ERROR) << "Failed to write schema to file (" << outfile
                 << "): " << status.message();
      return 1;
    }
  }

  return 0;
}
