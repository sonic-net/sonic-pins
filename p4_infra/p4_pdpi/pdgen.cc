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

// Given a P4Info file, generates the corresponding PD proto.

#include <cstdint>
#include <iostream>
#include <optional>
#include <string>

#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "absl/flags/usage.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_join.h"
#include "absl/strings/str_split.h"
#include "absl/strings/string_view.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_infra/p4_pdpi/ir.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/pdgenlib.h"

ABSL_FLAG(std::string, p4info, "", "p4info file (required)");
ABSL_FLAG(std::string, package, "", "protobuf package name (required)");
ABSL_FLAG(std::string, roles, "",
          "the @p4runtime_role's for which to generate PD");
ABSL_FLAG(
    std::optional<int16_t>, multicast_table_field_number, 2047,
    "Optional field number used for multicast_group_table_entry in TableEntry "
    "oneof. If set to nullopt, then multicast_group_table_entry is omitted "
    "from PD proto. Defaults to 2047 to avoid conflicts with other tables and "
    "remain small");

constexpr char kUsage[] =
    "--p4info=<file> --package=<package> --roles=<comma-separated-role-list>";

using ::p4::config::v1::P4Info;

int main(int argc, char** argv) {
  absl::SetProgramUsageMessage(
      absl::StrJoin({"usage:", (const char*)argv[0], kUsage}, " "));
  absl::ParseCommandLine(argc, argv);

  // Get the package name.
  const std::string package = absl::GetFlag(FLAGS_package);
  if (package.empty()) {
    std::cerr << "Missing argument: --package=<package>" << std::endl;
    return 1;
  }

  // Get p4info file name.
  const std::string p4info_filename = absl::GetFlag(FLAGS_p4info);
  if (p4info_filename.empty()) {
    std::cerr << "Missing argument: --p4info=<file>" << std::endl;
    return 1;
  }

  // Parse p4info file.
  P4Info p4info;
  absl::Status status = gutil::ReadProtoFromFile(p4info_filename, &p4info);
  if (!status.ok()) {
    std::cerr << status << std::endl;
    return 1;
  }

  // Create IrP4Info
  absl::StatusOr<pdpi::IrP4Info> status_or_info = pdpi::CreateIrP4Info(p4info);
  if (!status_or_info.ok()) {
    std::cerr << "Failed to convert to IrP4Info: " << status_or_info.status()
              << std::endl;
    return 1;
  }
  pdpi::IrP4Info info = status_or_info.value();

  // Output PD proto.
  absl::StatusOr<std::string> status_or_pdproto = pdpi::IrP4InfoToPdProto(
      info, pdpi::PdGenOptions{
                .package = package,
                .roles = absl::StrSplit(absl::GetFlag(FLAGS_roles), ','),
                .multicast_table_field_number =
                    absl::GetFlag(FLAGS_multicast_table_field_number),
            });
  if (!status_or_pdproto.ok()) {
    std::cerr << "Failed to generate PD proto: " << status_or_pdproto.status()
              << std::endl;
    return 1;
  }
  std::cout << status_or_pdproto.value() << std::endl;

  return 0;
}
