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

#include <iostream>
#include <string>

#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "absl/flags/usage.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "absl/strings/str_split.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "gutil/gutil/proto.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_infra/p4_pdpi/p4info_union_lib.h"

ABSL_FLAG(std::string, list_of_p4infos, "",
          "Comma-separated list of P4Infos files (required)");

using ::gutil::PrintTextProto;
using ::p4::config::v1::P4Info;

constexpr absl::string_view kUsage =
    "--list_of_p4infos=<comma-separated file list>";

int main(int argc, char** argv) {
  absl::SetProgramUsageMessage(
      absl::Substitute("usage: $0 $1", argv[0], kUsage));
  absl::ParseCommandLine(argc, argv);

  // Get p4info file name.
  if (absl::GetFlag(FLAGS_list_of_p4infos).empty()) {
    std::cerr
        << "Missing argument: --list_of_p4infos=<comma-separated file list>"
        << std::endl;
    return 1;
  }
  std::vector<std::string> p4info_files =
      absl::StrSplit(absl::GetFlag(FLAGS_list_of_p4infos), ',');

  // Generate p4infos from file names.
  std::vector<P4Info> p4infos;
  for (const auto& p4info_file : p4info_files) {
    absl::Status status =
        gutil::ReadProtoFromFile(p4info_file, &p4infos.emplace_back());
    if (!status.ok()) {
      std::cerr << absl::Substitute(
          "Failed to parse p4info_file: '$0'. Status: $1\n", p4info_file,
          status.message());
      return 1;
    }
  }

  auto p4info_union = pdpi::UnionP4info(p4infos);
  if (!p4info_union.ok()) {
    std::cerr << absl::Substitute("Failed to union p4info files:'$0'\n",
                                  p4info_union.status().message());
    return 1;
  }
  std::cout << PrintTextProto(*p4info_union);
  return 0;
}
