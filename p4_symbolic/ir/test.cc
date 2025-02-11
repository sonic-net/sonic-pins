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

// Test file for producing IR representations of P4 Programs.

#include <sstream>
#include <string>
#include <vector>

#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "absl/flags/usage.h"
#include "absl/status/status.h"
#include "absl/strings/str_format.h"
#include "gutil/io.h"
#include "gutil/proto.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/ir/parser.h"
#include "p4_symbolic/test_util.h"

ABSL_FLAG(std::string, p4info, "",
          "The path to the p4info protobuf file (required)");
ABSL_FLAG(std::string, bmv2, "", "The path to the bmv2 json file (required)");
ABSL_FLAG(std::string, entries, "",
          "The path to the table entries txt file (optional), leave this empty "
          "if the input p4 program contains no (explicit) tables for which "
          "entries are needed.");
ABSL_FLAG(std::string, output, "", "The output file for parsed IR.");

namespace {

using ::gutil::PrintTextProto;

absl::Status Test() {
  const std::string &p4info_path = absl::GetFlag(FLAGS_p4info);
  const std::string &bmv2_path = absl::GetFlag(FLAGS_bmv2);
  const std::string &entries_path = absl::GetFlag(FLAGS_entries);
  const std::string &output_path = absl::GetFlag(FLAGS_output);

  RET_CHECK(!p4info_path.empty());
  RET_CHECK(!bmv2_path.empty());
  RET_CHECK(!output_path.empty());

  // Transform to IR and print.
  ASSIGN_OR_RETURN(
      p4::v1::ForwardingPipelineConfig config,
      p4_symbolic::ParseToForwardingPipelineConfig(bmv2_path, p4info_path));
  ASSIGN_OR_RETURN(
      std::vector<p4::v1::Entity> entities,
      p4_symbolic::GetPiEntitiesFromPiUpdatesProtoTextFile(entries_path));
  ASSIGN_OR_RETURN(p4_symbolic::ir::Dataplane dataplane,
                   p4_symbolic::ir::ParseToIr(config, entities));

  // Dump string representation to the output file.
  std::ostringstream output;
  output << PrintTextProto(dataplane.program) << std::endl;
  for (const auto &[name, entries] : dataplane.entries) {
    output << "=====" << name << " Entries=====" << std::endl;
    output << std::endl;
    for (const p4_symbolic::ir::TableEntry &entry : entries) {
      output << PrintTextProto(entry) << std::endl;
    }
  }
  RETURN_IF_ERROR(gutil::WriteFile(output.str(), output_path));

  return absl::OkStatus();
}

}  // namespace

int main(int argc, char *argv[]) {
  // Verify link and compile versions are the same.
  // GOOGLE_PROTOBUF_VERIFY_VERSION;

  // Command line arguments and help message.
  absl::SetProgramUsageMessage(absl::StrFormat(
      "usage: %s %s", argv[0],
      "--bmv2=path/to/bmv2.json --p4info=path/to/p4info.pb.txt "
      "--output=path/to/output.txt [--entries=path/to/table_entries.txt]"));
  absl::ParseCommandLine(argc, argv);

  // Run test.
  absl::Status status = Test();

  // Error handling.
  if (!status.ok()) {
    std::cerr << "Error: " << status << std::endl;
    return 1;
  }

  return 0;
}
