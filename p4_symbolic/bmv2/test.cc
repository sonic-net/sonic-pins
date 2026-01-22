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

// This is a test file for our protobuf specifications of bmv2 json.
// It reads an input bmv2 json file (usually the output of p4c) specified
// as a command line argument.
// It parses that file using protobuf, and then dumps the parsed protobuf
// objects using protobuf text format and json format to two output files.
// The output files paths are provided as command line flags.

#include <iostream>
#include <string>

#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "absl/flags/usage.h"
#include "absl/status/status.h"
#include "absl/strings/str_format.h"
#include "google/protobuf/util/json_util.h"
#include "gutil/io.h"
#include "gutil/proto.h"
#include "gutil/status.h"
#include "p4_symbolic/bmv2/bmv2.h"

ABSL_FLAG(std::string, bmv2, "", "The path to the bmv2 json file (required)");
ABSL_FLAG(std::string, protobuf, "",
          "The path to the output protobuf file (required)");
ABSL_FLAG(std::string, json, "", "The path to the output json file (required)");

namespace {

using ::gutil::PrintTextProto;

absl::Status Test() {
  const std::string &bmv2_path = absl::GetFlag(FLAGS_bmv2);
  const std::string &protobuf_path = absl::GetFlag(FLAGS_protobuf);
  const std::string &json_path = absl::GetFlag(FLAGS_json);

  RET_CHECK(!bmv2_path.empty());
  RET_CHECK(!protobuf_path.empty());
  RET_CHECK(!json_path.empty());

  // Parse JSON using bmv2.cc.
  ASSIGN_OR_RETURN(p4_symbolic::bmv2::P4Program bmv2,
                   p4_symbolic::bmv2::ParseBmv2JsonFile(bmv2_path.c_str()));

  // Dumping protobuf.
  RETURN_IF_ERROR(
      gutil::WriteFile(PrintTextProto(bmv2), protobuf_path.c_str()));

  // Dumping JSON.
  google::protobuf::util::JsonPrintOptions dumping_options;
  dumping_options.add_whitespace = true;
  dumping_options.always_print_primitive_fields = true;
  dumping_options.preserve_proto_field_names = true;

  std::string json_output_str;
  RETURN_IF_ERROR(
      gutil::ToAbslStatus(google::protobuf::util::MessageToJsonString(
          bmv2, &json_output_str, dumping_options)));
  RETURN_IF_ERROR(gutil::WriteFile(json_output_str, json_path.c_str()));

  return absl::OkStatus();
}

}  // namespace

int main(int argc, char *argv[]) {
  // Verify link and compile versions are the same.
  // GOOGLE_PROTOBUF_VERIFY_VERSION;

  // Command line arguments and help message.
  absl::SetProgramUsageMessage(
      absl::StrFormat("usage: %s %s", argv[0],
                      "--bmv2=path/to/bmv2.json "
                      "--protobuf=path/to/output.pb.txt "
                      "--json=path/to/output.json"));
  absl::ParseCommandLine(argc, argv);

  // Run test.
  absl::Status status = Test();

  // Clean up.
  google::protobuf::ShutdownProtobufLibrary();

  // Error handling.
  if (!status.ok()) {
    std::cerr << "Error: " << status << std::endl;
    return 1;
  }

  return 0;
}
