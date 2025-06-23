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

#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "absl/log/initialize.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/ascii.h"
#include "absl/strings/str_format.h"
#include "grpcpp/security/credentials.h"
#include "gutil/gutil/io.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_runtime/p4_runtime_session.h"
#include "p4rt_app/scripts/p4rt_tool_helpers.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"

// Flag to select the SetForwardingPipelineConfig action.
ABSL_FLAG(
    std::string, forwarding_action, "",
    "Forwarding action to apply to the config. Values[VERIFY, VERIFY_AND_SAVE, "
    "VERIFY_AND_COMMIT, COMMIT, RECONCILE_AND_COMMIT]");

// Flags to select the P4Info.
ABSL_FLAG(bool, default_middleblock_p4info, false,
          "Use a default middleblock P4Info. Shouldn't be used with other "
          "P4Info flags.");
ABSL_FLAG(bool, default_fbr_p4info, false,
          "Use a default fabric boarder router P4Info. Shouldn't be used "
          "with other P4Info flags.");
ABSL_FLAG(std::string, p4info_file, "",
          "Reads a p4::v1::P4Info config from a file (in text format). "
          "Shouldn't be used with other P4Info flags.");

namespace p4rt_app {
namespace {

absl::StatusOr<p4::config::v1::P4Info> GetP4Info() {
  // Check for a default P4Info flag.
  if (absl::GetFlag(FLAGS_default_middleblock_p4info)) {
    Info("Loading a default Middleblock P4Info.");
    return sai::GetP4Info(sai::Instantiation::kMiddleblock);
  } else if (absl::GetFlag(FLAGS_default_fbr_p4info)) {
    Info("Loading a default Fabric Boarder Router P4Info.");
    return sai::GetP4Info(sai::Instantiation::kFabricBorderRouter);
  }

  // Otherwise, load the P4Info from a flag if requested.
  p4::config::v1::P4Info p4info;
  std::string p4info_file = absl::GetFlag(FLAGS_p4info_file);
  if (!p4info_file.empty()) {
    Info(absl::StrCat("Loading P4Info from: ", p4info_file));
    RETURN_IF_ERROR(gutil::ReadProtoFromFile(p4info_file, &p4info));
  }
  return p4info;
}

absl::StatusOr<p4::v1::SetForwardingPipelineConfigRequest::Action>
GetSetAction() {
  std::string forwarding_action = absl::GetFlag(FLAGS_forwarding_action);
  if (forwarding_action.empty()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "The --forwarding_action flag is not set.";
  }

  absl::AsciiStrToUpper(&forwarding_action);
  if (forwarding_action == "VERIFY") {
    return p4::v1::SetForwardingPipelineConfigRequest::VERIFY;
  } else if (forwarding_action == "VERIFY_AND_SAVE") {
    return p4::v1::SetForwardingPipelineConfigRequest::VERIFY_AND_SAVE;
  } else if (forwarding_action == "VERIFY_AND_COMMIT") {
    return p4::v1::SetForwardingPipelineConfigRequest::VERIFY_AND_COMMIT;
  } else if (forwarding_action == "COMMIT") {
    return p4::v1::SetForwardingPipelineConfigRequest::COMMIT;
  } else if (forwarding_action == "RECONCILE_AND_COMMIT") {
    return p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT;
  }

  return gutil::InvalidArgumentErrorBuilder()
         << "Unsupported --forwarding_action value '" << forwarding_action
         << "'.";
}

// Parses through the command line flags, and tries to apply them.
//
// NOTE: Flags are not applied in order, and only the first viable option will
// be choosen. For example, if a user tries to use both the default middleblock
// and fbr configs only one will be selected.
absl::Status Main() {
  ASSIGN_OR_RETURN(p4::v1::SetForwardingPipelineConfigRequest::Action action,
                   GetSetAction());

  // Only include the P4Info for specific requests.
  p4::v1::ForwardingPipelineConfig config;
  switch (action) {
    case p4::v1::SetForwardingPipelineConfigRequest::VERIFY:
    case p4::v1::SetForwardingPipelineConfigRequest::VERIFY_AND_COMMIT:
    case p4::v1::SetForwardingPipelineConfigRequest::VERIFY_AND_SAVE:
    case p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT: {
      ASSIGN_OR_RETURN(*config.mutable_p4info(), GetP4Info());
      break;
    }
    default:
      // do nothing.
      break;
  }

  ASSIGN_OR_RETURN(std::unique_ptr<p4_runtime::P4RuntimeSession> session,
                   CreateP4rtSession());
  return p4_runtime::SetMetadataAndSetForwardingPipelineConfig(session.get(),
                                                               action, config);
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
