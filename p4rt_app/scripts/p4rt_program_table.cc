// Copyright 2021 Google LLC
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
#include <cstdint>
#include <cstring>
#include <memory>
#include <string>
#include <vector>

#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "absl/log/initialize.h"
#include "absl/log/log.h"
#include "absl/status/statusor.h"
#include "absl/strings/match.h"
#include "absl/strings/str_split.h"
#include "google/protobuf/text_format.h"
#include "grpcpp/grpcpp.h"
#include "gutil/gutil/io.h"
#include "gutil/gutil/proto.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "p4_infra/p4_pdpi/pd.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"

ABSL_FLAG(bool, push_config, false, "Push P4 Info config file");
ABSL_FLAG(bool, cleanup, false, "Clean the entries that were programmed");
ABSL_FLAG(bool, cleanall, false,
          "Clean all the entries that exist in the switch");
ABSL_FLAG(
    std::string, input_file, "",
    "Input file in SAI PD format(sai::Update proto), see go/p4rt-sample-entry");
ABSL_FLAG(uint64_t, p4rt_device_id, 1, "P4RT device ID");
ABSL_FLAG(sai::Instantiation, switch_instantiation,
          sai::Instantiation::kMiddleblock,
          "The switch instantiation to test.");

namespace {

// Read input file and group PD table entries, split by the special
// line identifier '***'.
absl::StatusOr<std::vector<sai::Update>> ConvertToPdEntries(
    const std::string& input_file) {
  absl::StatusOr<std::string> in_str_or = gutil::ReadFile(input_file);
  std::vector<std::string> in_lines = absl::StrSplit(*in_str_or, '\n');
  std::vector<sai::Update> pd_entries;
  std::string entry;
  for (const auto& line : in_lines) {
    if (line.empty()) continue;
    if (absl::StrContains(line, "***")) {
      if (!entry.empty()) {
        sai::Update pd_entry;
        RETURN_IF_ERROR(gutil::ReadProtoFromString(entry, &pd_entry));
        pd_entries.push_back(pd_entry);
        entry.clear();
      }
    } else {
      absl::StrAppend(&entry, line, "\n");
    }
  }
  // Add the last entry to PD table.
  if (!entry.empty()) {
    sai::Update pd_entry;
    RETURN_IF_ERROR(gutil::ReadProtoFromString(entry, &pd_entry));
    pd_entries.push_back(pd_entry);
  }
  return pd_entries;
}

}  // namespace

// Class to help in programming P4RT table entries on the switch.
class P4rtTableWriter {
 public:
  P4rtTableWriter(std::unique_ptr<pdpi::P4RuntimeSession> p4rt_session,
                  bool cleanup, bool cleanall)
      : p4rt_session_(std::move(p4rt_session)),
        cleanup_(cleanup),
        cleanall_(cleanall) {}

  ~P4rtTableWriter() {
    // Cleanup all entries, if specified.
    if (cleanall_) {
      auto status = pdpi::ClearEntities(*p4rt_session_);
      if (!status.ok()) {
        LOG(ERROR) << "Unable to clear enries on the switch: "
                   << status.ToString();
      }
      return;
    }
    // Cleanup the entries in reverse order, if specified.
    if (cleanup_) {
      for (auto it = pi_entries_.rbegin(); it != pi_entries_.rend(); ++it) {
        (*it).set_type(p4::v1::Update::DELETE);
        p4::v1::WriteRequest write_request;
        *write_request.add_updates() = *it;
        auto write_status = pdpi::SetMetadataAndSendPiWriteRequest(
            p4rt_session_.get(), write_request);
        if (!write_status.ok()) {
          LOG(ERROR) << "Error : " << write_status.ToString()
                     << " in deleting entry " << write_request.DebugString();
        }
      }
    }
  }

  // Convert PD entry to PI and write to switch.
  absl::Status SendP4WriteToSwitch(const pdpi::IrP4Info& ir_p4info,
                                   const sai::Update& pd_entry) {
    ASSIGN_OR_RETURN(auto pi_entry, pdpi::PdUpdateToPi(ir_p4info, pd_entry));
    p4::v1::WriteRequest write_request;
    write_request.set_device_id(p4rt_session_->DeviceId());
    *write_request.add_updates() = pi_entry;
    RETURN_IF_ERROR(pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                           write_request));
    pi_entries_.push_back(pi_entry);
    return absl::OkStatus();
  }

 private:
  std::unique_ptr<pdpi::P4RuntimeSession> p4rt_session_;
  std::vector<p4::v1::Update> pi_entries_;
  bool cleanup_ = false;
  bool cleanall_ = false;
};

int main(int argc, char** argv) {
  absl::InitializeLog();
  absl::ParseCommandLine(argc, argv);

  // Create connection to P4RT server.
  auto stub = pdpi::CreateP4RuntimeStub(
      "unix:/sock/p4rt.sock", grpc::experimental::LocalCredentials(UDS));
  auto p4rt_session_or = pdpi::P4RuntimeSession::Create(
      std::move(stub), absl::GetFlag(FLAGS_p4rt_device_id));
  if (!p4rt_session_or.ok()) {
    LOG(ERROR) << "Failed to create P4Runtime session, error : "
               << p4rt_session_or.status();
    return -1;
  }
  std::unique_ptr<pdpi::P4RuntimeSession> p4rt_session =
      std::move(*p4rt_session_or);

  sai::Instantiation switch_instantiation =
      absl::GetFlag(FLAGS_switch_instantiation);
  const p4::config::v1::P4Info& p4info = sai::GetP4Info(switch_instantiation);
  const pdpi::IrP4Info& ir_p4info = sai::GetIrP4Info(switch_instantiation);

  // Push P4 Info Config file if specified.
  if (absl::GetFlag(FLAGS_push_config)) {
    auto push_p4info_status = pdpi::SetMetadataAndSetForwardingPipelineConfig(
        p4rt_session.get(),
        p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
        p4info);
    if (!push_p4info_status.ok()) {
      LOG(ERROR) << "Failed to push P4Info to the switch, error : "
                 << push_p4info_status.ToString();
      return push_p4info_status.raw_code();
    }
  }

  auto pd_entries_or = ConvertToPdEntries(absl::GetFlag(FLAGS_input_file));
  if (!pd_entries_or.ok()) {
    LOG(ERROR) << "Failed to convert input entries to SAI PD, error : "
               << pd_entries_or.status();
    return -1;
  }
  std::vector<sai::Update> pd_entries = std::move(*pd_entries_or);

  P4rtTableWriter writer(std::move(p4rt_session), absl::GetFlag(FLAGS_cleanup),
                         absl::GetFlag(FLAGS_cleanall));
  absl::Status status;
  // Convert to PI and program the entries on the switch.
  for (const auto& pd_entry : pd_entries) {
    status = writer.SendP4WriteToSwitch(ir_p4info, pd_entry);
    if (!status.ok()) {
      LOG(ERROR) << "Error in programming entry to the switch : "
                 << status.ToString();
      break;
    }
  }

  return status.raw_code();
}
