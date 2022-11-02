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
#include <cstring>
#include <memory>
#include <vector>

#include "absl/flags/parse.h"
#include "absl/strings/str_split.h"
#include "gflags/gflags.h"
#include "glog/logging.h"
#include "google/protobuf/text_format.h"
#include "grpcpp/grpcpp.h"
#include "gutil/io.h"
#include "gutil/proto.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/pd.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"

DEFINE_bool(push_config, false, "Push P4 Info config file");
DEFINE_bool(cleanup, false, "Clean the entries that were programmed");
DEFINE_string(
    input_file, "",
    "Input file in SAI PD format(sai::Update proto), see go/p4rt-sample-entry");
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
                  bool cleanup)
      : p4rt_session_(std::move(p4rt_session)), cleanup_(cleanup) {}

  ~P4rtTableWriter() {
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
};

int main(int argc, char** argv) {
  google::InitGoogleLogging(argv[0]);
  gflags::ParseCommandLineFlags(&argc, &argv, true);

  // Create connection to P4RT server.
  auto stub = pdpi::CreateP4RuntimeStub(
      "unix:/sock/p4rt.sock", grpc::experimental::LocalCredentials(UDS));
  auto p4rt_session_or =
      pdpi::P4RuntimeSession::Create(std::move(stub),
                                     /*device_id=*/183807201);
  if (!p4rt_session_or.ok()) {
    LOG(ERROR) << "Failed to create P4Runtime session, error : "
               << p4rt_session_or.status();
    return -1;
  }
  std::unique_ptr<pdpi::P4RuntimeSession> p4rt_session =
      std::move(*p4rt_session_or);

  const p4::config::v1::P4Info& p4info =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);
  const pdpi::IrP4Info& ir_p4info =
      sai::GetIrP4Info(sai::Instantiation::kMiddleblock);

  // Push P4 Info Config file if specified.
  if (FLAGS_push_config) {
    auto push_p4info_status = pdpi::SetForwardingPipelineConfig(
        p4rt_session.get(),
        p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
        p4info);
    if (!push_p4info_status.ok()) {
      LOG(ERROR) << "Failed to push P4Info to the switch, error : "
                 << push_p4info_status.ToString();
      return push_p4info_status.raw_code();
    }
  }

  auto pd_entries_or = ConvertToPdEntries(FLAGS_input_file);
  if (!pd_entries_or.ok()) {
    LOG(ERROR) << "Failed to convert input entries to SAI PD, error : "
               << pd_entries_or.status();
    return -1;
  }
  std::vector<sai::Update> pd_entries = std::move(*pd_entries_or);

  P4rtTableWriter writer(std::move(p4rt_session), FLAGS_cleanup);
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
