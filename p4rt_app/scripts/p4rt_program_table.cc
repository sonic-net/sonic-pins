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
#include <iostream>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "absl/log/initialize.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/status.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"

ABSL_FLAG(bool, push_config, false, "Push P4 Info config file");
ABSL_FLAG(bool, cleanup, false, "Clean the entries that were programmed");
ABSL_FLAG(bool, cleanall, false,
          "Clean all the entries that exist in the switch");
ABSL_FLAG(std::string, input_file, "",
          "Input file in IR format(IrEntities or IrWriteRequest proto), see "
          "go/p4rt-sample-entry");
ABSL_FLAG(uint64_t, p4rt_device_id, 1, "P4RT device ID");
ABSL_FLAG(sai::Instantiation, switch_instantiation,
          sai::Instantiation::kMiddleblock,
          "The switch instantiation to test.");

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
      std::cout << "Successfully cleared all entries on the switch."
                << std::endl;
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
      std::cout << "Successfully deleted " << pi_entries_.size()
                << " entries on the switch." << std::endl;
    }
  }

  // Convert IR entry to PI and write to switch.
  absl::Status SendP4WriteToSwitch(
      const pdpi::IrP4Info& ir_p4info,
      const pdpi::IrWriteRequest& ir_write_request) {
    p4::v1::WriteRequest write_request;
    write_request.set_device_id(p4rt_session_->DeviceId());
    for (const auto& updates : ir_write_request.updates()) {
      p4::v1::Update* update = write_request.add_updates();
      update->set_type(updates.type());
      ASSIGN_OR_RETURN(auto pi_update, pdpi::IrUpdateToPi(ir_p4info, updates));
      *update->mutable_entity() = std::move(pi_update.entity());
    }
    RETURN_IF_ERROR(pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                           write_request));
    // Save the entries for cleanup.
    for (const auto& update : write_request.updates()) {
      pi_entries_.push_back(update);
    }
    std::cout << "Successfully programmed " << pi_entries_.size()
              << " entries on the switch." << std::endl;
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

  pdpi::IrEntities ir_entities;
  pdpi::IrWriteRequest ir_write_request;
  absl::Status status =
      gutil::ReadProtoFromFile(absl::GetFlag(FLAGS_input_file), &ir_entities);
  if (!status.ok()) {
    // Try to read the file as IrWriteRequest.
    status = gutil::ReadProtoFromFile(absl::GetFlag(FLAGS_input_file),
                                      &ir_write_request);
    if (!status.ok()) {
      LOG(ERROR) << "Failed to convert input entries to IR format, error : "
                 << status.ToString();
      return -1;
    } else {
      std::cout << "Successfully read input file in IrWriteRequest format."
                << std::endl;
    }
  }

  // Convert IR entities (if present) to IR Write Request.
  if (ir_entities.entities_size() > 0) {
    for (const auto& entity : ir_entities.entities()) {
      pdpi::IrUpdate ir_update;
      ir_update.set_type(p4::v1::Update::INSERT);
      *ir_update.mutable_entity() = entity;
      *ir_write_request.add_updates() = std::move(ir_update);
    }
  }

  // Convert to PI and program the entries on the switch.

  P4rtTableWriter writer(std::move(p4rt_session), absl::GetFlag(FLAGS_cleanup),
                         absl::GetFlag(FLAGS_cleanall));
  status = writer.SendP4WriteToSwitch(ir_p4info, ir_write_request);
  if (!status.ok()) {
    LOG(ERROR) << "Error in programming entry to the switch : "
               << status.ToString();
    return -1;
  }

  return 0;
}
