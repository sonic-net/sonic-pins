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
#include "lib/p4rt/packet_listener.h"

#include <functional>
#include <string>
#include <utility>

#include "absl/container/flat_hash_map.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/testing.h"
#include "lib/p4rt/p4rt_programming_context.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "p4_infra/p4_pdpi/pd.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"

namespace pins_test {

PacketListener::PacketListener(
    pdpi::P4RuntimeSession* session, P4rtProgrammingContext context,
    sai::Instantiation instantiation,
    const absl::flat_hash_map<std::string, std::string>*
        interface_port_id_to_name)
    : session_(session),
      context_(std::move(context)),
      instantiation_(instantiation),
      interface_port_id_to_name_(*interface_port_id_to_name) {}

absl::Status PacketListener::HandlePacketsFor(
    absl::Duration duration, thinkit::PacketCallback callback) {
  ASSIGN_OR_RETURN(std::vector<p4::v1::StreamMessageResponse> messages,
                   session_->GetAllStreamMessagesFor(duration));
  for (const auto& pi_response : messages) {
    sai::StreamMessageResponse pd_response;
    if (!pdpi::PiStreamMessageResponseToPd(sai::GetIrP4Info(instantiation_),
                                           pi_response, &pd_response)
             .ok()) {
      LOG(ERROR) << "Failed to convert PI stream message response to PD.";
      continue;
    }
    if (!pd_response.has_packet()) {
      LOG(ERROR) << "PD response has no packet.";
      continue;
    }
    std::string port_id = pd_response.packet().metadata().ingress_port();

    auto port_name = interface_port_id_to_name_.find(port_id);
    if (port_name == interface_port_id_to_name_.end()) {
      LOG(WARNING) << port_id << " not found.";
      continue;
    }
    LOG_EVERY_POW_2(INFO) << "Packet received (Count: " << COUNTER << ").";
    callback(port_name->second, pd_response.packet().payload());
  }

  return absl::OkStatus();
}

}  // namespace pins_test
