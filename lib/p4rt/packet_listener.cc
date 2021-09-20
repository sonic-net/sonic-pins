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

#include "absl/base/thread_annotations.h"
#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/strings/escaping.h"
#include "absl/synchronization/mutex.h"
#include "glog/logging.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/pd.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "thinkit/control_device.h"

namespace pins_test {

PacketListener::PacketListener(
    pdpi::P4RuntimeSession* session, const pdpi::IrP4Info* ir_p4info,
    const absl::flat_hash_map<std::string, std::string>*
        interface_port_id_to_name,
    thinkit::PacketCallback callback)
    : session_(session),
      time_to_exit_(false),
      receive_packet_thread_([this, ir_p4info, interface_port_id_to_name,
                              callback = std::move(
                                  callback)]() ABSL_LOCKS_EXCLUDED(mutex_) {
        p4::v1::StreamMessageResponse pi_response;
        while (session_->StreamChannelRead(pi_response)) {
          {
            absl::MutexLock lock(&mutex_);
            if (time_to_exit_) {
              break;
            }
          }

          sai::StreamMessageResponse pd_response;
          if (!pdpi::PiStreamMessageResponseToPd(*ir_p4info, pi_response,
                                                 &pd_response)
                   .ok()) {
            LOG(ERROR) << "Failed to convert PI stream message response to PD.";
            return;
          }
          if (!pd_response.has_packet()) {
            LOG(ERROR) << "PD response has no packet.";
            return;
          }
          std::string port_id = pd_response.packet().metadata().ingress_port();

          LOG(INFO) << "Packet received from port id: " << port_id;
          auto port_name = interface_port_id_to_name->find(port_id);
          if (port_name == interface_port_id_to_name->end()) {
            LOG(WARNING) << port_id << " not found.";
            return;
          }
          callback(port_name->second,
                   absl::BytesToHexString(pd_response.packet().payload()));
        }
      }) {}

}  // namespace pins_test
