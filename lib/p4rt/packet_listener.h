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
#ifndef GOOGLE_LIB_P4RT_PACKET_LISTENER_H_
#define GOOGLE_LIB_P4RT_PACKET_LISTENER_H_

#include <string>
#include <thread>  // NOLINT

#include "absl/base/thread_annotations.h"
#include "absl/container/flat_hash_map.h"
#include "absl/synchronization/mutex.h"
#include "glog/logging.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/pd.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "thinkit/control_device.h"
#include "thinkit/packet_generation_finalizer.h"
#include "thinkit/switch.h"

namespace pins_test {

// PacketListener will callback once a packet is received and stop listening for
// packets when it goes out of scope.
class PacketListener : public thinkit::PacketGenerationFinalizer {
 public:
  // Calls PacketCallback once a packet is received. Parameters passed in
  // (besides the callback) cannot be null and need to outlive this class.
  PacketListener(pdpi::P4RuntimeSession* session,
                 const pdpi::IrP4Info* ir_p4info,
                 const absl::flat_hash_map<std::string, std::string>*
                     interface_port_id_to_name,
                 thinkit::PacketCallback callback);

  ~PacketListener() ABSL_LOCKS_EXCLUDED(mutex_) {
    {
      absl::MutexLock lock(&mutex_);
      time_to_exit_ = true;
    }
    LOG(INFO) << "receive packet thread join.";
    receive_packet_thread_.join();
  } 

 private:
  pdpi::P4RuntimeSession* session_;
  bool time_to_exit_ ABSL_GUARDED_BY(mutex_);
  absl::Mutex mutex_;
  std::thread receive_packet_thread_;
};

}  // namespace pins_test

#endif  // GOOGLE_LIB_P4RT_PACKET_LISTENERR_H_
