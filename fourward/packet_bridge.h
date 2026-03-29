// Copyright 2026 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// PacketBridge: emulates back-to-back physical links between two 4ward
// P4RuntimeServer instances.
//
// When the SUT outputs a packet on port X, the bridge injects it into the
// control switch on port X (and vice versa). This lets upstream DVaaS's
// standard packet injection flow work unmodified:
//
//   DVaaS -> control_switch PacketOut -> bridge -> SUT ingress
//   SUT egress -> bridge -> control_switch ingress -> punt-all -> PacketIn -> DVaaS
//
// Uses 4ward's DataplaneService.SubscribeResults to observe output packets
// and DataplaneService.InjectPackets (streaming) to forward them.

#ifndef PINS_FOURWARD_PACKET_BRIDGE_H_
#define PINS_FOURWARD_PACKET_BRIDGE_H_

#include <atomic>
#include <cstdint>
#include <mutex>
#include <string>
#include <thread>

#include "absl/status/status.h"
#include "absl/synchronization/notification.h"
#include "grpcpp/client_context.h"

namespace dvaas {

// Bridges packet traffic between two 4ward instances.
//
// Usage:
//   PacketBridge bridge("localhost:9559", "localhost:9560");
//   RETURN_IF_ERROR(bridge.Start());
//   // ... run DVaaS validation ...
//   bridge.Stop();
//
// The bridge spawns two threads (one per direction) that subscribe to
// SubscribeResults on each instance and forward output packets to the other.
class PacketBridge {
 public:
  PacketBridge(std::string sut_address, std::string control_address);
  ~PacketBridge();

  // Starts the bridge. Returns OK once both subscriptions are active.
  absl::Status Start();

  // Stops the bridge and joins the forwarding threads.
  void Stop();

  // Returns the number of packets forwarded (both directions combined).
  int64_t PacketsForwarded() const { return packets_forwarded_.load(); }

  // Returns the number of packets that failed to inject.
  int64_t InjectFailures() const { return inject_failures_.load(); }

 private:
  // Subscribes to SubscribeResults on `from` and forwards each output packet
  // to `to` via a streaming InjectPackets writer.
  void ForwardLoop(const std::string& from_address,
                   const std::string& to_address,
                   const std::string& direction_label,
                   absl::Notification& ready);

  std::string sut_address_;
  std::string control_address_;
  std::atomic<bool> running_{false};
  std::atomic<int64_t> packets_forwarded_{0};
  std::atomic<int64_t> inject_failures_{0};
  std::thread sut_to_control_;
  std::thread control_to_sut_;

  // ClientContext pointers for active SubscribeResults streams.
  // Stop() calls TryCancel() on these to unblock Read().
  std::mutex contexts_mu_;
  grpc::ClientContext* sut_subscribe_ctx_ = nullptr;
  grpc::ClientContext* control_subscribe_ctx_ = nullptr;

  // Signaled by each ForwardLoop when its SubscribeResults stream is active.
  absl::Notification sut_to_control_ready_;
  absl::Notification control_to_sut_ready_;
};

}  // namespace dvaas

#endif  // PINS_FOURWARD_PACKET_BRIDGE_H_
