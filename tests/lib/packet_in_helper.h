// Copyright 2024 Google LLC
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
#ifndef PINS_TESTS_LIB_PACKET_IO_HELPER_H_
#define PINS_TESTS_LIB_PACKET_IO_HELPER_H_

#include <functional>
#include <queue>
#include <thread> // NOLINT: third_party code.

#include "absl/status/statusor.h"
#include "absl/synchronization/mutex.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"

namespace pins {

// A helper class for managing P4RT PacketIO requests. On construction it will
// spawn a thread to asynchronously collect PacketIn messages from the switch.
//
// NOTE: This class will not take ownership of a P4RT session, but on
// destruction it will close the gRPC stream channel to the switch.
class PacketInHelper final {
public:
  // Spawns a thread to collect PacketIn messages sent from the switch.
  //
  // A filter can be used to limit the type of messages collected. The filter
  // should return true for any packets the test wants to collect, and false for
  // any packets the test wants to ignore.
  explicit PacketInHelper(
      pdpi::P4RuntimeSession *p4rt_session,
      std::function<bool(const p4::v1::StreamMessageResponse &)>
          packet_in_message_filter);

  // Closes the P4RuntimeSession's stream, and joins the PacketIn thread.
  ~PacketInHelper();

  // Always returns true so no packet gets filtered out.
  static bool NoFilter(const p4::v1::StreamMessageResponse &response);

  // Returns true if the PacketIn queue has packets. Otherwise it returns false.
  bool HasPacketInMessage() const ABSL_LOCKS_EXCLUDED(packet_in_lock_);

  // Returns the next packet in the queue. If no packet exists in the queue it
  // will return an OUT_OF_BOUNDS error.
  absl::StatusOr<p4::v1::StreamMessageResponse> GetNextPacketInMessage()
      ABSL_LOCKS_EXCLUDED(packet_in_lock_);

private:
  // Helper method used by the PacketIn thread to update the PacketIn messages.
  void PushBackPacketInMessage(const p4::v1::StreamMessageResponse &response)
      ABSL_LOCKS_EXCLUDED(packet_in_lock_);

  pdpi::P4RuntimeSession &p4rt_session_;

  // Thread is spawned in ctor and joined in dtor. It will wait for a PacketIn
  // message then update the PacketIn message queue.
  std::thread packet_in_thread_;

  // Accessing the packet-in queue is lock protected because the P4RT server is
  // sending new packets while the tests can be reading them back.
  mutable absl::Mutex packet_in_lock_;

  // Hold all PacketIn messages until the test reads them out.
  std::queue<p4::v1::StreamMessageResponse>
      packet_in_messages_ ABSL_GUARDED_BY(packet_in_lock_);

  // A filter to restrict which packets are actually collected by the
  // PacketInHelper class.
  //
  // return true to collect the packet.
  // return false to ignore the packet.
  std::function<bool(const p4::v1::StreamMessageResponse &)>
      packet_in_message_filter_;
};

} // namespace pins

#endif // PINS_TESTS_LIB_PACKET_IO_HELPER_H_
