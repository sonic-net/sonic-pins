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
#include "tests/lib/packet_in_helper.h"

#include "absl/status/status.h"
#include "absl/synchronization/mutex.h"
#include "glog/logging.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"

namespace pins {

PacketInHelper::PacketInHelper(
    pdpi::P4RuntimeSession* p4rt_session,
    std::function<bool(const p4::v1::StreamMessageResponse&)>
        packet_in_message_filter)
    : p4rt_session_(*p4rt_session),
      packet_in_message_filter_(std::move(packet_in_message_filter)) {
  CHECK(p4rt_session != nullptr);  // Crash OK in ctor.

  packet_in_thread_ = std::thread([&]() {
    LOG(INFO) << "Start monitoring PacketIO events.";
    p4::v1::StreamMessageResponse response;
    while (p4rt_session_.StreamChannelRead(response)) {
      if (packet_in_message_filter_(response)) {
        PushBackPacketInMessage(response);
      }
    }
  });
}

PacketInHelper::~PacketInHelper() {
  // If the thread was never started then there isn't any other cleanup needed.
  if (!packet_in_thread_.joinable()) return;

  // Otherwise we try to stop the P4RT session, and join back the thread.
  absl::Status stop_session = p4rt_session_.Finish();
  if (!stop_session.ok()) {
    LOG(ERROR) << "Problem stopping the P4RT session: " << stop_session;
    return;
  }

  packet_in_thread_.join();
  LOG(INFO) << "Stopped monitoring PacketIO events.";
}

bool PacketInHelper::NoFilter(const p4::v1::StreamMessageResponse& response) {
  return true;
}

bool PacketInHelper::HasPacketInMessage() const {
  absl::MutexLock l(&packet_in_lock_);
  return !packet_in_messages_.empty();
}

absl::StatusOr<p4::v1::StreamMessageResponse>
PacketInHelper::GetNextPacketInMessage() {
  absl::MutexLock l(&packet_in_lock_);

  // If the queue is empty then we return an error.
  if (packet_in_messages_.empty()) {
    return absl::Status(absl::StatusCode::kOutOfRange,
                        "The PacketIn queue is empty.");
  }

  // Otherwise, we return the next packet in the queue.
  p4::v1::StreamMessageResponse message = packet_in_messages_.front();
  packet_in_messages_.pop();
  return message;
}

void PacketInHelper::PushBackPacketInMessage(
    const p4::v1::StreamMessageResponse& response) {
  absl::MutexLock l(&packet_in_lock_);
  packet_in_messages_.push(response);
}

}  // namespace pins
