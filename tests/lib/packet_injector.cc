// Copyright 2025 Google LLC
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
#include "tests/lib/packet_injector.h"

#include <memory>
#include <optional>
#include <string>
#include <thread>  
#include <utility>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/functional/any_invocable.h"
#include "absl/log/log.h"
#include "absl/memory/memory.h"
#include "absl/status/status.h"
#include "absl/synchronization/mutex.h"
#include "absl/synchronization/notification.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "lib/p4rt/p4rt_port.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"

namespace pins_test {

absl::StatusOr<std::unique_ptr<PacketInjector>> PacketInjector::Create(
    pdpi::P4RuntimeSession& injector_p4rt_session, pdpi::IrP4Info ir_p4info,
    P4rtPortId port, std::vector<std::string> packets, absl::Duration interval,
    absl::AnyInvocable<
        absl::Status(const std::string& /*port*/, const std::string& /*packet*/,
                     const pdpi::IrP4Info&, pdpi::P4RuntimeSession*,
                     std::optional<absl::Duration>)>
        injector) {
  if (packets.empty()) {
    return absl::InvalidArgumentError(
        "Attempted to create PacketInjector with an empty packet vector.");
  }

  return absl::WrapUnique(new PacketInjector(
      injector_p4rt_session, std::move(ir_p4info), std::move(port),
      std::move(packets), interval, std::move(injector)));
}

PacketInjector::PacketInjector(
    pdpi::P4RuntimeSession& injector_p4rt_session, pdpi::IrP4Info ir_p4info,
    P4rtPortId port, std::vector<std::string> packets, absl::Duration interval,
    absl::AnyInvocable<absl::Status(
        const std::string&, const std::string&, const pdpi::IrP4Info&,
        pdpi::P4RuntimeSession*, std::optional<absl::Duration>)>
        injector)
    : p4rt_session_(injector_p4rt_session),
      ir_p4info_(std::move(ir_p4info)),
      port_(port),
      packets_(std::move(packets)),
      interval_(interval),
      injection_error_(absl::OkStatus()),
      pause_(false),
      injector_(std::move(injector)) {
  for (const auto& packet : packets_) {
    injection_counts_.insert_or_assign(packet, 0);
  }
  injection_thread_ = std::thread(&PacketInjector::DoInjection, this);
}

PacketInjector::~PacketInjector() {
  stop_.Notify();
  if (injection_thread_.joinable()) injection_thread_.join();
}

// Injects the specified packets in round-robin fashion.
void PacketInjector::DoInjection() {
  absl::Time deadline = absl::Now();

  auto packet = packets_.begin();
  while (!stop_.WaitForNotificationWithDeadline(deadline)) {
    deadline += interval_;
    if (IsPaused()) continue;

    absl::MutexLock lock(&mutex_);
    absl::Status result = injector_(port_.GetP4rtEncoding(), *packet,
                                    ir_p4info_, &p4rt_session_, std::nullopt);
    if (result.ok()) {
      ++injection_counts_.at(*packet);
      if (++packet == packets_.end()) packet = packets_.begin();
    } else {
      LOG(WARNING) << "Failed to inject packet. Pausing injection. " << result;
      injection_error_ = result;
      pause_ = true;
    }
  }
}

bool PacketInjector::IsPaused() {
  absl::MutexLock lock(&mutex_);
  return pause_;
}

void PacketInjector::Pause() {
  absl::MutexLock lock(&mutex_);
  pause_ = true;
}

void PacketInjector::Resume() {
  absl::MutexLock lock(&mutex_);
  pause_ = false;
}

absl::flat_hash_map<std::string, int> PacketInjector::InjectedPackets() {
  absl::MutexLock lock(&mutex_);
  return injection_counts_;
}

absl::Status PacketInjector::InjectionError() {
  absl::MutexLock lock(&mutex_);
  return injection_error_;
}

}  // namespace pins_test
