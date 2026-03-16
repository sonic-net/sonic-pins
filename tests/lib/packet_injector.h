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
#ifndef PINS_TESTS_LIB_PACKET_INJECTOR_H_
#define PINS_TESTS_LIB_PACKET_INJECTOR_H_

#include <memory>
#include <optional>
#include <string>
#include <thread>  
#include <vector>

#include "absl/base/thread_annotations.h"
#include "absl/container/flat_hash_map.h"
#include "absl/functional/any_invocable.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/synchronization/mutex.h"
#include "absl/synchronization/notification.h"
#include "absl/time/time.h"
#include "lib/p4rt/p4rt_port.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_runtime/p4_runtime_session.h"
#include "tests/forwarding/util.h"
namespace pins_test {

// Injects the specified packets in a round-robin fashion.
// * Injection starts as soon as the class object is created.
// * Injection stops when the class is destroyed.
//
// Example usage: Simple packet generation
// TEST_F(MyTest, ForwardsPackets) {
//   // Set Up Forwarding
//
//   ASSERT_OK_AND_ASSIGN(auto injector, PacketInjector::Create(
//       control_switch_p4rt_session(), control_switch_ir_p4info(),
//       control_switch_egress_port, {packet1, packet2, packet3});
//   absl::SleepFor(absl::Minutes(1));
//   injector->Pause();
//   auto injected_packets = injector->InjectedPackets();
//
//   // Verify received packets against injected packets.
// }
//
// Example usage: Packet generation with pause & resume:
// TEST_F(MyTest, ForwardsPacketsAfterChange) {
//   // Set Up Forwarding
//   ASSERT_OK_AND_ASSIGN(auto injector, PacketInjector::Create(
//       control_switch_p4rt_session(), control_switch_ir_p4info(),
//       control_switch_egress_port, {packet1, packet2, packet3});
//   absl::SleepFor(absl::Minutes(1));
//   injector->Pause();
//
//   // Do other stuff
//   injector->ResumeInjection();
//   absl::SleepFor(absl::Minutes(1));
//   injector->Pause();
//   auto injected_packets = injector->InjectedPackets();
//
//   // Verify received packets against injected packets.
// }
class PacketInjector {
 public:
  // Factor method to create a PacketInjector.
  static absl::StatusOr<std::unique_ptr<PacketInjector>> Create(
      p4_runtime::P4RuntimeSession& injector_p4rt_session,
      pdpi::IrP4Info ir_p4info, P4rtPortId port,
      std::vector<std::string> packets,
      absl::Duration interval = absl::Milliseconds(10),
      absl::AnyInvocable<absl::Status(
          const std::string& /*port*/, const std::string& /*packet*/,
          const pdpi::IrP4Info&, p4_runtime::P4RuntimeSession*,
          std::optional<absl::Duration>)>
          injector = pins::InjectEgressPacket);

  ~PacketInjector();

  // Resume packet injection.
  void Resume() ABSL_LOCKS_EXCLUDED(mutex_);

  // Pause packet injection.
  void Pause() ABSL_LOCKS_EXCLUDED(mutex_);

  // Returns true if packet injection is paused.
  bool IsPaused() ABSL_LOCKS_EXCLUDED(mutex_);

  // Injection results.
  absl::Status InjectionError() ABSL_LOCKS_EXCLUDED(mutex_);
  absl::flat_hash_map<std::string, int> InjectedPackets()
      ABSL_LOCKS_EXCLUDED(mutex_);

 private:
  // Constructor allowing for a custom packet injector.
  PacketInjector(p4_runtime::P4RuntimeSession& injector_p4rt_session,
                 pdpi::IrP4Info ir_p4info, P4rtPortId port,
                 std::vector<std::string> packets, absl::Duration interval,
                 absl::AnyInvocable<absl::Status(
                     const std::string& /*port*/, const std::string& /*packet*/,
                     const pdpi::IrP4Info&, p4_runtime ::P4RuntimeSession*,
                     std::optional<absl::Duration>)>
                     injector);

  // This should only be called inside the thread.
  void DoInjection() ABSL_LOCKS_EXCLUDED(mutex_);

  p4_runtime::P4RuntimeSession& p4rt_session_;
  const pdpi::IrP4Info ir_p4info_;
  const P4rtPortId port_;
  const std::vector<std::string> packets_;
  const absl::Duration interval_;

  std::thread injection_thread_;

  mutable absl::Mutex mutex_;
  absl::Status injection_error_ ABSL_GUARDED_BY(mutex_);
  bool pause_ ABSL_GUARDED_BY(mutex_);
  absl::flat_hash_map<std::string, int> injection_counts_
      ABSL_GUARDED_BY(mutex_);

  absl::AnyInvocable<absl::Status(
      const std::string&, const std::string&, const pdpi::IrP4Info&,
      p4_runtime::P4RuntimeSession*, std::optional<absl::Duration>)>
      injector_;

  absl::Notification stop_;
};

}  // namespace pins_test

#endif  // PINS_TESTS_LIB_PACKET_INJECTOR_H_
