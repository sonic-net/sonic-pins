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
// limitations under the License.
#include "tests/lib/packet_injector.h"

#include <optional>
#include <string>

#include "absl/functional/bind_front.h"
#include "absl/status/status.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status_matchers.h"
#include "lib/p4rt/p4rt_port.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_runtime/p4_runtime_session.h"
#include "p4_infra/p4_runtime/p4_runtime_session_mocking.h"

namespace pins_test {
namespace {

using ::testing::AllOf;
using ::testing::Ge;
using ::testing::Gt;
using ::testing::Le;
using ::testing::Pair;
using ::testing::UnorderedElementsAre;

// Many of these tests will verify threaded behaviors. Instead of having each
// test sleep for a fixed amount of time we will poll for the expected state.
// However, in case something breaks this timeout will be the longest any test
// will wait for a given state.
constexpr absl::Duration kTimeout = absl::Seconds(1);

absl::Status OkInjector(const std::string& /*port*/,
                        const std::string& /*packet*/, const pdpi::IrP4Info&,
                        p4_runtime::P4RuntimeSession*,
                        std::optional<absl::Duration>) {
  return absl::OkStatus();
}

absl::Status CountingOkInjector(int& call_count, const std::string& /*port*/,
                                const std::string& /*packet*/,
                                const pdpi::IrP4Info&,
                                p4_runtime::P4RuntimeSession*,
                                std::optional<absl::Duration>) {
  ++call_count;
  return absl::OkStatus();
}

TEST(PacketInjector, CanDestructWhilePaused) {
  ASSERT_OK_AND_ASSIGN(auto mock, p4_runtime::MakeP4SessionWithMockStub({}));
  ASSERT_OK_AND_ASSIGN(auto port, P4rtPortId::MakeFromP4rtEncoding("12"));
  ASSERT_OK_AND_ASSIGN(
      auto injector, PacketInjector::Create(
                         *mock.p4rt_session, pdpi::IrP4Info(), port,
                         {"abcd", "efgh"}, absl::ZeroDuration(), &OkInjector));
  injector->Pause();
}

TEST(PacketInjector, CanDestructWhileRunning) {
  ASSERT_OK_AND_ASSIGN(auto mock, p4_runtime::MakeP4SessionWithMockStub({}));
  ASSERT_OK_AND_ASSIGN(auto port, P4rtPortId::MakeFromP4rtEncoding("12"));
  ASSERT_OK_AND_ASSIGN(
      auto injector, PacketInjector::Create(
                         *mock.p4rt_session, pdpi::IrP4Info(), port,
                         {"abcd", "efgh"}, absl::ZeroDuration(), &OkInjector));
}

TEST(PacketInjector, CanDestructWhileResumed) {
  ASSERT_OK_AND_ASSIGN(auto mock, p4_runtime::MakeP4SessionWithMockStub({}));
  ASSERT_OK_AND_ASSIGN(auto port, P4rtPortId::MakeFromP4rtEncoding("12"));
  ASSERT_OK_AND_ASSIGN(
      auto injector, PacketInjector::Create(
                         *mock.p4rt_session, pdpi::IrP4Info(), port,
                         {"abcd", "efgh"}, absl::ZeroDuration(), &OkInjector));
  injector->Pause();
  injector->Resume();
}

TEST(PacketInjector, InjectsPackets) {
  ASSERT_OK_AND_ASSIGN(auto mock, p4_runtime::MakeP4SessionWithMockStub({}));
  ASSERT_OK_AND_ASSIGN(auto port, P4rtPortId::MakeFromP4rtEncoding("12"));
  int call_count = 0;
  ASSERT_OK_AND_ASSIGN(
      auto injector,
      PacketInjector::Create(*mock.p4rt_session, pdpi::IrP4Info(), port,
                             {"abcd", "efgh"}, absl::ZeroDuration(),
                             absl::bind_front(CountingOkInjector, call_count)));
  EXPECT_FALSE(injector->IsPaused());
  absl::Time deadline = absl::Now() + kTimeout;
  while (call_count < 2 && absl::Now() < deadline) {
    absl::SleepFor(absl::Milliseconds(1));
  }

  EXPECT_OK(injector->InjectionError());
  EXPECT_THAT(injector->InjectedPackets(),
              UnorderedElementsAre(Pair("abcd", testing::Gt(0)),
                                   Pair("efgh", testing::Gt(0))));
}

TEST(PacketInjector, InjectsEvenDistributionOfPackets) {
  ASSERT_OK_AND_ASSIGN(auto mock, p4_runtime::MakeP4SessionWithMockStub({}));
  ASSERT_OK_AND_ASSIGN(auto port, P4rtPortId::MakeFromP4rtEncoding("12"));
  int call_count = 0;
  ASSERT_OK_AND_ASSIGN(
      auto injector,
      PacketInjector::Create(*mock.p4rt_session, pdpi::IrP4Info(), port,
                             {"abcd", "efgh"}, absl::ZeroDuration(),
                             absl::bind_front(CountingOkInjector, call_count)));

  absl::Time deadline = absl::Now() + kTimeout;
  while (call_count < 20 && absl::Now() < deadline) {
    absl::SleepFor(absl::Milliseconds(1));
  }
  injector->Pause();

  int packet_diff = injector->InjectedPackets().at("abcd") -
                    injector->InjectedPackets().at("efgh");
  EXPECT_THAT(packet_diff, AllOf(Le(1), Ge(-1)));
  EXPECT_OK(injector->InjectionError());
}

TEST(PacketInjector, StopsEarlyAndReportsError) {
  ASSERT_OK_AND_ASSIGN(auto mock, p4_runtime::MakeP4SessionWithMockStub({}));
  ASSERT_OK_AND_ASSIGN(auto port, P4rtPortId::MakeFromP4rtEncoding("12"));

  int successes = 5;
  auto func = [&successes](const std::string& port, const std::string& packet,
                           const pdpi::IrP4Info& p4info,
                           p4_runtime::P4RuntimeSession* session,
                           std::optional<absl::Duration> duration) {
    if (successes-- > 0) {
      return OkInjector(port, packet, p4info, session, duration);
    }
    return absl::InternalError("Test error");
  };

  ASSERT_OK_AND_ASSIGN(
      auto injector,
      PacketInjector::Create(*mock.p4rt_session, pdpi::IrP4Info(), port,
                             {"abcd", "efgh"}, absl::ZeroDuration(), func));
  absl::Time deadline = absl::Now() + absl::Seconds(1);
  while (!injector->IsPaused() && absl::Now() < deadline) {
    absl::SleepFor(absl::Milliseconds(1));
  }
  EXPECT_THAT(injector->InjectionError(),
              gutil::StatusIs(absl::StatusCode::kInternal));
  EXPECT_THAT(injector->InjectedPackets(),
              UnorderedElementsAre(Pair("abcd", 3), Pair("efgh", 2)));
  EXPECT_TRUE(injector->IsPaused());
  EXPECT_EQ(successes, -1) << "Injection paused but injector is still running.";
}

TEST(PacketInjector, CanPause) {
  ASSERT_OK_AND_ASSIGN(auto mock, p4_runtime::MakeP4SessionWithMockStub({}));
  ASSERT_OK_AND_ASSIGN(auto port, P4rtPortId::MakeFromP4rtEncoding("12"));
  ASSERT_OK_AND_ASSIGN(
      auto injector, PacketInjector::Create(
                         *mock.p4rt_session, pdpi::IrP4Info(), port,
                         {"abcd", "efgh"}, absl::ZeroDuration(), &OkInjector));
  absl::SleepFor(absl::Milliseconds(10));
  injector->Pause();
  EXPECT_TRUE(injector->IsPaused());
  auto early_injection_results = injector->InjectedPackets();
  absl::SleepFor(absl::Milliseconds(10));

  EXPECT_THAT(
      injector->InjectedPackets(),
      UnorderedElementsAre(Pair("abcd", early_injection_results.at("abcd")),
                           Pair("efgh", early_injection_results.at("efgh"))));
}

TEST(PacketInjector, CanResume) {
  ASSERT_OK_AND_ASSIGN(auto mock, p4_runtime::MakeP4SessionWithMockStub({}));
  ASSERT_OK_AND_ASSIGN(auto port, P4rtPortId::MakeFromP4rtEncoding("12"));
  int call_count = 0;
  ASSERT_OK_AND_ASSIGN(
      auto injector,
      PacketInjector::Create(*mock.p4rt_session, pdpi::IrP4Info(), port,
                             {"abcd", "efgh"}, absl::ZeroDuration(),
                             absl::bind_front(CountingOkInjector, call_count)));
  absl::Time deadline = absl::Now() + kTimeout;
  while (call_count < 2 && absl::Now() < deadline) {
    absl::SleepFor(absl::Milliseconds(1));
  }
  injector->Pause();
  auto early_injection_results = injector->InjectedPackets();
  injector->Resume();
  EXPECT_FALSE(injector->IsPaused());

  call_count = 0;
  deadline = absl::Now() + kTimeout;
  while (call_count < 2 && absl::Now() < deadline) {
    absl::SleepFor(absl::Milliseconds(1));
  }

  auto injection_results = injector->InjectedPackets();
  EXPECT_THAT(injection_results,
              UnorderedElementsAre(
                  Pair("abcd", Gt(early_injection_results.at("abcd"))),
                  Pair("efgh", Gt(early_injection_results.at("efgh")))));
}

TEST(PacketInjector, InjectorWithNoPacketsFails) {
  ASSERT_OK_AND_ASSIGN(auto mock, p4_runtime::MakeP4SessionWithMockStub({}));
  ASSERT_OK_AND_ASSIGN(auto port, P4rtPortId::MakeFromP4rtEncoding("12"));
  ASSERT_THAT(PacketInjector::Create(*mock.p4rt_session, pdpi::IrP4Info(), port,
                                     {}, absl::ZeroDuration(), &OkInjector),
              gutil::StatusIs(absl::StatusCode::kInvalidArgument));
}

}  // namespace
}  // namespace pins_test
