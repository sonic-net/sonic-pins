#include "p4rt_app/event_monitoring/app_state_db_send_to_ingress_port_table_event.h"

#include "absl/status/status.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "p4rt_app/p4runtime/mock_p4runtime_impl.h"
#include "p4rt_app/p4runtime/packetio_helpers.h"
#include "swss/schema.h"

namespace p4rt_app {
namespace {

using ::gutil::StatusIs;
using ::testing::Return;

// global variables for swss_common macros.
constexpr char kSetCommand[] = SET_COMMAND;
constexpr char kDelCommand[] = DEL_COMMAND;
constexpr char kSendToIngressPort[] = SEND_TO_INGRESS_PORT_NAME;

TEST(SendToIngressPortTableEventTest, SetEventCreatesPacketIoPort) {
  MockP4RuntimeImpl mock_p4runtime_impl;
  AppStateDbSendToIngressPortTableEventHandler port_change_events(
      &mock_p4runtime_impl);

  EXPECT_CALL(mock_p4runtime_impl, AddPacketIoPort(kSendToIngressPort))
      .WillOnce(Return(absl::OkStatus()));

  EXPECT_OK(
      port_change_events.HandleEvent(kSetCommand, kSendToIngressPort, {}));
}

TEST(SendToIngressPortTableEventTest, DelEventRemovesPacketIoPort) {
  MockP4RuntimeImpl mock_p4runtime_impl;
  AppStateDbSendToIngressPortTableEventHandler port_change_events(
      &mock_p4runtime_impl);

  EXPECT_CALL(mock_p4runtime_impl, RemovePacketIoPort(kSendToIngressPort))
      .WillOnce(Return(absl::OkStatus()));

  EXPECT_OK(
      port_change_events.HandleEvent(kDelCommand, kSendToIngressPort, {}));
}

TEST(SendToIngressPortTableEventTest, UnknownEventTypeFails) {
  MockP4RuntimeImpl mock_p4runtime_impl;
  AppStateDbSendToIngressPortTableEventHandler port_change_events(
      &mock_p4runtime_impl);

  EXPECT_CALL(mock_p4runtime_impl, AddPacketIoPort).Times(0);
  EXPECT_CALL(mock_p4runtime_impl, RemovePacketIoPort).Times(0);

  EXPECT_THAT(port_change_events.HandleEvent(/*operation=*/"UNKNOWN",
                                             kSendToIngressPort, {}),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(SendToIngressPortTableEventTest, UnexpectedPortNameIsANoop) {
  MockP4RuntimeImpl mock_p4runtime_impl;
  AppStateDbSendToIngressPortTableEventHandler port_change_events(
      &mock_p4runtime_impl);

  EXPECT_CALL(mock_p4runtime_impl, AddPacketIoPort).Times(0);
  EXPECT_CALL(mock_p4runtime_impl, RemovePacketIoPort).Times(0);

  EXPECT_OK(port_change_events.HandleEvent(kSetCommand, "Ethernet1/2/1", {}));
  EXPECT_OK(port_change_events.HandleEvent(kDelCommand, "Ethernet1/2/1", {}));
}

}  // namespace
}  // namespace p4rt_app
