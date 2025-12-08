// Copyright 2022 Google LLC
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
#include <grpcpp/support/status.h>

#include <memory>
#include <utility>

#include "absl/log/log.h"
#include "gmock/gmock.h"
#include "grpcpp/client_context.h"
#include "grpcpp/security/credentials.h"
#include "grpcpp/security/server_credentials.h"
#include "grpcpp/server_builder.h"
#include "grpcpp/support/channel_arguments.h"
#include "gtest/gtest.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4rt_app/p4runtime/p4runtime_impl.h"
#include "p4rt_app/sonic/adapters/fake_warm_boot_state_adapter.h"
#include "p4rt_app/sonic/fake_packetio_interface.h"
#include "p4rt_app/sonic/redis_connections.h"
//TODO(PINS): Add fake Component/System state Translator
//#include "swss/fakes/fake_component_state_helper.h"
//#include "swss/fakes/fake_system_state_helper.h"

namespace p4rt_app {
namespace {

constexpr char kServerAddr[] = "localhost:9999";

// This test suite doesn't deal with the P4Runtime service so we do not need to
// properly configure the fake DB connections.
P4RuntimeImpl DummyP4RuntimeImpl() {
  // Dummy RedisDB tables.
  sonic::P4rtTable dummy_p4rt_table;
  sonic::VrfTable dummy_vrf_table;
  sonic::VlanTable dummy_vlan_table;
  sonic::VlanMemberTable dummy_vlan_member_table;
  sonic::HashTable dummy_hash_table;
  sonic::SwitchTable dummy_switch_table;
  sonic::PortTable dummy_port_table;
  sonic::HostStatsTable dummy_host_stats_table;
  sonic::SwitchCapabilityTable dummy_switch_capability_table;

  // Dummy PacketIO.
  auto packet_io = std::make_unique<sonic::FakePacketIoInterface>();

//TODO(PINS): To add fake component_state_helper, system_state_helper and netdev_translator.
  // Dummy state management.
  // swss::FakeComponentStateHelper component_state_helper;
  // swss::FakeSystemStateHelper system_state_helper;

  // Dummy netdev name translation.
  // sonic::FakeIntfTranslator netdev_translator(/*enabled=*/false);

  return P4RuntimeImpl(
      std::move(dummy_p4rt_table), std::move(dummy_vrf_table),
      std::move(dummy_vlan_table), std::move(dummy_vlan_member_table),
      std::move(dummy_hash_table), std::move(dummy_switch_table),
      std::move(dummy_port_table), std::move(dummy_host_stats_table),
      std::move(dummy_switch_capability_table),
      std::make_unique<p4rt_app::sonic::FakeWarmBootStateAdapter>(),
      std::move(packet_io),
      // TODO(PINS): To add component_state_helper, system_state_helper and
      // netdev_translator. component_state_helper, system_state_helper,
      // netdev_translator,
      P4RuntimeImplOptions{});
}

TEST(GrpcBehaviorTest,
     SendingKeepAliveWithoutDataWillCloseServerWithDefaultConfig) {
  P4RuntimeImpl dummy_service = DummyP4RuntimeImpl();

  // Configure the gRPC service using default values.
  grpc::ServerBuilder builder;
  builder.AddListeningPort(kServerAddr, grpc::InsecureServerCredentials());
  builder.RegisterService(&dummy_service);

  // If we wanted to ignore all ping strikes due to excessive KEEPALIVE pings we
  // could disable the count on the server side. For example:
  //   builder.AddChannelArgument(GRPC_ARG_HTTP2_MAX_PING_STRIKES, 0);
  // In this case we would expect this test to run until timeout.
  std::unique_ptr<grpc::Server> server(builder.BuildAndStart());

  // https://github.com/grpc/grpc/blob/master/doc/keepalive.md
  //
  // We configure the client such that the KEEPALIVE pings are sent every 500
  // ms, and can be sent even if there is not data being sent over the channel.
  grpc::ChannelArguments channel_args;
  channel_args.SetInt(GRPC_ARG_KEEPALIVE_TIME_MS, 500);
  channel_args.SetInt(GRPC_ARG_HTTP2_MAX_PINGS_WITHOUT_DATA, 0);

  // Open a stream channel to the gRPC service.
  auto channel = grpc::CreateCustomChannel(
      kServerAddr, grpc::InsecureChannelCredentials(), channel_args);
  auto p4rt_stub = p4::v1::P4Runtime::NewStub(channel);
  grpc::ClientContext client_context;
  auto client_stream = p4rt_stub->StreamChannel(&client_context);

  // By default the gRPC will allow 2 pings without data before it sends a HTTP2
  // GOAWAY frame and closes the connection. Since we send this ping every 500ms
  // we expect the test to take a few seconds (i.e. 2 * 500ms) before the stream
  // gets closed.
  p4::v1::StreamMessageResponse dummy_response;
  while (client_stream->Read(&dummy_response)) {
    // We do not expect a response since no request was sent, but we log
    // anything just in case.
    LOG(WARNING) << dummy_response.DebugString();
  }

  grpc::Status status = client_stream->Finish();
  LOG(INFO) << "Client status: " << status.error_message();
  EXPECT_EQ(status.error_code(), grpc::StatusCode::UNAVAILABLE);
}

}  // namespace
}  // namespace p4rt_app
