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

#include "fourward/packet_bridge.h"

#include <cstdint>
#include <memory>
#include <string>
#include <utility>

#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/time/time.h"
#include "dataplane.grpc.pb.h"
#include "dataplane.pb.h"
#include "grpcpp/channel.h"
#include "grpcpp/client_context.h"
#include "grpcpp/create_channel.h"
#include "grpcpp/security/credentials.h"

namespace dvaas {

using fourward::dataplane::Dataplane;
using fourward::dataplane::InjectPacketRequest;
using fourward::dataplane::InjectPacketsResponse;
using fourward::dataplane::OutputPacket;
using fourward::dataplane::PacketSet;
using fourward::dataplane::ProcessPacketResult;
using fourward::dataplane::SubscribeResultsRequest;
using fourward::dataplane::SubscribeResultsResponse;

PacketBridge::PacketBridge(std::string sut_address,
                           std::string control_address)
    : sut_address_(std::move(sut_address)),
      control_address_(std::move(control_address)) {}

PacketBridge::~PacketBridge() { Stop(); }

absl::Status PacketBridge::Start() {
  bool expected = false;
  if (!running_.compare_exchange_strong(expected, true)) {
    return absl::FailedPreconditionError("PacketBridge already running");
  }

  // Spawn forwarding threads for both directions.
  sut_to_control_ = std::thread(&PacketBridge::ForwardLoop, this,
                                sut_address_, control_address_,
                                "SUT->Control",
                                std::ref(sut_to_control_ready_));
  control_to_sut_ = std::thread(&PacketBridge::ForwardLoop, this,
                                control_address_, sut_address_,
                                "Control->SUT",
                                std::ref(control_to_sut_ready_));
  // Block until both subscriptions are active.
  constexpr absl::Duration kTimeout = absl::Seconds(10);
  if (!sut_to_control_ready_.WaitForNotificationWithTimeout(kTimeout) ||
      !control_to_sut_ready_.WaitForNotificationWithTimeout(kTimeout)) {
    Stop();
    return absl::DeadlineExceededError(
        "PacketBridge subscriptions did not become active within 10s");
  }

  LOG(INFO) << "PacketBridge started: " << sut_address_ << " <-> "
            << control_address_;
  return absl::OkStatus();
}

void PacketBridge::Stop() {
  if (!running_.load()) return;
  running_.store(false);
  // Cancel active SubscribeResults streams to unblock Read().
  {
    std::lock_guard<std::mutex> lock(contexts_mu_);
    if (sut_subscribe_ctx_) sut_subscribe_ctx_->TryCancel();
    if (control_subscribe_ctx_) control_subscribe_ctx_->TryCancel();
  }
  if (sut_to_control_.joinable()) sut_to_control_.join();
  if (control_to_sut_.joinable()) control_to_sut_.join();
  LOG(INFO) << "PacketBridge stopped. Forwarded: " << packets_forwarded_.load()
            << ", inject failures: " << inject_failures_.load();
}

void PacketBridge::ForwardLoop(const std::string& from_address,
                               const std::string& to_address,
                               const std::string& direction_label,
                               absl::Notification& ready) {
  // Create channels and stubs.
  std::shared_ptr<grpc::Channel> from_channel =
      grpc::CreateChannel(from_address, grpc::InsecureChannelCredentials());
  std::unique_ptr<Dataplane::StubInterface> from_stub =
      Dataplane::NewStub(from_channel);

  std::shared_ptr<grpc::Channel> to_channel =
      grpc::CreateChannel(to_address, grpc::InsecureChannelCredentials());
  std::unique_ptr<Dataplane::StubInterface> to_stub =
      Dataplane::NewStub(to_channel);

  // Subscribe to SubscribeResults on the "from" instance.
  grpc::ClientContext subscribe_ctx;
  {
    std::lock_guard<std::mutex> lock(contexts_mu_);
    if (from_address == sut_address_)
      sut_subscribe_ctx_ = &subscribe_ctx;
    else
      control_subscribe_ctx_ = &subscribe_ctx;
  }
  SubscribeResultsRequest subscribe_request;
  std::unique_ptr<grpc::ClientReaderInterface<SubscribeResultsResponse>>
      reader = from_stub->SubscribeResults(&subscribe_ctx, subscribe_request);

  LOG(INFO) << direction_label << ": subscribed to " << from_address;

  // Open a single streaming InjectPackets writer to the "to" instance,
  // avoiding per-packet unary RPC overhead.
  grpc::ClientContext inject_ctx;
  InjectPacketsResponse inject_response;
  std::unique_ptr<grpc::ClientWriterInterface<InjectPacketRequest>> writer =
      to_stub->InjectPackets(&inject_ctx, &inject_response);

  SubscribeResultsResponse response;
  while (running_.load() && reader->Read(&response)) {
    switch (response.event_case()) {
      case SubscribeResultsResponse::kActive:
        LOG(INFO) << direction_label << ": subscription active";
        ready.Notify();
        continue;
      case SubscribeResultsResponse::kResult:
        break;
      case SubscribeResultsResponse::EVENT_NOT_SET:
        continue;
    }

    const ProcessPacketResult& result = response.result();

    // Forward each output packet from the first possible outcome to the
    // other instance.  Only the first outcome is forwarded because real
    // hardware executes exactly one alternative; forwarding all would
    // duplicate packets for nondeterministic programs.
    for (const PacketSet& outcome : result.possible_outcomes()) {
      for (const OutputPacket& output : outcome.packets()) {
        InjectPacketRequest inject_request;
        // The output's egress port becomes the input's ingress port on the
        // other instance (simulating a back-to-back physical link).
        inject_request.set_dataplane_ingress_port(
            output.dataplane_egress_port());
        inject_request.set_payload(output.payload());

        if (writer->Write(inject_request)) {
          packets_forwarded_.fetch_add(1);
        } else {
          inject_failures_.fetch_add(1);
        }
      }
      // Only forward the first possible outcome.
      break;
    }
  }

  // Shut down the inject stream.
  writer->WritesDone();
  grpc::Status inject_status = writer->Finish();
  if (!inject_status.ok()) {
    LOG(WARNING) << direction_label << ": InjectPackets stream finished with "
                 << inject_status.error_message();
  }

  // Deregister context before finishing.
  {
    std::lock_guard<std::mutex> lock(contexts_mu_);
    if (from_address == sut_address_)
      sut_subscribe_ctx_ = nullptr;
    else
      control_subscribe_ctx_ = nullptr;
  }
  reader->Finish();
  LOG(INFO) << direction_label << ": stopped";
}

}  // namespace dvaas
