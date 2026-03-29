#include "fourward/fourward_oracle.h"

#include <cstdint>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "fourward/fourward_server.h"
#include "grpcpp/channel.h"
#include "grpcpp/client_context.h"
#include "grpcpp/create_channel.h"
#include "grpcpp/security/credentials.h"
#include "gutil/status.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_runtime/p4_runtime_session.h"
#include "p4_infra/p4_runtime/p4_runtime_session_extras.h"
#include "dataplane.grpc.pb.h"
#include "dataplane.pb.h"

namespace dvaas {
namespace {

using fourward::dataplane::Dataplane;
using fourward::dataplane::InjectPacketRequest;
using fourward::dataplane::InjectPacketsResponse;
using fourward::dataplane::ProcessPacketResult;
using fourward::dataplane::SubscribeResultsRequest;
using fourward::dataplane::SubscribeResultsResponse;

PacketPrediction ResultToPrediction(const ProcessPacketResult& result) {
  PacketPrediction prediction;
  for (const fourward::dataplane::PacketSet& outcome :
       result.possible_outcomes()) {
    for (const fourward::dataplane::OutputPacket& packet :
         outcome.packets()) {
      prediction.output_packets.push_back({
          .port = std::string(packet.p4rt_egress_port()),
          .bytes = std::string(packet.payload()),
      });
    }
    // TODO: Return all outcomes for non-deterministic programs.
    break;
  }
  if (result.has_trace()) {
    prediction.trace = result.trace();
  }
  return prediction;
}

}  // namespace

FourwardOracle::FourwardOracle(
    FourwardServer server, std::shared_ptr<grpc::Channel> channel,
    std::unique_ptr<p4_runtime::P4RuntimeSession> session)
    : server_(std::move(server)),
      channel_(std::move(channel)),
      session_(std::move(session)) {}

absl::StatusOr<std::unique_ptr<FourwardOracle>> FourwardOracle::Create(
    const p4::v1::ForwardingPipelineConfig& pipeline_config,
    uint32_t device_id) {
  ASSIGN_OR_RETURN(FourwardServer server, FourwardServer::Start(device_id));

  std::shared_ptr<grpc::Channel> channel = grpc::CreateChannel(
      server.Address(), grpc::InsecureChannelCredentials());
  std::unique_ptr<p4::v1::P4Runtime::StubInterface> stub =
      p4::v1::P4Runtime::NewStub(channel);

  ASSIGN_OR_RETURN(std::unique_ptr<p4_runtime::P4RuntimeSession> session,
                   p4_runtime::P4RuntimeSession::Create(
                       std::move(stub), device_id));

  RETURN_IF_ERROR(p4_runtime::SetMetadataAndSetForwardingPipelineConfig(
      session.get(),
      p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
      pipeline_config));

  return std::unique_ptr<FourwardOracle>(new FourwardOracle(
      std::move(server), std::move(channel), std::move(session)));
}

absl::Status FourwardOracle::InstallIrEntities(
    const pdpi::IrEntities& ir_entities) {
  return p4_runtime::InstallIrEntities(*session_, ir_entities);
}

absl::StatusOr<std::vector<PacketPrediction>> FourwardOracle::PredictAll(
    const std::vector<PacketInput>& packets) {
  if (packets.empty()) return std::vector<PacketPrediction>{};

  std::unique_ptr<Dataplane::StubInterface> stub =
      Dataplane::NewStub(channel_);

  // Subscribe before injecting to avoid missing results.
  grpc::ClientContext results_context;
  std::unique_ptr<grpc::ClientReaderInterface<SubscribeResultsResponse>>
      results_reader = stub->SubscribeResults(
          &results_context, SubscribeResultsRequest());

  SubscribeResultsResponse response;
  if (!results_reader->Read(&response) || !response.has_active()) {
    return absl::InternalError("SubscribeResults did not confirm activation");
  }

  {
    grpc::ClientContext context;
    InjectPacketsResponse response;
    std::unique_ptr<grpc::ClientWriterInterface<InjectPacketRequest>> writer =
        stub->InjectPackets(&context, &response);

    for (const PacketInput& packet : packets) {
      InjectPacketRequest request;
      request.set_p4rt_ingress_port(packet.ingress_port);
      request.set_payload(packet.payload);
      if (!writer->Write(request)) {
        return absl::InternalError("Failed to write to InjectPackets stream");
      }
    }
    writer->WritesDone();

    grpc::Status status = writer->Finish();
    if (!status.ok()) {
      return gutil::GrpcStatusToAbslStatus(status);
    }
  }

  std::vector<PacketPrediction> predictions;
  predictions.reserve(packets.size());
  while (results_reader->Read(&response)) {
    if (!response.has_result()) continue;
    predictions.push_back(ResultToPrediction(response.result()));
    if (predictions.size() == packets.size()) break;
  }
  results_context.TryCancel();

  if (predictions.size() != packets.size()) {
    return absl::InternalError(absl::StrCat(
        "Expected ", packets.size(), " results, got ", predictions.size()));
  }
  return predictions;
}

}  // namespace dvaas
