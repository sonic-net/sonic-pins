#include "fourward/fourward_oracle.h"

#include <memory>
#include <string>
#include <vector>

#include "gtest/gtest.h"
#include "gutil/io.h"
#include "gutil/status_matchers.h"
#include "p4/v1/p4runtime.pb.h"
#include "simulator.pb.h"
#include "tools/cpp/runfiles/runfiles.h"

namespace dvaas {
namespace {

using ::bazel::tools::cpp::runfiles::Runfiles;

p4::v1::ForwardingPipelineConfig LoadPipelineConfig() {
  std::string error;
  std::unique_ptr<Runfiles> runfiles(Runfiles::CreateForTest(&error));
  EXPECT_NE(runfiles, nullptr) << "Failed to create Runfiles: " << error;

  absl::StatusOr<std::string> contents = gutil::ReadFile(
      runfiles->Rlocation("_main/fourward/sai_middleblock_fourward.binpb"));
  EXPECT_OK(contents);

  p4::v1::ForwardingPipelineConfig config;
  EXPECT_TRUE(config.ParseFromString(*contents));
  return config;
}

TEST(FourwardOracleTest, CreateAndLoadPipeline) {
  p4::v1::ForwardingPipelineConfig config = LoadPipelineConfig();
  ASSERT_FALSE(config.p4info().tables().empty());

  ASSERT_OK_AND_ASSIGN(std::unique_ptr<FourwardOracle> oracle,
                       FourwardOracle::Create(config));
  EXPECT_FALSE(oracle->ServerAddress().empty());
}

TEST(FourwardOracleTest, PredictAllDropsPacketsWithNoEntries) {
  p4::v1::ForwardingPipelineConfig config = LoadPipelineConfig();
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<FourwardOracle> oracle,
                       FourwardOracle::Create(config));

  std::string ethernet_frame(64, '\0');
  ASSERT_OK_AND_ASSIGN(
      std::vector<PacketPrediction> predictions,
      oracle->PredictAll({{.ingress_port = "1", .payload = ethernet_frame}}));

  ASSERT_EQ(predictions.size(), 1);
  EXPECT_TRUE(predictions[0].output_packets.empty());
  EXPECT_GT(predictions[0].trace.events_size(), 0);
}

TEST(FourwardOracleTest, PredictAllBatchProcessing) {
  p4::v1::ForwardingPipelineConfig config = LoadPipelineConfig();
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<FourwardOracle> oracle,
                       FourwardOracle::Create(config));

  std::string ethernet_frame(64, '\0');
  std::vector<PacketInput> packets;
  for (int i = 0; i < 10; ++i) {
    packets.push_back({.ingress_port = "1", .payload = ethernet_frame});
  }

  ASSERT_OK_AND_ASSIGN(std::vector<PacketPrediction> predictions,
                       oracle->PredictAll(packets));
  EXPECT_EQ(predictions.size(), 10);

  for (const PacketPrediction& prediction : predictions) {
    EXPECT_TRUE(prediction.output_packets.empty());
    EXPECT_GT(prediction.trace.events_size(), 0);
  }
}

}  // namespace
}  // namespace dvaas
