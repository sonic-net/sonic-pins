#include "fourward/fourward_oracle.h"

#include <fstream>
#include <memory>
#include <sstream>
#include <string>
#include <vector>

#include "gtest/gtest.h"
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
  std::string path = runfiles->Rlocation(
      "_main/fourward/sai_middleblock_fourward.binpb");

  std::ifstream file(path, std::ios::binary);
  EXPECT_TRUE(file.good()) << "Failed to open: " << path;
  std::ostringstream buffer;
  buffer << file.rdbuf();

  p4::v1::ForwardingPipelineConfig config;
  EXPECT_TRUE(config.ParseFromString(buffer.str()))
      << "Failed to parse binary proto from: " << path;
  return config;
}

TEST(FourwardOracleTest, CreateAndLoadPipeline) {
  p4::v1::ForwardingPipelineConfig config = LoadPipelineConfig();
  ASSERT_FALSE(config.p4info().tables().empty())
      << "Pipeline config has no tables";

  ASSERT_OK_AND_ASSIGN(std::unique_ptr<FourwardOracle> oracle,
                       FourwardOracle::Create(config));
  EXPECT_FALSE(oracle->ServerAddress().empty());
}

TEST(FourwardOracleTest, PredictDropsPacketWithNoEntries) {
  p4::v1::ForwardingPipelineConfig config = LoadPipelineConfig();
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<FourwardOracle> oracle,
                       FourwardOracle::Create(config));

  std::string ethernet_frame(64, '\0');
  ASSERT_OK_AND_ASSIGN(
      PacketPrediction prediction,
      oracle->Predict({.ingress_port = "1", .payload = ethernet_frame}));

  EXPECT_TRUE(prediction.output_packets.empty())
      << "Expected drop, got " << prediction.output_packets.size()
      << " output packets";

  EXPECT_GT(prediction.trace.events_size(), 0);
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
    EXPECT_TRUE(prediction.output_packets.empty())
        << "Expected drop with no entries";
    EXPECT_GT(prediction.trace.events_size(), 0);
  }
}

}  // namespace
}  // namespace dvaas
