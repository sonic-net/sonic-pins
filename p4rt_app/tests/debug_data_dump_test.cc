// Copyright 2024 Google LLC
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
#include <string>

#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "gmock/gmock.h"
#include "grpcpp/support/status.h"
#include "gtest/gtest.h"
#include "gutil/io.h"
#include "p4rt_app/p4runtime/p4runtime_impl.h"
#include "p4rt_app/tests/lib/p4runtime_component_test_fixture.h"
#include "p4rt_app/tests/lib/p4runtime_grpc_service.h"
#include "sai_p4/instantiations/google/instantiations.h"

namespace p4rt_app {
namespace {

class DebugDataDumpTest : public test_lib::P4RuntimeComponentTestFixture {
 protected:
  DebugDataDumpTest()
      : test_lib::P4RuntimeComponentTestFixture(
            sai::Instantiation::kMiddleblock) {}
};

TEST_F(DebugDataDumpTest, VerifyDebugDumpPacketIoCountersToCorrectFile) {
  std::string temp_dir = testing::TempDir();

  EXPECT_OK(p4rt_service_.GetP4rtServer().DumpDebugData(temp_dir, "alert"));

  // Check if the file exists.
  ASSERT_OK_AND_ASSIGN(std::string packetio_debugs,
                       gutil::ReadFile(temp_dir + "/packet_io_counters"));
  ASSERT_FALSE(packetio_debugs.empty());
}

}  // namespace
}  // namespace p4rt_app
