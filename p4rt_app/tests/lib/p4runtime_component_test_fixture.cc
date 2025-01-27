// Copyright 2020 Google LLC
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
#include "p4rt_app/tests/lib/p4runtime_component_test_fixture.h"

#include <vector>

#include "absl/strings/str_cat.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "sai_p4/instantiations/google/instantiations.h"

namespace p4rt_app {
namespace test_lib {

P4RuntimeComponentTestFixture::P4RuntimeComponentTestFixture(
    sai::Instantiation sai_instantiation)
    : p4_info_(sai::GetP4Info(sai_instantiation)),
      ir_p4_info_(sai::GetIrP4Info(sai_instantiation)),
      p4rt_service_(P4RuntimeImplOptions{}) {
  // do nothing.
}

P4RuntimeComponentTestFixture::P4RuntimeComponentTestFixture(
    sai::Instantiation sai_instantiation, const P4RuntimeImplOptions& options)
    : p4_info_(sai::GetP4Info(sai_instantiation)),
      ir_p4_info_(sai::GetIrP4Info(sai_instantiation)),
      p4rt_service_(options) {
  // do nothing.
}

P4RuntimeComponentTestFixture::P4RuntimeComponentTestFixture(
    p4::config::v1::P4Info p4info)
    : p4_info_(std::move(p4info)),
      ir_p4_info_(*pdpi::CreateIrP4Info(p4_info_)),
      p4rt_service_(P4RuntimeImplOptions{}) {
  // do nothing.
}

void P4RuntimeComponentTestFixture::SetUp() {
  // Configure the Device ID on the P4Runtime Server.
  ASSERT_OK(p4rt_service_.GetP4rtServer().UpdateDeviceId(device_id_));

  // Open a P4RT client connection to the gRPC server.
  std::string address = absl::StrCat("localhost:", p4rt_service_.GrpcPort());
  auto stub =
      pdpi::CreateP4RuntimeStub(address, grpc::InsecureChannelCredentials());
  ASSERT_OK_AND_ASSIGN(p4rt_session_, pdpi::P4RuntimeSession::Create(
                                          std::move(stub), device_id_));
  LOG(INFO) << "Opening P4RT connection to " << address << ".";

  // Push a P4Info file to enable the reading, and writing of entries.
  ASSERT_OK(pdpi::SetMetadataAndSetForwardingPipelineConfig(
      p4rt_session_.get(),
      p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
      p4_info_));
}

}  // namespace test_lib
}  // namespace p4rt_app
