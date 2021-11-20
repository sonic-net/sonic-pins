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
#include "p4_pdpi/p4_runtime_session.h"
#include "sai_p4/instantiations/google/instantiations.h"

namespace p4rt_app {
namespace test_lib {

P4RuntimeComponentTestFixture::P4RuntimeComponentTestFixture(
    sai::Instantiation sai_instantiation,
    std::vector<FakeGnmiPortConfig> gnmi_ports)
    : p4_info_(sai::GetP4Info(sai_instantiation)),
      ir_p4_info_(sai::GetIrP4Info(sai_instantiation)),
      gnmi_ports_(gnmi_ports) {
  // do nothing.
}

void P4RuntimeComponentTestFixture::SetUp() {
  // Fake any gNMI configurations first.
  // Configure any ethernet ports for the tests.
  for (const auto& port : gnmi_ports_) {
    p4rt_service_.GetPortAppDbTable().InsertTableEntry(port.port_name,
                                                       {{"id", port.port_id}});
  }

  // Open a P4RT client connection to the gRPC server.
  std::string address = absl::StrCat("localhost:", p4rt_service_.GrpcPort());
  auto stub =
      pdpi::CreateP4RuntimeStub(address, grpc::InsecureChannelCredentials());
  ASSERT_OK_AND_ASSIGN(p4rt_session_, pdpi::P4RuntimeSession::Create(
                                          std::move(stub), device_id_));
  LOG(INFO) << "Opening P4RT connection to " << address << ".";

  // Push a P4Info file to enable the reading, and writing of entries.
  ASSERT_OK(pdpi::SetForwardingPipelineConfig(
      p4rt_session_.get(),
      p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
      p4_info_));
}

}  // namespace test_lib
}  // namespace p4rt_app
