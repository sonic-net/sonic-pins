// Copyright 2021 Google LLC
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
#ifndef PINS_P4RT_APP_TESTS_LIB_P4RUNTIME_COMPONENT_TEST_FIXTURE_H_
#define PINS_P4RT_APP_TESTS_LIB_P4RUNTIME_COMPONENT_TEST_FIXTURE_H_

#include "absl/strings/str_cat.h"
#include "grpcpp/security/credentials.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status_matchers.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "p4rt_app/p4runtime/p4runtime_impl.h"
#include "p4rt_app/tests/lib/p4runtime_grpc_service.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"

namespace p4rt_app {
namespace test_lib {

// A P4Runtime component test fixture that will bring up a fake P4RT Application
// service, and P4RT client session. This fixture can also be used to fake any
// gNMI configurations.
class P4RuntimeComponentTestFixture : public testing::Test {
protected:
  P4RuntimeComponentTestFixture(sai::Instantiation sai_instantiation);
  P4RuntimeComponentTestFixture(p4::config::v1::P4Info p4info);
  P4RuntimeComponentTestFixture(sai::Instantiation sai_instantiation,
                                const P4RuntimeImplOptions &options);
  void SetUp() override;

  // Component test configurations that should never change for the lifetime of
  // a test.
  const uint32_t device_id_ = 183807201;
  const p4::config::v1::P4Info p4_info_;
  const pdpi::IrP4Info ir_p4_info_;

  // A testable P4Runtime gRPC server with fake DB connections
  P4RuntimeGrpcService p4rt_service_;

  // The P4RT gRPC client session tests will use to connect to the fake
  // P4Runtime server.
  std::unique_ptr<pdpi::P4RuntimeSession> p4rt_session_;
};

} // namespace test_lib
} // namespace p4rt_app

#endif // PINS_P4RT_APP_TESTS_LIB_P4RUNTIME_COMPONENT_TEST_FIXTURE_H_
