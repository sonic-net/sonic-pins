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

#ifndef PINS_TESTS_CPU_QOS_TEST_H_
#define PINS_TESTS_CPU_QOS_TEST_H_
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/generic_testbed_fixture.h"

namespace pins_test {

struct QosTestArguments {
  // Description of the test instantation given by this set of arguments.
  std::string description;
  thinkit::GenericTestbedInterface* testbed_interface;
  std::vector<sai::TableEntry> table_entries;
  std::string gnmi_config;
  p4::config::v1::P4Info p4info;
  absl::optional<std::string> test_case_id;
};

class CpuQosIxiaTestFixture : public testing::TestWithParam<QosTestArguments> {
 protected:
  void SetUp() override { GetParam().testbed_interface->SetUp(); }

  void TearDown() override { GetParam().testbed_interface->TearDown(); }

  ~CpuQosIxiaTestFixture() override { delete GetParam().testbed_interface; }
};
}  // namespace pins_test
#endif  // PINS_TESTS_CPU_QOS_TEST_H_
