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

#ifndef PINS_SAI_P4_INSTANTIATIONS_GOOGLE_TEST_TOOLS_SET_UP_BMV2_H_
#define PINS_SAI_P4_INSTANTIATIONS_GOOGLE_TEST_TOOLS_SET_UP_BMV2_H_

#include "../../fixed/ids.h"
#include "absl/status/statusor.h"
#include "p4/v1/p4runtime.pb.h"
#include "platforms/networking/p4/p4_infra/bmv2/bmv2.h"
#include "sai_p4/instantiations/google/instantiations.h"

namespace sai {

// Returns sensible default arguments for using BMv2 with SAI P4.
inline orion::p4::test::Bmv2Args DefaultSaiP4Bmv2Args() {
  return orion::p4::test::Bmv2Args{
      .device_id = 1,
      .cpu_port = SAI_P4_CPU_PORT,
      .drop_port = SAI_P4_DROP_PORT,
  };
}

// Returns configured BMv2 ready for use with SAI P4.
// Configures BMv2 by pushing the given `config` and installing the auxiliary
// clone session entry required for PacketIO.
absl::StatusOr<orion::p4::test::Bmv2> SetUpBmv2ForSaiP4(
    const p4::v1::ForwardingPipelineConfig& bmv2_config,
    orion::p4::test::Bmv2Args bmv2_args = DefaultSaiP4Bmv2Args());

// Returns configured BMv2 ready for use with SAI P4.
// Configures BMv2 by pushing the pipeline config associated with the given
// `instantiation` and installing the auxiliary clone session entry required for
// PacketIO.
absl::StatusOr<orion::p4::test::Bmv2> SetUpBmv2ForSaiP4(
    Instantiation instantiation,
    orion::p4::test::Bmv2Args bmv2_args = DefaultSaiP4Bmv2Args());

} // namespace sai

#endif // PINS_SAI_P4_INSTANTIATIONS_GOOGLE_TEST_TOOLS_SET_UP_BMV2_H_
