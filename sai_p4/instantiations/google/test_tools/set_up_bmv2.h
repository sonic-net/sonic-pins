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
#include "p4_pdpi/p4_runtime_session_extras.pb.h"
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

enum class InitialBmv2ControlPlane {
  kInstallCloneEntries,
  kNoControlPlane,
};

template <typename Sink>
void AbslStringify(Sink &sink, InitialBmv2ControlPlane e) {
  switch (e) {
    case InitialBmv2ControlPlane::kInstallCloneEntries:
      sink.Append("kInstallCloneEntries");
      break;
    case InitialBmv2ControlPlane::kNoControlPlane:
      sink.Append("kNoControlPlane");
      break;
  }
}

// Options for setting up BMv2 to run with SAI P4.
// These options are not arguments that are forwarded to the BMv2 binary.
// Instead they are used to control the installation of control plane entities
// on BMv2 after it has been instantiated. For example, whether clone entries
// should be installed or not.
struct SaiP4Bmv2SetupOptions {
  // The BMv2 SAI setup installs a clone configuration, which can be disabled.
  InitialBmv2ControlPlane initial_bmv2_control_plane =
      InitialBmv2ControlPlane::kInstallCloneEntries;
};

// Returns CloneSession (CS) entries and IngressClone (IC) entries that
// aggregate punting and mirroring's effect needed by V1Model targets such as
// BMv2:
// 1. one CS entry with 1 p4::v1::Replica for punting only.
// 2. one IC entry that lets marked_to_punt packets to get cloned using the CS
// created in step 1.
// 3. One CS entry for each port with one p4::v1::Replica that mirrors to that
// port.
// 4. One IC entry for each port. Each IC entry lets marked_to_mirror packets
// to get cloned with the CS entry for that port created in step 3.
// 5. One CS entry for each port with 2 p4::v1::Replicas. In each CS entry, One
// replica mirrors to that particular port and the other replica punts.
// 6. One IC entry for each port. Each IC entry lets marked_to_mirror and
// marked_to_punt packets to get cloned and punt with the CS entry for that port
// created in step 5.
//
// BMv2's port number ranges from 1 to 511 (V1Model uses 9 bits for port and
// BMv2 prohibits port to be 0).
absl::StatusOr<pdpi::PiEntities> GetEntitiesForClone(
    const pdpi::IrP4Info &bmv2_ir_p4info);

// Returns configured BMv2 ready for use with SAI P4.
// Configures BMv2 by pushing the given `config` and installing the auxiliary
// clone session entry required for PacketIO.
absl::StatusOr<orion::p4::test::Bmv2> SetUpBmv2ForSaiP4(
    const p4::v1::ForwardingPipelineConfig &bmv2_config,
    const SaiP4Bmv2SetupOptions &options = {},
    orion::p4::test::Bmv2Args bmv2_args = DefaultSaiP4Bmv2Args());

// Returns configured BMv2 ready for use with SAI P4.
// Configures BMv2 by pushing the pipeline config associated with the given
// `instantiation` and installing the auxiliary clone session entry required for
// PacketIO.
absl::StatusOr<orion::p4::test::Bmv2> SetUpBmv2ForSaiP4(
    Instantiation instantiation, const SaiP4Bmv2SetupOptions &options = {},
    orion::p4::test::Bmv2Args bmv2_args = DefaultSaiP4Bmv2Args());

} // namespace sai

#endif // PINS_SAI_P4_INSTANTIATIONS_GOOGLE_TEST_TOOLS_SET_UP_BMV2_H_
