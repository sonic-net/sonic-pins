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
#include "p4rt_app/tests/lib/p4runtime_request_helpers.h"

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/status.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/pd.h"
#include "p4_infra/p4_runtime/p4_runtime_session.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"

namespace p4rt_app {
namespace test_lib {

absl::StatusOr<p4::v1::WriteRequest> PdWriteRequestToPi(
    absl::string_view pd_request, const pdpi::IrP4Info& ir_p4_info) {
  sai::WriteRequest pd_proto;
  RETURN_IF_ERROR(gutil::ReadProtoFromString(pd_request, &pd_proto))
      << "unable to translate PD proto string";
  return pdpi::PdWriteRequestToPi(ir_p4_info, pd_proto);
}

absl::StatusOr<p4::v1::WriteRequest> IrWriteRequestToPi(
    absl::string_view ir_request, const pdpi::IrP4Info& ir_p4_info) {
  pdpi::IrWriteRequest ir_proto;
  RETURN_IF_ERROR(gutil::ReadProtoFromString(ir_request, &ir_proto))
      << "Unable to translate IrWriteRequest proto string";
  return pdpi::IrWriteRequestToPi(ir_p4_info, ir_proto);
}

}  // namespace test_lib
}  // namespace p4rt_app
