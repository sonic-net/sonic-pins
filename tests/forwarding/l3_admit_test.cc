// Copyright 2024 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
#include "tests/forwarding/l3_admit_test.h"

#include <memory>
#include <optional>
#include <utility>

#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "gutil/proto.h"
#include "gutil/status_matchers.h"
#include "lib/gnmi/gnmi_helper.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/packetlib/packetlib.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "tests/forwarding/util.h"
#include "tests/lib/p4rt_fixed_table_programming_helper.h"
#include "tests/lib/packet_in_helper.h"
#include "thinkit/mirror_testbed_fixture.h"

namespace pins {
namespace {

absl::Status AddAndSetDefaultVrf(pdpi::P4RuntimeSession& session,
                                 const pdpi::IrP4Info& ir_p4info,
                                 const std::string& vrf_id) {
  pdpi::IrWriteRequest ir_write_request;
  RETURN_IF_ERROR(gutil::ReadProtoFromString(
      absl::Substitute(R"pb(
                         updates {
                           type: INSERT
                           table_entry {
                             table_name: "vrf_table"
                             matches {
                               name: "vrf_id"
                               exact { str: "$0" }
                             }
                             action { name: "no_action" }
                           }
                         }
                         updates {
                           type: INSERT
                           table_entry {
                             table_name: "acl_pre_ingress_table"
                             priority: 2000
                             action {
                               name: "set_vrf"
                               params {
                                 name: "vrf_id"
                                 value { str: "$0" }
                               }
                             }
                           }
                         }
                       )pb",
                       vrf_id),
      &ir_write_request));
  ASSIGN_OR_RETURN(p4::v1::WriteRequest pi_write_request,
                   pdpi::IrWriteRequestToPi(ir_p4info, ir_write_request));
  return pdpi::SetMetadataAndSendPiWriteRequest(&session, pi_write_request);
}
}  // namespace

TEST_P(L3AdmitTestFixture, L3PacketsAreRoutedWhenMacAddressIsInMyStation) {
  LOG(INFO) << "Starting test.";

  // PacketIO handlers for both the SUT and control switch.
  std::unique_ptr<PacketInHelper> packetio_sut =
      std::make_unique<PacketInHelper>(p4rt_sut_switch_session_.get(),
                                       PacketInHelper::NoFilter);
  std::unique_ptr<PacketInHelper> packetio_control =
      std::make_unique<PacketInHelper>(p4rt_control_switch_session_.get(),
                                       PacketInHelper::NoFilter);
}

}  // namespace pins
