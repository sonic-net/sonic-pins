// Copyright (c) 2024, Google Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "lib/basic_traffic/basic_p4rt_util.h"

#include <functional>
#include <string>
#include <type_traits>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/substitute.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/status.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_infra/p4_pdpi/pd.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"

namespace pins_test::basic_traffic {
namespace {

absl::Status WritePdWriteRequest(
    const std::function<absl::Status(p4::v1::WriteRequest&)>& write_request,
    const pdpi::IrP4Info& ir_p4info,
    const sai::WriteRequest& pd_write_request) {
  ASSIGN_OR_RETURN(p4::v1::WriteRequest pi_write_request,
                   pdpi::PdWriteRequestToPi(ir_p4info, pd_write_request));
  return write_request(pi_write_request);
}

}  // namespace

absl::Status ProgramTrafficVrf(
    const std::function<absl::Status(p4::v1::WriteRequest&)>& write_request,
    const pdpi::IrP4Info& ir_p4info) {
  ASSIGN_OR_RETURN(auto vrf_request,
                   gutil::ParseTextProto<sai::WriteRequest>(
                       R"pb(updates {
                              type: INSERT
                              table_entry {
                                vrf_table_entry {
                                  match { vrf_id: "traffic-vrf" }
                                  action { no_action {} }
                                }
                              }
                            })pb"));
  RETURN_IF_ERROR(WritePdWriteRequest(write_request, ir_p4info, vrf_request))
      << "Error writing VRF request.";

  ASSIGN_OR_RETURN(auto pre_ingress_request,
                   gutil::ParseTextProto<sai::WriteRequest>(R"pb(
                     updates {
                       type: INSERT
                       table_entry {
                         acl_pre_ingress_table_entry {
                           action { set_vrf { vrf_id: "traffic-vrf" } }
                           priority: 1132
                         }
                       }
                     }
                   )pb"));
  RETURN_IF_ERROR(
      WritePdWriteRequest(write_request, ir_p4info, pre_ingress_request))
      << "Error writing pre-ingress request.";
  return absl::OkStatus();
}

absl::Status ProgramRouterInterface(
    const std::function<absl::Status(p4::v1::WriteRequest&)>& write_request,
    int port_id, const pdpi::IrP4Info& ir_p4info) {
  ASSIGN_OR_RETURN(
      auto request,
      gutil::ParseTextProto<sai::WriteRequest>(absl::Substitute(
          R"pb(
            updates {
              type: INSERT
              table_entry {
                router_interface_table_entry {
                  match { router_interface_id: "traffic-router-interface-$0" }
                  action { set_port_and_src_mac { port: "$0" src_mac: "$1" } }
                }
              }
            }
          )pb",
          port_id, PortIdToMac(port_id))));
  RETURN_IF_ERROR(WritePdWriteRequest(write_request, ir_p4info, request))
      << "Error writing router interface request.";
  return absl::OkStatus();
}

absl::Status ProgramIPv4Route(
    const std::function<absl::Status(p4::v1::WriteRequest&)>& write_request,
    int port_id, const pdpi::IrP4Info& ir_p4info) {
  ASSIGN_OR_RETURN(
      auto neighbor_request,
      gutil::ParseTextProto<sai::WriteRequest>(absl::Substitute(
          R"pb(
            updates {
              type: INSERT
              table_entry {
                neighbor_table_entry {
                  match {
                    router_interface_id: "traffic-router-interface-$0"
                    neighbor_id: "fe80::21a:11ff:fe17:0080"
                  }
                  action { set_dst_mac { dst_mac: "00:1A:11:17:00:80" } }
                }
              }
            }
          )pb",
          port_id)));
  RETURN_IF_ERROR(
      WritePdWriteRequest(write_request, ir_p4info, neighbor_request))
      << "Error writing neighbor entry request.";

  ASSIGN_OR_RETURN(
      auto nexthop_request,
      gutil::ParseTextProto<sai::WriteRequest>(absl::Substitute(
          R"pb(
            updates {
              type: INSERT
              table_entry {
                nexthop_table_entry {
                  match { nexthop_id: "traffic-nexthop-$0" }
                  action {
                    set_ip_nexthop {
                      router_interface_id: "traffic-router-interface-$0"
                      neighbor_id: "fe80::21a:11ff:fe17:0080"
                    }
                  }
                }
              }
            }
          )pb",
          port_id)));
  RETURN_IF_ERROR(
      WritePdWriteRequest(write_request, ir_p4info, nexthop_request))
      << "Error writing nexthop entry request.";

  ASSIGN_OR_RETURN(
      auto ipv4_request,
      gutil::ParseTextProto<sai::WriteRequest>(absl::Substitute(
          R"pb(
            updates {
              type: INSERT
              table_entry {
                ipv4_table_entry {
                  match {
                    vrf_id: "traffic-vrf"
                    ipv4_dst { value: "$1" prefix_length: 32 }
                  }
                  action { set_nexthop_id { nexthop_id: "traffic-nexthop-$0" } }
                }
              }
            }
          )pb",
          port_id, PortIdToIP(port_id))));
  RETURN_IF_ERROR(WritePdWriteRequest(write_request, ir_p4info, ipv4_request))
      << "Error writing IPv4 entry request.";
  return absl::OkStatus();
}

absl::Status ProgramL3AdmitTableEntry(
    const std::function<absl::Status(p4::v1::WriteRequest&)>& write_request,
    const pdpi::IrP4Info& ir_p4info) {
  sai::TableEntry l3_admit_table_entry;
  ASSIGN_OR_RETURN(
      auto l3_admit_request,
      gutil::ParseTextProto<sai::WriteRequest>(
          R"pb(
            updates {
              type: INSERT
              table_entry {
                l3_admit_table_entry {
                  match {
                    dst_mac {
                      value: "00:00:00:00:00:00"
                      mask: "01:00:00:00:00:00"
                    }
                  }
                  action { admit_to_l3 {} }
                  priority: 1
                  controller_metadata: "Experimental_type: VARIOUS_L3ADMIT_PUNTFLOW"
                }
              }
            }
          )pb"));

  RETURN_IF_ERROR(
      WritePdWriteRequest(write_request, ir_p4info, l3_admit_request))
      << "Error writing l3 admit table entry request.";
  return absl::OkStatus();
}

}  // namespace pins_test::basic_traffic
