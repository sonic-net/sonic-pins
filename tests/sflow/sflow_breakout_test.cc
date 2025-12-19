#include "tests/sflow/sflow_breakout_test.h"

#include <string>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/time/time.h"
#include "grpcpp/client_context.h"
#include "gtest/gtest.h"
#include "gutil/status.h"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/validator/validator_lib.h"
#include "p4/config/v1/p4info.pb.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "proto/gnmi/gnmi.pb.h"
#include "tests/sflow/sflow_util.h"
#include "tests/thinkit_gnmi_interface_util.h"
#include "tests/thinkit_util.h"
#include "thinkit/switch.h"

namespace pins_test {
namespace {
constexpr absl::string_view kSflowGnmiStateInterfacePath =
    "/sampling/sflow/interfaces/interface[name=$0]/state/";

// Verify that the config is successfully applied now.
// When `option.mirror_broken_out` is true, sets all ports expected oper
// status to be UP since the othe side of mirror testbed has performed the same
// breakout mode.
// When `option.mirror_broken_out` is false, modifies the oper status of the
// ports in new_breakout_info according to the expected oper status. Expect
// logical ports that did not change on breakout to be UP. e.g.,
// Ethernet1/1/1(UP), Ethernet1/1/5(UP)  ->
// Ethernet1/1/1(UP), Ethernet1/1/5(DOWN), Ethernet1/1/7(DOWN)
// Or
// Ethernet1/1/1(UP), Ethernet1/1/5(DOWN) ->
// Ethernet1/1/1(DOWN), Ethernet1/1/3(DOWN), Ethernet1/1/5(DOWN),
// Ethernet1/1/7(DOWN)
absl::Status VerifyAppliedBreakoutAndSflowConverged(
    gnmi::gNMI::StubInterface* sut_gnmi_stub,
    const absl::flat_hash_map<std::string, pins_test::PortBreakoutInfo>&
        orig_breakout_info,
    absl::flat_hash_map<std::string, pins_test::PortBreakoutInfo>&
        new_breakout_info,
    const SflowBreakoutTestOption& option) {
  for (auto& [breakout_port_name, breakout_port_info] : new_breakout_info) {
    if (option.mirror_broken_out) {
      breakout_port_info.oper_status = kStateUp;
      continue;
    }
    breakout_port_info.oper_status = kStateDown;
    // For the logical ports that do not change on breakout, expect them to be
    // operationally up.
    auto it = orig_breakout_info.find(breakout_port_name);
    if (it != orig_breakout_info.end()) {
      if (it->second.physical_channels ==
              breakout_port_info.physical_channels &&
          it->second.breakout_speed == breakout_port_info.breakout_speed) {
        breakout_port_info.oper_status = kStateUp;
      }
    }
  }
  // e.g., Ethernet1/1/1, Ethernet1/1/5 (2x200) -> Ethernet1/1/1 (400)
  // Ethernet1/1/5 is non-existing port.
  RETURN_IF_ERROR(ValidateBreakoutState(
      sut_gnmi_stub, new_breakout_info,
      GetNonExistingPortsAfterBreakout(orig_breakout_info, new_breakout_info,
                                       /*expected_success=*/true)));

  // Expect sFlow interfaces to be converged.
  for (const auto& [port_name, unused] : new_breakout_info) {
    const std::string state_enable_path = absl::Substitute(
        "/sampling/sflow/interfaces/interface[name=$0]/state/enabled",
        port_name);
    const std::string state_sampling_rate_path = absl::Substitute(
        "/sampling/sflow/interfaces/interface[name=$0]/state/"
        "ingress-sampling-rate",
        port_name);
    RETURN_IF_ERROR(pins::VerifyGnmiStateConverged(
        sut_gnmi_stub, state_enable_path,
        /*expected_value=*/
        R"({"openconfig-sampling-sflow:enabled":true})"));
    RETURN_IF_ERROR(pins::VerifyGnmiStateConverged(
        sut_gnmi_stub, state_sampling_rate_path,
        /*expected_value=*/
        absl::Substitute(
            R"({"openconfig-sampling-sflow:ingress-sampling-rate":$0})",
            option.sampling_rate)));
  }

  // Expect sFlow objects to be deleted for non-existing ports.
  for (const auto& port_name : GetNonExistingPortsAfterBreakout(
           orig_breakout_info, new_breakout_info, true)) {
    auto resp_parse_str = "openconfig-sampling-sflow:state";
    if (GetGnmiStatePathInfo(
            sut_gnmi_stub,
            absl::Substitute(kSflowGnmiStateInterfacePath, port_name),
            resp_parse_str)
            .ok()) {
      return gutil::InternalErrorBuilder().LogError()
             << "Unexpected sFlow port (" << port_name
             << ") found after application of breakout mode";
    }
  }
  return absl::OkStatus();
}

absl::Status ApplySflowBreakoutConfig(
    thinkit::Switch& sut, gnmi::gNMI::StubInterface* sut_gnmi_stub,
    const std::string& breakout_config_with_sflow) {
  // TODO: Use a full config push after library is available.
  ASSIGN_OR_RETURN(gnmi::SetRequest req,
                   BuildGnmiSetRequest("", GnmiSetType::kReplace,
                                       breakout_config_with_sflow));
  gnmi::SetResponse resp;
  grpc::ClientContext context;
  return gutil::GrpcStatusToAbslStatus(
      sut_gnmi_stub->Set(&context, req, &resp));
}

}  // namespace

std::string SflowBreakoutTestOption::DebugString() const {
  return absl::Substitute(
      "[sampling_rate: $0, sampling_header_size:$1, agent_address: "
      "$2, collector_ip:$3, collector_port:$4, breakout_port_info: $5, "
      "mirror_broken_out: $6]",
      sampling_rate, sampling_header_size, agent_addr_ipv6, collector_ip,
      collector_port, (port_info.has_value() ? port_info->port_name : "none"),
      mirror_broken_out);
}

absl::StatusOr<SflowBreakoutResult> TestBreakoutWithSflowConfig(
    thinkit::Switch& sut, const std::string& platform_json_contents,
    const p4::config::v1::P4Info& p4_info,
    const SflowBreakoutTestOption& option) {
  SCOPED_TRACE(absl::StrCat("Test port breakout on ", sut.ChassisName(),
                            " with sflow option: ", option.DebugString()));
  LOG(INFO) << "========== " << __func__ << " Test port breakout on "
            << sut.ChassisName()
            << " with sflow option: " << option.DebugString() << " ==========";
  ASSIGN_OR_RETURN(auto sut_gnmi_stub, sut.CreateGnmiStub());

  RandomPortBreakoutInfo selected_port_info;
  if (option.port_info.has_value()) {
    // Use selected port for testing, applicable when doing breakout on the
    // mirrored switch after the first switch has already selected the breakout
    // port.
    selected_port_info = *option.port_info;
  } else {
    ASSIGN_OR_RETURN(auto port_id_per_port_name,
                     GetAllUpInterfacePortIdsByName(*sut_gnmi_stub));
    std::vector<absl::string_view> up_copper_ports;
    for (const auto& [interface, unused] : port_id_per_port_name) {
      // Run breakout tests only on copper ports to avoid breakout compatibility
      // complexity for non-copper ports.
      if (auto is_copper = IsCopperPort(sut_gnmi_stub.get(), interface);
          is_copper.ok() && *is_copper) {
        up_copper_ports.push_back(interface);
      }
    }
    RET_CHECK(!up_copper_ports.empty()) << "No UP copper ports found.";
    // Get a random port from list of front panel UP ports that supports at
    // least one breakout mode of required type other than its current mode.
    ASSIGN_OR_RETURN(
        selected_port_info,
        GetRandomPortWithSupportedBreakoutModes(
            *sut_gnmi_stub, platform_json_contents, BreakoutType::kAny,
            BreakoutType::kAny, up_copper_ports));
  }
  LOG(INFO) << "Using port " << selected_port_info.port_name
            << " with current breakout mode "
            << selected_port_info.curr_breakout_mode;

  // Get the original breakout info on the port.
  // This contains the state values of physical channels and
  // operational status information for ports in original breakout mode.
  ASSIGN_OR_RETURN(auto orig_breakout_info,
                   GetBreakoutStateInfoForPort(
                       sut_gnmi_stub.get(), selected_port_info.port_name,
                       selected_port_info.curr_breakout_mode));

  for (const auto& [port_name, unused] : orig_breakout_info) {
    // Set sFlow interface config to enabled before breakout.
    RETURN_IF_ERROR(
        pins::SetSflowInterfaceConfig(sut_gnmi_stub.get(), port_name,
                                       /*enabled=*/true, option.sampling_rate))
        << "Failed to SetSflowInterfaceConfig on " << port_name;
  }

  // Get breakout config for the new breakout mode.
  ASSIGN_OR_RETURN(auto port_index, GetPortIndex(platform_json_contents,
                                                 selected_port_info.port_name));
  // Generate breakout and sflow config.
  ASSIGN_OR_RETURN(
      const std::string breakout_config,
      GetBreakoutModeConfigJson(sut_gnmi_stub.get(), port_index,
                                selected_port_info.port_name,
                                selected_port_info.supported_breakout_mode));
  // Get expected port information for new breakout mode and set sflow sample
  // interfaces.
  ASSIGN_OR_RETURN(auto new_breakout_info,
                   GetExpectedPortInfoForBreakoutMode(
                       selected_port_info.port_name,
                       selected_port_info.supported_breakout_mode));
  absl::flat_hash_map<std::string, bool> sflow_interfaces;
  for (const auto& [port_name, unused] : new_breakout_info) {
    sflow_interfaces[port_name] = true;
  }
  ASSIGN_OR_RETURN(
      const std::string breakout_config_with_sflow,
      pins::UpdateSflowConfig(breakout_config, option.agent_addr_ipv6,
                               {{option.collector_ip, option.collector_port}},
                               sflow_interfaces, option.sampling_rate,
                               option.sampling_header_size));
  LOG(INFO) << "Generated config:\n" << breakout_config_with_sflow;

  // Apply breakout config on SUT.
  RETURN_IF_ERROR(ApplySflowBreakoutConfig(sut, sut_gnmi_stub.get(),
                                           breakout_config_with_sflow));
  LOG(INFO) << "Configured breakout mode "
            << selected_port_info.supported_breakout_mode << " on port "
            << selected_port_info.port_name << " and sFlow config on "
            << sut.ChassisName() << ".";

  // Verify breakout status.
  // Wait at most 60s for breakout config to go through.
  // Expect the ports to be up if the other side has performed a breakout.
  RETURN_IF_ERROR(pins_test::WaitForCondition(
      VerifyAppliedBreakoutAndSflowConverged, absl::Seconds(60),
      sut_gnmi_stub.get(), orig_breakout_info, new_breakout_info, option));

  SflowBreakoutResult result;
  for (const auto& [port_name, unused] : new_breakout_info) {
    result.breakout_ports.push_back(port_name);
  }
  result.port_info = selected_port_info;

  LOG(INFO) << "========== " << __func__
            << " Successfully applied port breakout on " << sut.ChassisName()
            << ". Breakout ports: "
            << absl::StrJoin(result.breakout_ports, ", ") << " ============";
  return result;
}
}  // namespace pins_test
