#include "tests/qos/qos_test_util.h"

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "gutil/status.h"
#include "lib/gnmi/gnmi_helper.h"

namespace pins_test {
absl::StatusOr<QueueCounters> GetGnmiQueueCounters(
    absl::string_view port, absl::string_view queue,
    gnmi::gNMI::StubInterface &gnmi_stub) {
  QueueCounters counters;

  const std::string openconfig_transmit_count_state_path = absl::Substitute(
      "qos/interfaces/interface[interface-id=$0]"
      "/output/queues/queue[name=$1]/state/transmit-pkts",
      port, queue);

  ASSIGN_OR_RETURN(
      std::string transmit_counter_response,
      GetGnmiStatePathInfo(&gnmi_stub, openconfig_transmit_count_state_path,
                           "openconfig-qos:transmit-pkts"));

  if (!absl::SimpleAtoi(StripQuotes(transmit_counter_response),
                        &counters.num_packets_transmitted)) {
    return absl::InternalError(absl::StrCat("Unable to parse counter from ",
                                            transmit_counter_response));
  }

  const std::string openconfig_drop_count_state_path = absl::Substitute(
      "qos/interfaces/interface[interface-id=$0]"
      "/output/queues/queue[name=$1]/state/dropped-pkts",
      port, queue);

  ASSIGN_OR_RETURN(
      std::string drop_counter_response,
      GetGnmiStatePathInfo(&gnmi_stub, openconfig_drop_count_state_path,
                           "openconfig-qos:dropped-pkts"));

  if (!absl::SimpleAtoi(StripQuotes(drop_counter_response),
                        &counters.num_packet_dropped)) {
    return absl::InternalError(
        absl::StrCat("Unable to parse counter from ", drop_counter_response));
  }
  return counters;
}

absl::StatusOr<ResultWithTimestamp> GetGnmiQueueCounterWithTimestamp(
    absl::string_view port, absl::string_view queue,
    absl::string_view statistic, gnmi::gNMI::StubInterface &gnmi_stub) {
  const std::string openconfig_transmit_count_state_path = absl::Substitute(
      "qos/interfaces/interface[interface-id=$0]"
      "/output/queues/queue[name=$1]/state/$2",
      port, queue, statistic);
  
  return GetGnmiStatePathAndTimestamp(&gnmi_stub,
                                      openconfig_transmit_count_state_path,
                                      "openconfig-qos:transmit-pkts");
}

// Returns the total number of packets enqueued for the queue with the given
// `QueueCounters`.
int64_t CumulativeNumPacketsEnqueued(const QueueCounters &counters) {
  return counters.num_packet_dropped + counters.num_packets_transmitted;
}

absl::Status SetPortSpeed(const std::string &port_speed,
                          const std::string &iface,
                          gnmi::gNMI::StubInterface &gnmi_stub) {
  std::string ops_config_path = absl::StrCat(
      "interfaces/interface[name=", iface, "]/ethernet/config/port-speed");
  std::string ops_val =
      absl::StrCat("{\"openconfig-if-ethernet:port-speed\":", port_speed, "}");

  RETURN_IF_ERROR(pins_test::SetGnmiConfigPath(&gnmi_stub, ops_config_path,
                                               GnmiSetType::kUpdate, ops_val));

  return absl::OkStatus();
}

absl::Status SetPortMtu(int port_mtu, const std::string &interface_name,
                        gnmi::gNMI::StubInterface &gnmi_stub) {
  std::string config_path = absl::StrCat(
      "interfaces/interface[name=", interface_name, "]/config/mtu");
  std::string value = absl::StrCat("{\"config:mtu\":", port_mtu, "}");

  RETURN_IF_ERROR(pins_test::SetGnmiConfigPath(&gnmi_stub, config_path,
                                               GnmiSetType::kUpdate, value));

  return absl::OkStatus();
}

absl::StatusOr<bool> CheckLinkUp(const std::string &iface,
                                 gnmi::gNMI::StubInterface &gnmi_stub) {
  std::string oper_status_state_path =
      absl::StrCat("interfaces/interface[name=", iface, "]/state/oper-status");

  std::string parse_str = "openconfig-interfaces:oper-status";
  ASSIGN_OR_RETURN(
      std::string ops_response,
      GetGnmiStatePathInfo(&gnmi_stub, oper_status_state_path, parse_str));

  return ops_response == "\"UP\"";
}

// Go over the connections and return vector of connections
// whose links are up.
absl::StatusOr<std::vector<IxiaLink>> GetReadyIxiaLinks(
    thinkit::GenericTestbed &generic_testbed,
    gnmi::gNMI::StubInterface &gnmi_stub) {
  std::vector<IxiaLink> links;

  absl::flat_hash_map<std::string, thinkit::InterfaceInfo> interface_info =
      generic_testbed.GetSutInterfaceInfo();
  // Loop through the interface_info looking for Ixia/SUT interface pairs,
  // checking if the link is up.  Add the pair to connections.
  for (const auto &[interface, info] : interface_info) {
    bool sut_link_up = false;
    if (info.interface_modes.contains(thinkit::TRAFFIC_GENERATOR))
    {
      ASSIGN_OR_RETURN(sut_link_up, CheckLinkUp(interface, gnmi_stub));
      if (sut_link_up) {
        links.push_back({
            .ixia_interface = info.peer_interface_name,
            .sut_interface = interface,
        });
      }
    }
  }

  return links;
}

absl::StatusOr<absl::flat_hash_map<int, std::string>>
ParseIpv4DscpToQueueMapping(absl::string_view gnmi_config) {
  // TODO: Actually parse config -- hard-coded for now.
  absl::flat_hash_map<int, std::string> queue_by_dscp;
  for (int dscp = 0; dscp < 64; ++dscp) queue_by_dscp[dscp] = "BE1";
  for (int dscp = 8; dscp <= 11; ++dscp) queue_by_dscp[dscp] = "AF1";
  queue_by_dscp[13] = "LLQ1";
  for (int dscp = 16; dscp <= 19; ++dscp) queue_by_dscp[dscp] = "AF2";
  queue_by_dscp[21] = "LLQ2";
  for (int dscp = 24; dscp <= 27; ++dscp) queue_by_dscp[dscp] = "AF3";
  for (int dscp = 32; dscp <= 35; ++dscp) queue_by_dscp[dscp] = "AF4";
  for (int dscp = 48; dscp <= 59; ++dscp) queue_by_dscp[dscp] = "NC1";
  return queue_by_dscp;
}

absl::StatusOr<absl::flat_hash_map<int, std::string>>
ParseIpv6DscpToQueueMapping(absl::string_view gnmi_config) {
  // TODO: Actually parse config -- hard-coded for now.
  return ParseIpv4DscpToQueueMapping(gnmi_config);
}

}  // namespace pins_test
