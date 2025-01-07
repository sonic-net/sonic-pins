#include "tests/qos/qos_test_util.h"

#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/string_view.h"
#include "absl/strings/strip.h"
#include "absl/strings/substitute.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "google/protobuf/util/json_util.h"
#include "gutil/collections.h"
#include "gutil/proto.h"
#include "gutil/status.h"
#include "include/nlohmann/json.hpp"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/gnmi/openconfig.pb.h"
#include "lib/utils/json_utils.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "proto/gnmi/gnmi.pb.h"
#include "tests/qos/gnmi_parsers.h"

namespace pins_test {

QueueCounters operator-(const QueueCounters &x, const QueueCounters &y) {
  return QueueCounters{
      .num_packets_transmitted =
          x.num_packets_transmitted - y.num_packets_transmitted,
      .num_packets_dropped = x.num_packets_dropped - y.num_packets_dropped,
  };
}

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
                        &counters.num_packets_dropped)) {
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
int64_t TotalPacketsForQueue(const QueueCounters &counters) {
  return counters.num_packets_dropped + counters.num_packets_transmitted;
}

absl::Status SetPortSpeedInBitsPerSecond(const std::string &port_speed,
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

absl::StatusOr<int64_t>
GetPortSpeedInBitsPerSecond(const std::string &interface_name,
                            gnmi::gNMI::StubInterface &gnmi_stub) {
  // Map keyed on openconfig speed string to value in bits per second.
  // http://ops.openconfig.net/branches/models/master/docs/openconfig-interfaces.html#mod-openconfig-if-ethernet
  const auto kPortSpeedTable =
      absl::flat_hash_map<absl::string_view, uint64_t>({
          {"openconfig-if-ethernet:SPEED_100GB", 100000000000},
          {"openconfig-if-ethernet:SPEED_200GB", 200000000000},
          {"openconfig-if-ethernet:SPEED_400GB", 400000000000},
      });
  std::string speed_state_path =
      absl::StrCat("interfaces/interface[name=", interface_name,
                   "]/ethernet/state/port-speed");

  std::string parse_str = "openconfig-if-ethernet:port-speed";
  ASSIGN_OR_RETURN(
      std::string response,
      GetGnmiStatePathInfo(&gnmi_stub, speed_state_path, parse_str));

  auto speed = kPortSpeedTable.find(StripQuotes(response));
  if (speed == kPortSpeedTable.end()) {
    return absl::NotFoundError(response);
  }
  return speed->second;
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
        ASSIGN_OR_RETURN(int64_t bit_per_second,
                         GetPortSpeedInBitsPerSecond(interface, gnmi_stub));
        links.push_back(IxiaLink{
            .ixia_interface = info.peer_interface_name,
            .sut_interface = interface,
            .sut_interface_bits_per_second = bit_per_second,
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

absl::StatusOr<absl::flat_hash_map<int, std::string>> GetIpv4DscpToQueueMapping(
    absl::string_view port, gnmi::gNMI::StubInterface &gnmi_stub) {
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

absl::StatusOr<absl::flat_hash_map<int, std::string>> GetIpv6DscpToQueueMapping(
    absl::string_view port, gnmi::gNMI::StubInterface &gnmi_stub) {
  // TODO: Actually parse config -- hard-coded for now.
  return GetIpv4DscpToQueueMapping(port, gnmi_stub);
}

absl::StatusOr<absl::flat_hash_map<std::string, std::vector<int>>>
GetQueueToIpv4DscpsMapping(absl::string_view port,
                           gnmi::gNMI::StubInterface &gnmi_stub) {
  absl::flat_hash_map<std::string, std::vector<int>> dscps_by_queue;
  absl::flat_hash_map<int, std::string> queue_by_dscp;
  ASSIGN_OR_RETURN(queue_by_dscp, GetIpv4DscpToQueueMapping(port, gnmi_stub));
  for (auto &[dscp, queue] : queue_by_dscp) {
    dscps_by_queue[queue].push_back(dscp);
  }
  return dscps_by_queue;
}

absl::StatusOr<absl::flat_hash_map<std::string, std::vector<int>>>
GetQueueToIpv6DscpsMapping(absl::string_view port,
                           gnmi::gNMI::StubInterface &gnmi_stub) {
  absl::flat_hash_map<std::string, std::vector<int>> dscps_by_queue;
  absl::flat_hash_map<int, std::string> queue_by_dscp;
  ASSIGN_OR_RETURN(queue_by_dscp, GetIpv6DscpToQueueMapping(port, gnmi_stub));
  for (auto &[dscp, queue] : queue_by_dscp) {
    dscps_by_queue[queue].push_back(dscp);
  }
  return dscps_by_queue;
}

absl::Status SetPortLoopbackMode(bool port_loopback,
                                 absl::string_view interface_name,
                                 gnmi::gNMI::StubInterface &gnmi_stub) {
  std::string config_path = absl::StrCat(
      "interfaces/interface[name=", interface_name, "]/config/loopback-mode");
  std::string config_json;
  if (port_loopback) {
    config_json = "{\"openconfig-interfaces:loopback-mode\":true}";
  } else {
    config_json = "{\"openconfig-interfaces:loopback-mode\":false}";
  }

  RETURN_IF_ERROR(pins_test::SetGnmiConfigPath(
      &gnmi_stub, config_path, GnmiSetType::kUpdate, config_json));

  return absl::OkStatus();
}

absl::StatusOr<std::string>
GetQueueNameByDscpAndPort(int dscp, absl::string_view port,
                          gnmi::gNMI::StubInterface &gnmi_stub) {
  absl::flat_hash_map<int, std::string> queue_by_dscp;
  ASSIGN_OR_RETURN(queue_by_dscp, GetIpv4DscpToQueueMapping(port, gnmi_stub));
  return gutil::FindOrStatus(queue_by_dscp, dscp);
}

absl::StatusOr<std::string>
GetSchedulerPolicyNameByEgressPort(absl::string_view egress_port,
                                   gnmi::gNMI::StubInterface &gnmi) {
  const std::string kPath = absl::StrFormat(
      "qos/interfaces/interface[interface-id=%s]/output/scheduler-policy/"
      "config/name",
      egress_port);
  ASSIGN_OR_RETURN(std::string name,
                   ReadGnmiPath(&gnmi, kPath, gnmi::GetRequest::CONFIG,
                                "openconfig-qos:name"));
  return std::string(StripQuotes(name));
}

static std::string
SchedulerPolicyPath(absl::string_view scheduler_policy_name) {
  return absl::StrFormat("qos/scheduler-policies/scheduler-policy[name=%s]",
                         scheduler_policy_name);
}

absl::StatusOr<std::string>
GetSchedulerPolicyConfig(absl::string_view scheduler_policy_name,
                         gnmi::gNMI::StubInterface &gnmi) {
  std::string path = SchedulerPolicyPath(scheduler_policy_name);
  return ReadGnmiPath(&gnmi, path, gnmi::GetRequest::CONFIG, "");
}

absl::StatusOr<openconfig::Qos::SchedulerPolicy>
GetSchedulerPolicyConfigAsProto(absl::string_view scheduler_policy_name,
                                gnmi::gNMI::StubInterface &gnmi) {
  const std::string kPath = SchedulerPolicyPath(scheduler_policy_name);
  const std::string kRoot = "openconfig-qos:scheduler-policy";
  ASSIGN_OR_RETURN(const std::string kRawConfig,
                   ReadGnmiPath(&gnmi, kPath, gnmi::GetRequest::CONFIG, kRoot));
  ASSIGN_OR_RETURN(
      openconfig::Qos::SchedulerPolicy proto_config,
      gutil::ParseJsonAsProto<openconfig::Qos::SchedulerPolicy>(
          StripBrackets(kRawConfig), /*ignore_unknown_fields=*/true));
  return proto_config;
}

absl::Status
UpdateSchedulerPolicyConfig(absl::string_view scheduler_policy_name,
                            absl::string_view config,
                            gnmi::gNMI::StubInterface &gnmi) {
  std::string path = SchedulerPolicyPath(scheduler_policy_name);
  return SetGnmiConfigPath(&gnmi, path, GnmiSetType::kUpdate, config);
}

absl::Status SetSchedulerPolicyParameters(
    absl::string_view scheduler_policy_name,
    absl::flat_hash_map<std::string, SchedulerParameters> params_by_queue_name,
    gnmi::gNMI::StubInterface &gnmi, absl::Duration convergence_timeout) {
  // Pull existing config.
  const std::string kPath = SchedulerPolicyPath(scheduler_policy_name);
  const std::string kRoot = "openconfig-qos:scheduler-policy";
  ASSIGN_OR_RETURN(const std::string kRawConfig,
                   ReadGnmiPath(&gnmi, kPath, gnmi::GetRequest::CONFIG, kRoot));
  ASSIGN_OR_RETURN(
      openconfig::Qos::SchedulerPolicy proto_config,
      gutil::ParseJsonAsProto<openconfig::Qos::SchedulerPolicy>(
          StripBrackets(kRawConfig), /*ignore_unknown_fields=*/true));

  // Updated config.
  for (openconfig::Qos::Scheduler &scheduler :
       *proto_config.mutable_schedulers()->mutable_scheduler()) {
    if (scheduler.inputs().input_size() == 0)
      continue;
    if (scheduler.inputs().input_size() > 1) {
      return gutil::UnimplementedErrorBuilder()
             << "scheduler with several inputs unsupported: "
             << scheduler.DebugString();
    }
    const std::string kQueue = scheduler.inputs().input(0).config().queue();
    const std::string kSchedulerPath = absl::StrFormat(
        "%s/schedulers/scheduler[sequence=%d]",
        SchedulerPolicyPath(scheduler_policy_name), scheduler.sequence());
    LOG(INFO) << "found scheduler '" << kSchedulerPath << " for queue "
              << kQueue;
    SchedulerParameters *const params =
        gutil::FindOrNull(params_by_queue_name, kQueue);
    LOG(INFO) << "-> " << (params == nullptr ? "no " : "")
              << "changes requested";
    if (params == nullptr)
      continue;

    if (scheduler.config().type() !=
        "openconfig-qos-types:TWO_RATE_THREE_COLOR") {
      return gutil::InvalidArgumentErrorBuilder()
             << "scheduler '" << kSchedulerPath << "' of unsupported type: '"
             << scheduler.config().type() << "'";
    }

    auto &config = *scheduler.mutable_two_rate_three_color()->mutable_config();
    if (auto pir = params->peak_information_rate; pir.has_value()) {
      // OpenConfig uses bits, but our API uses bytes for consistency.
      config.set_pir(absl::StrCat(*pir * 8));
    }
    if (auto be = params->excess_burst_size; be.has_value()) {
      config.set_be(*be);
    }
    if (auto cir = params->committed_information_rate; cir.has_value()) {
      // OpenConfig uses bits, but our API uses bytes for consistency.
      config.set_cir(absl::StrCat(*cir * 8));
    }
    if (auto bc = params->committed_burst_size; bc.has_value()) {
      config.set_bc(*bc);
    }

    auto &input_config =
        *scheduler.mutable_inputs()->mutable_input(0)->mutable_config();

    if (auto weight = params->weight; weight.has_value()) {
      input_config.set_weight(absl::StrCat(*weight));
    }

    LOG(INFO) << "modified scheduler: " << scheduler.DebugString();

    // We update the entire scheduler subtree, instead of applying updates
    // incrementally, to work around b/228117691.
    {
      // Convert proto back to JSON string.
      ASSIGN_OR_RETURN(std::string scheduler_json,
                       gutil::SerializeProtoAsJson(scheduler));
      // Apply updated scheduler.
      RETURN_IF_ERROR(SetGnmiConfigPath(
          &gnmi, kSchedulerPath, GnmiSetType::kUpdate,
          absl::StrFormat(R"({ "scheduler": [%s] })", scheduler_json)));
    }
  }

  // Wait for convergence.
  const absl::Time kDeadline = absl::Now() + convergence_timeout;
  std::string config_state_diff;
  do {
    ASSIGN_OR_RETURN(std::string raw_config,
                     ReadGnmiPath(&gnmi, kPath, gnmi::GetRequest::ALL, kRoot));
    ASSIGN_OR_RETURN(
        openconfig::Qos::SchedulerPolicy proto_config,
        gutil::ParseJsonAsProto<openconfig::Qos::SchedulerPolicy>(
            StripBrackets(raw_config), /*ignore_unknown_fields=*/true));
    for (openconfig::Qos::Scheduler &scheduler :
         *proto_config.mutable_schedulers()->mutable_scheduler()) {
      if (!scheduler.has_two_rate_three_color())
        continue;
      auto &config = scheduler.two_rate_three_color().config();
      auto &state = scheduler.two_rate_three_color().state();
      ASSIGN_OR_RETURN(config_state_diff, gutil::ProtoDiff(config, state));
      if (!config_state_diff.empty()) {
        absl::StrAppendFormat(&config_state_diff,
                              "between two-rate-three-color config and state, "
                              "for scheduler '%s[%d]'",
                              scheduler_policy_name, scheduler.sequence());
        break;
      }

      if (!scheduler.has_inputs())
        continue;
      auto &input_config = scheduler.inputs().input(0).config();
      auto &input_state = scheduler.inputs().input(0).state();
      ASSIGN_OR_RETURN(config_state_diff,
                       gutil::ProtoDiff(input_config, input_state));
      if (!config_state_diff.empty()) {
        absl::StrAppendFormat(&config_state_diff,
                              "between input config and state, "
                              "for scheduler '%s[%d]'",
                              scheduler_policy_name, scheduler.sequence());
        break;
      }
    }
  } while (!config_state_diff.empty() && absl::Now() < kDeadline);

  if (!config_state_diff.empty()) {
    return gutil::DeadlineExceededErrorBuilder()
           << "QoS scheduler policy state paths did not converge within "
           << convergence_timeout << "; diff:\n"
           << config_state_diff;
  }

  return absl::OkStatus();
}

absl::StatusOr<absl::flat_hash_map<std::string, int64_t>>
GetSchedulerPolicyWeightsByQueue(absl::string_view scheduler_policy_name,
                                 gnmi::gNMI::StubInterface &gnmi) {
  // The mapping we're about to compute.
  absl::flat_hash_map<std::string, int64_t> weight_by_queue_name;

  ASSIGN_OR_RETURN(std::vector<QueueInfo> queues,
                   GetQueuesForSchedulerPolicyInDescendingOrderOfPriority(
                       scheduler_policy_name, gnmi));
  for (auto &queue : queues) {
    if (queue.type == QueueType::kRoundRobin) {
      weight_by_queue_name[queue.name] = queue.weight;
    }
  }
  return weight_by_queue_name;
}

absl::StatusOr<std::vector<std::string>>
GetStrictlyPrioritizedQueuesInDescendingOrderOfPriority(
    absl::string_view scheduler_policy_name, gnmi::gNMI::StubInterface &gnmi) {
  std::vector<std::string> strict_queues;
  ASSIGN_OR_RETURN(std::vector<QueueInfo> queues,
                   GetQueuesForSchedulerPolicyInDescendingOrderOfPriority(
                       scheduler_policy_name, gnmi));
  for (auto &queue : queues) {
    if (queue.type == QueueType::kStrictlyPrioritized)
      strict_queues.push_back(queue.name);
  }
  return strict_queues;
}

bool IsStrict(const openconfig::Qos::Scheduler &scheduler) {
  return scheduler.config().priority() == "STRICT";
}

absl::StatusOr<std::vector<QueueInfo>>
GetQueuesForSchedulerPolicyInDescendingOrderOfPriority(
    absl::string_view scheduler_policy_name, gnmi::gNMI::StubInterface &gnmi) {
  std::vector<QueueInfo> queues;

  // Read and sort schedulers.
  ASSIGN_OR_RETURN(
      const openconfig::Qos::SchedulerPolicy kSchedulerPolicy,
      GetSchedulerPolicyConfigAsProto(scheduler_policy_name, gnmi));
  std::vector<openconfig::Qos::Scheduler> schedulers(
      kSchedulerPolicy.schedulers().scheduler().begin(),
      kSchedulerPolicy.schedulers().scheduler().end());
  absl::c_sort(schedulers, [](const auto &a, const auto &b) -> bool {
    // TODO: Remove this temporary workaround once strict queues
    // are no longer inverted.
    if (IsStrict(a) && IsStrict(b))
      return a.sequence() > b.sequence();
    return a.sequence() < b.sequence();
  });

  // Extract queue info, and ensure strict queues come before round-robin
  // queues.
  bool have_seen_round_robin_scheduler = false;
  for (const openconfig::Qos::Scheduler &scheduler : schedulers) {
    if (scheduler.inputs().input_size() != 1) {
      return gutil::UnimplementedErrorBuilder()
             << "scheduler with none/several inputs unsupported: "
             << scheduler.DebugString();
    }
    const auto &input = scheduler.inputs().input(0);
    const std::string &queue = input.config().queue();
    const std::string &weight = input.config().weight();
    QueueInfo &info = queues.emplace_back();
    info = QueueInfo{
        .name = queue,
        .type = IsStrict(scheduler) ? QueueType::kStrictlyPrioritized
                                    : QueueType::kRoundRobin,
        .sequence = static_cast<int>(scheduler.sequence()),
    };

    // Extract weight, if relevant.
    if (info.type == QueueType::kRoundRobin) {
      have_seen_round_robin_scheduler = true;
      bool parsed_weight = absl::SimpleAtoi(weight, &info.weight);
      if (!parsed_weight) {
        return gutil::UnknownErrorBuilder()
               << "unable to parse weight '" << weight << "' for queue '"
               << queue << "' in scheduler of sequence "
               << scheduler.config().sequence() << " in scheduler policy '"
               << scheduler_policy_name << "'";
      }
    }

    // Ensure invariant.
    if (IsStrict(scheduler) && have_seen_round_robin_scheduler) {
      return gutil::UnimplementedErrorBuilder()
             << "found strict scheduler after weighted scheduler";
    }
  }
  return queues;
}

absl::StatusOr<std::string>
GetBufferAllocationProfileByEgressPort(absl::string_view egress_port,
                                       gnmi::gNMI::StubInterface &gnmi) {
  const std::string kPath =
      absl::StrFormat("qos/interfaces/interface[interface-id=%s]/output/config/"
                      "buffer-allocation-profile",
                      egress_port);
  ASSIGN_OR_RETURN(std::string name,
                   ReadGnmiPath(&gnmi, kPath, gnmi::GetRequest::CONFIG,
                                "openconfig-qos:buffer-allocation-profile"));
  return std::string(StripQuotes(name));
}

static std::string
BufferAllocationProfilePath(absl::string_view buffer_allocation_profile_name) {
  return absl::StrFormat(
      "qos/buffer-allocation-profiles/buffer-allocation-profile[name=%s]",
      buffer_allocation_profile_name);
}

absl::StatusOr<std::string> GetBufferAllocationProfileConfig(
    absl::string_view buffer_allocation_profile_name,
    gnmi::gNMI::StubInterface &gnmi) {
  std::string path =
      BufferAllocationProfilePath(buffer_allocation_profile_name);
  return ReadGnmiPath(&gnmi, path, gnmi::GetRequest::CONFIG, "");
}

absl::StatusOr<openconfig::Qos::BufferAllocationProfile>
GetBufferAllocationProfileConfigAsProto(
    absl::string_view buffer_allocation_profile,
    gnmi::gNMI::StubInterface &gnmi) {
  const std::string kPath = SchedulerPolicyPath(buffer_allocation_profile);
  const std::string kRoot = "openconfig-qos:buffer-allocation-profile";
  ASSIGN_OR_RETURN(const std::string kRawConfig,
                   ReadGnmiPath(&gnmi, kPath, gnmi::GetRequest::CONFIG, kRoot));
  ASSIGN_OR_RETURN(
      openconfig::Qos::BufferAllocationProfile proto_config,
      gutil::ParseJsonAsProto<openconfig::Qos::BufferAllocationProfile>(
          StripBrackets(kRawConfig), /*ignore_unknown_fields=*/true));
  return proto_config;
}

absl::Status
UpdateBufferAllocationProfileConfig(absl::string_view buffer_allocation_profile,
                                    absl::string_view config,
                                    gnmi::gNMI::StubInterface &gnmi) {
  std::string path = BufferAllocationProfilePath(buffer_allocation_profile);
  return SetGnmiConfigPath(&gnmi, path, GnmiSetType::kUpdate, config);
}

absl::Status SetBufferConfigParameters(
    absl::string_view buffer_allocation_profile,
    absl::flat_hash_map<std::string, BufferParameters> params_by_queue_name,
    gnmi::gNMI::StubInterface &gnmi, absl::Duration convergence_timeout) {
  // Pull existing config.
  const std::string kPath =
      BufferAllocationProfilePath(buffer_allocation_profile);
  const std::string kRoot = "openconfig-qos:buffer-allocation-profile";
  ASSIGN_OR_RETURN(const std::string kRawConfig,
                   ReadGnmiPath(&gnmi, kPath, gnmi::GetRequest::CONFIG, kRoot));
  ASSIGN_OR_RETURN(
      openconfig::Qos::BufferAllocationProfile proto_config,
      gutil::ParseJsonAsProto<openconfig::Qos::BufferAllocationProfile>(
          StripBrackets(kRawConfig), /*ignore_unknown_fields=*/true));

  // Updated config.
  for (openconfig::Qos::Queue &queue :
       *proto_config.mutable_queues()->mutable_queue()) {
    const std::string kBufferQueuePath =
        absl::StrFormat("%s/queues/queue[name=%s]", kPath, queue.name());

    BufferParameters *const params =
        gutil::FindOrNull(params_by_queue_name, queue.name());

    if (params == nullptr) {
      continue;
    }

    if (auto dedicated_buffer = params->dedicated_buffer;
        dedicated_buffer.has_value()) {
      queue.mutable_config()->set_dedicated_buffer(
          absl::StrCat(*dedicated_buffer));
    }

    if (auto use_shared_buffer = params->use_shared_buffer;
        use_shared_buffer.has_value()) {
      queue.mutable_config()->set_use_shared_buffer(*use_shared_buffer);
    }
    if (auto shared_buffer_limit_type = params->shared_buffer_limit_type;
        shared_buffer_limit_type.has_value()) {
      queue.mutable_config()->set_shared_buffer_limit_type(
          *shared_buffer_limit_type);
    }

    if (auto dynamic_limit_scaling_factor =
            params->dynamic_limit_scaling_factor;
        dynamic_limit_scaling_factor.has_value()) {
      queue.mutable_config()->set_dynamic_limit_scaling_factor(
          *dynamic_limit_scaling_factor);
    }

    if (auto shared_static_limit = params->shared_static_limit;
        shared_static_limit.has_value()) {
      queue.mutable_config()->set_static_shared_buffer_limit(
          *shared_static_limit);
    }

    // We update the entire queue subtree.
    {
      // Convert proto back to JSON string.
      ASSIGN_OR_RETURN(std::string buffer_queue_json,
                       gutil::SerializeProtoAsJson(queue));
      // Apply updated queue.
      RETURN_IF_ERROR(SetGnmiConfigPath(
          &gnmi, kBufferQueuePath, GnmiSetType::kUpdate,
          absl::StrFormat(R"({ "queue": [%s] })", buffer_queue_json)));
    }
  }

  // Wait for convergence.
  const absl::Time kDeadline = absl::Now() + convergence_timeout;
  std::string config_state_diff;
  do {
    ASSIGN_OR_RETURN(std::string raw_config,
                     ReadGnmiPath(&gnmi, kPath, gnmi::GetRequest::ALL, kRoot));
    ASSIGN_OR_RETURN(
        openconfig::Qos::BufferAllocationProfile proto_config,
        gutil::ParseJsonAsProto<openconfig::Qos::BufferAllocationProfile>(
            StripBrackets(raw_config), /*ignore_unknown_fields=*/true));
    for (openconfig::Qos::Queue &queue :
         *proto_config.mutable_queues()->mutable_queue()) {
      auto &config = queue.config();
      auto &state = queue.state();
      ASSIGN_OR_RETURN(config_state_diff, gutil::ProtoDiff(config, state));
      LOG(INFO) << "config state diff : " << config_state_diff;
      if (!config_state_diff.empty()) {
        absl::StrAppendFormat(&config_state_diff,
                              "between queue config and state, "
                              "for buffer-allocation-profile '%s[%s]'",
                              buffer_allocation_profile, queue.name());
        break;
      }
    }
  } while (!config_state_diff.empty() && absl::Now() < kDeadline);

  // TODO: Uncomment after convergence issue is resolved.
  // if (!config_state_diff.empty()) {
  // return gutil::DeadlineExceededErrorBuilder()
  //         << "QoS buffer config state paths did not converge within "
  //         << convergence_timeout << "; diff:\n"
  //         << config_state_diff;
  // }
  return absl::OkStatus();

}

}  // namespace pins_test
