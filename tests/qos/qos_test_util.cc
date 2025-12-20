// Copyright 2025 Google LLC
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

#include "tests/qos/qos_test_util.h"

#include <array>

#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/match.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "google/protobuf/util/json_util.h"
#include "gutil/gutil/collections.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/status.h"
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

absl::StatusOr<absl::flat_hash_map<std::string, std::vector<int>>>
GetQueueToDscpsMapping(absl::flat_hash_map<int, std::string> queue_by_dscp) {
  absl::flat_hash_map<std::string, std::vector<int>> dscps_by_queue;
  for (auto &[dscp, queue] : queue_by_dscp) {
    dscps_by_queue[queue].push_back(dscp);
  }
  return dscps_by_queue;
}

absl::StatusOr<std::string> GetQueueNameByDscpAndPort(
    int dscp, absl::string_view port, gnmi::gNMI::StubInterface &gnmi_stub,
    absl::flat_hash_map<int, std::string> queue_by_dscp) {
  return gutil::FindOrStatus(queue_by_dscp, dscp);
}

absl::StatusOr<std::string> GetSchedulerPolicyNameByEgressPort(
    absl::string_view egress_port, gnmi::gNMI::StubInterface &gnmi) {
  const std::string kPath = absl::StrFormat(
      "qos/interfaces/interface[interface-id=%s]/output/scheduler-policy/"
      "config/name",
      egress_port);
  ASSIGN_OR_RETURN(std::string name,
                   ReadGnmiPath(&gnmi, kPath, gnmi::GetRequest::CONFIG,
                                "openconfig-qos:name"));
  return std::string(StripQuotes(name));
}

static std::string SchedulerPolicyPath(
    absl::string_view scheduler_policy_name) {
  return absl::StrFormat("qos/scheduler-policies/scheduler-policy[name=%s]",
                         scheduler_policy_name);
}

absl::StatusOr<std::string> GetSchedulerPolicyConfig(
    absl::string_view scheduler_policy_name, gnmi::gNMI::StubInterface &gnmi) {
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

absl::Status UpdateSchedulerPolicyConfig(
    absl::string_view scheduler_policy_name, absl::string_view config,
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
    if (scheduler.inputs().input_size() == 0) continue;
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
    if (params == nullptr) continue;

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
      if (!scheduler.has_two_rate_three_color()) continue;
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

      if (!scheduler.has_inputs()) continue;
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

absl::Status ReplaceCpuSchedulerPolicyParametersForAllQueues(
    gnmi::gNMI::StubInterface &gnmi_stub, SchedulerParameters scheduler_param) {
  ASSIGN_OR_RETURN(std::string scheduler_policy_name,
                   GetSchedulerPolicyNameByEgressPort("CPU", gnmi_stub));
  absl::flat_hash_map<std::string, SchedulerParameters> scheduler_params;
  ASSIGN_OR_RETURN(std::vector<std::string> queues,
                   GetQueuesByEgressPort("CPU", gnmi_stub));
  for (absl::string_view queue_name : queues) {
    scheduler_params[queue_name] = scheduler_param;
  }
  return SetSchedulerPolicyParameters(scheduler_policy_name, scheduler_params,
                                      gnmi_stub);
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

absl::StatusOr<absl::flat_hash_set<std::string>>
GetStrictlyPrioritizedQueuesMap(absl::string_view scheduler_policy_name,
                                gnmi::gNMI::StubInterface &gnmi) {
  absl::flat_hash_set<std::string> strict_queues;
  ASSIGN_OR_RETURN(std::vector<QueueInfo> queues,
                   GetQueuesForSchedulerPolicyInDescendingOrderOfPriority(
                       scheduler_policy_name, gnmi));
  for (auto &queue : queues) {
    if (queue.type == QueueType::kStrictlyPrioritized)
      strict_queues.insert(queue.name);
  }
  return strict_queues;
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
    return a.sequence() < b.sequence();
  });

  // Extract queue info.
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
      bool parsed_weight = absl::SimpleAtoi(weight, &info.weight);
      if (!parsed_weight) {
        return gutil::UnknownErrorBuilder()
               << "unable to parse weight '" << weight << "' for queue '"
               << queue << "' in scheduler of sequence "
               << scheduler.config().sequence() << " in scheduler policy '"
               << scheduler_policy_name << "'";
      }
    }
  }
  return queues;
}

absl::StatusOr<std::string> GetBufferAllocationProfileByEgressPort(
    absl::string_view egress_port, gnmi::gNMI::StubInterface &gnmi) {
  const std::string kPath = absl::StrFormat(
      "qos/interfaces/interface[interface-id=%s]/output/config/"
      "buffer-allocation-profile",
      egress_port);
  ASSIGN_OR_RETURN(std::string name,
                   ReadGnmiPath(&gnmi, kPath, gnmi::GetRequest::CONFIG,
                                "openconfig-qos:buffer-allocation-profile"));
  return std::string(StripQuotes(name));
}

static std::string BufferAllocationProfilePath(
    absl::string_view buffer_allocation_profile_name) {
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
  const std::string kPath =
      BufferAllocationProfilePath(buffer_allocation_profile);
  const std::string kRoot = "openconfig-qos:buffer-allocation-profile";
  ASSIGN_OR_RETURN(const std::string kRawConfig,
                   ReadGnmiPath(&gnmi, kPath, gnmi::GetRequest::CONFIG, kRoot));
  ASSIGN_OR_RETURN(
      openconfig::Qos::BufferAllocationProfile proto_config,
      gutil::ParseJsonAsProto<openconfig::Qos::BufferAllocationProfile>(
          StripBrackets(kRawConfig), /*ignore_unknown_fields=*/true));
  return proto_config;
}

absl::StatusOr<std::vector<std::string>> GetQueuesByEgressPort(
    absl::string_view egress_port, gnmi::gNMI::StubInterface &gnmi) {
  std::vector<std::string> queues;
  ASSIGN_OR_RETURN(std::string buffer_profile,
                   GetBufferAllocationProfileByEgressPort(egress_port, gnmi));
  ASSIGN_OR_RETURN(
      openconfig::Qos::BufferAllocationProfile proto_config,
      GetBufferAllocationProfileConfigAsProto(buffer_profile, gnmi));
  for (openconfig::Qos::Queue &queue :
       *proto_config.mutable_queues()->mutable_queue()) {
    queues.push_back(queue.name());
  }
  return queues;
}
absl::Status UpdateBufferAllocationProfileConfig(
    absl::string_view buffer_allocation_profile, absl::string_view config,
    gnmi::gNMI::StubInterface &gnmi) {
  std::string path = BufferAllocationProfilePath(buffer_allocation_profile);
  return SetGnmiConfigPath(&gnmi, path, GnmiSetType::kUpdate, config);
}

absl::Status SetBufferConfigParameters(
    absl::string_view buffer_allocation_profile,
    absl::flat_hash_map<std::string, BufferParameters> params_by_queue_name,
    gnmi::gNMI::StubInterface &gnmi, absl::Duration convergence_timeout) {
  // Pull existing config.
  const std::string kPath = "qos";
  const std::string kRoot = "openconfig-qos:qos";
  ASSIGN_OR_RETURN(const std::string kRawConfig,
                   ReadGnmiPath(&gnmi, kPath, gnmi::GetRequest::CONFIG, kRoot));
  ASSIGN_OR_RETURN(
      openconfig::Qos proto_config,
      gutil::ParseJsonAsProto<openconfig::Qos>(StripBrackets(kRawConfig),
                                               /*ignore_unknown_fields=*/true));

  for (openconfig::Qos::BufferAllocationProfile &buffer_profile :
       *proto_config.mutable_buffer_allocation_profiles()
            ->mutable_buffer_allocation_profile()) {
    if (buffer_profile.name() == buffer_allocation_profile) {
      for (openconfig::Qos::Queue &queue :
           *buffer_profile.mutable_queues()->mutable_queue()) {
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
      }
    }
  }

  proto_config.clear_scheduler_policies();
  // Convert proto back to JSON string.
  ASSIGN_OR_RETURN(std::string qos_json,
                   gutil::SerializeProtoAsJson(proto_config));
  RETURN_IF_ERROR(SetGnmiConfigPath(
      &gnmi, "qos", GnmiSetType::kUpdate,
      absl::StrFormat(R"({ "openconfig-qos:qos": %s })", qos_json)));

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

absl::Status DisablePuntRateLimits(gnmi::gNMI::StubInterface &gnmi_stub) {
  // Effectively Disabling punt rate limiting on both control switch and SUT
  // by setting both committed and peak information rate to 1 million pkt/s and
  // both committed and excess burst rate to 1'000 pkts.
  constexpr int64_t k1Million = 1'000'000;
  constexpr int64_t k1Thousand = 1'000;
  SchedulerParameters scheduler_params = SchedulerParameters{
      .committed_information_rate = k1Million,
      .committed_burst_size = k1Thousand,
      .peak_information_rate = k1Million,
      .excess_burst_size = k1Thousand,
  };
  RETURN_IF_ERROR(ReplaceCpuSchedulerPolicyParametersForAllQueues(
      gnmi_stub, scheduler_params));
  return absl::OkStatus();
}

absl::Status UpdateBufferAllocationForAllCpuQueues(
    gnmi::gNMI::StubInterface &gnmi_stub, int buffer_size) {
  absl::flat_hash_map<std::string, BufferParameters>
      buffer_config_by_queue_name;
  ASSIGN_OR_RETURN(std::vector<std::string> queues,
                   GetQueuesByEgressPort("CPU", gnmi_stub));
  for (absl::string_view queue_name : queues) {
    buffer_config_by_queue_name[queue_name] = BufferParameters{
        .dedicated_buffer = 0,
        .use_shared_buffer = true,
        .shared_buffer_limit_type = "openconfig-qos:STATIC",
        .dynamic_limit_scaling_factor = 0,
        .shared_static_limit = buffer_size,
    };
  }
  ASSIGN_OR_RETURN(const std::string buffer_profile_name,
                   GetBufferAllocationProfileByEgressPort("CPU", gnmi_stub));
  RETURN_IF_ERROR(SetBufferConfigParameters(
      buffer_profile_name, buffer_config_by_queue_name, gnmi_stub));
  return absl::OkStatus();
}

absl::Status EffectivelyDisablePuntLimitsForSwitch(
    SwitchRoleToDisablePuntFlowQoS role, thinkit::MirrorTestbed &testbed) {
  std::unique_ptr<gnmi::gNMI::StubInterface> gnmi_stub;
  switch (role) {
    case SwitchRoleToDisablePuntFlowQoS::kSwitchUnderTest: {
      ASSIGN_OR_RETURN(gnmi_stub, testbed.Sut().CreateGnmiStub());
      break;
    }
    case SwitchRoleToDisablePuntFlowQoS::kControlSwitch: {
      ASSIGN_OR_RETURN(gnmi_stub, testbed.ControlSwitch().CreateGnmiStub());
      break;
    }
  }
  std::string switch_role_name = SwitchRoleToDisableQoSToString(role);

  ASSIGN_OR_RETURN(auto gnmi_config_before_qos_and_buffer_change,
                   pins_test::GetGnmiConfig(*gnmi_stub));
  RETURN_IF_ERROR(testbed.Environment().StoreTestArtifact(
      absl::StrCat(switch_role_name,
                   "_gnmi_config_before_qos_and_buffer_change.pb.txt"),
      gnmi_config_before_qos_and_buffer_change));
  RETURN_IF_ERROR(pins_test::DisablePuntRateLimits(*gnmi_stub));
  LOG(INFO) << "Disabling punt rate limits complete for " << switch_role_name;

  // The default buffer size for CPU on most switches is 18'432. We use 4x of
  // the current value to prevent packet loss.
  constexpr int kBufferSizeForCpuInBype = 18432 * 4;
  RETURN_IF_ERROR(pins_test::UpdateBufferAllocationForAllCpuQueues(
      *gnmi_stub, kBufferSizeForCpuInBype));

  LOG(INFO) << "Update buffer allocation for all CPU queues complete for "
            << switch_role_name << ". All CPU queues now have "
            << kBufferSizeForCpuInBype << " bytes for their buffers.";

  ASSIGN_OR_RETURN(auto gnmi_config_after_qos_and_buffer_change,
                   pins_test::GetGnmiConfig(*gnmi_stub));
  RETURN_IF_ERROR(testbed.Environment().StoreTestArtifact(
      absl::StrCat(switch_role_name,
                   "_gnmi_config_after_qos_and_buffer_change.pb.txt"),
      gnmi_config_after_qos_and_buffer_change));
  return absl::OkStatus();
}

absl::StatusOr<int64_t> GetGnmiPortEcnCounter(
    absl::string_view port, gnmi::gNMI::StubInterface &gnmi_stub) {
  const std::string openconfig_transmit_count_state_path = absl::Substitute(
      "interfaces/interface[name=$0]"
      "/state/counters/out-ecn-marked-pkts",
      port);

  ASSIGN_OR_RETURN(
      std::string ecn_counter_response,
      GetGnmiStatePathInfo(&gnmi_stub, openconfig_transmit_count_state_path,
                           "interfaces:out-ecn-marked-pkts"));

  int64_t ecn_counters;
  if (!absl::SimpleAtoi(StripQuotes(ecn_counter_response), &ecn_counters)) {
    return gutil::UnknownErrorBuilder()
           << "Unable to parse counter from response: \""
           << ecn_counter_response << "\"";
  }
  return ecn_counters;
}

absl::StatusOr<int64_t> GetGnmiPortIngressCounter(
    absl::string_view port, gnmi::gNMI::StubInterface &gnmi_stub) {
  const std::string openconfig_transmit_count_state_path = absl::Substitute(
      "interfaces/interface[name=$0]"
      "/state/counters/in-pkts",
      port);

  ASSIGN_OR_RETURN(
      std::string ingress_counter_response,
      GetGnmiStatePathInfo(&gnmi_stub, openconfig_transmit_count_state_path,
                           "openconfig-interfaces:in-pkts"));

  int64_t ingress_counter;
  if (!absl::SimpleAtoi(StripQuotes(ingress_counter_response),
                        &ingress_counter)) {
    return gutil::UnknownErrorBuilder()
           << "Unable to parse counter from response: \""
           << ingress_counter_response << "\"";
  }
  return ingress_counter;
}

// Extract the queue configurations from the gNMI configuration.
// The function returns a map keyed on queue name and value
// holds queue configuration information.
// TODO: Need to handle exceptions cleanly for failures
// during json parsing which can crash the test run.
// Currently we are assuming validity of config json parameter passed into
// the test.
absl::StatusOr<absl::flat_hash_map<std::string, QueueInfoByQueueName>>
ExtractQueueInfoViaGnmiConfig(absl::string_view port,
                              absl::string_view gnmi_config,
                              bool is_rate_mode_in_packets) {
  nlohmann::json config = nlohmann::json::parse(gnmi_config);
  if (!config.is_object()) {
    return absl::InvalidArgumentError("Could not parse gnmi configuration.");
  }

  absl::flat_hash_map<std::string, QueueInfoByQueueName> queue_info;
  auto &qos_interfaces =
      config["openconfig-qos:qos"]["interfaces"]["interface"];

  std::string scheduler_policy;
  for (auto &interface : qos_interfaces) {
    if (interface["interface-id"].get<std::string>() == port) {
      scheduler_policy =
          interface["output"]["scheduler-policy"]["config"]["name"]
              .get<std::string>();
      break;
    }
  }

  auto &scheduler_policies =
      config["openconfig-qos:qos"]["scheduler-policies"]["scheduler-policy"];
  for (auto &policy : scheduler_policies) {
    if (policy["name"].get<std::string>() == scheduler_policy) {
      for (auto &scheduler : policy["schedulers"]["scheduler"]) {
        std::string queue_name =
            scheduler["inputs"]["input"][0]["config"]["queue"]
                .get<std::string>();
        queue_info[queue_name].gnmi_queue_name = queue_name;
        queue_info[queue_name].p4_queue_name = queue_name;
        std::string peak_rate =
            scheduler["two-rate-three-color"]["config"]
                     [is_rate_mode_in_packets ? "qos:pir-pkts"
                                              : "pir"]
                         .get<std::string>();
        if (!absl::SimpleAtoi(
                peak_rate, &queue_info[queue_name].rate_packets_per_second)) {
          return absl::InternalError(
              absl::StrCat("Unable to parse rate as int ", peak_rate,
                           " for queue ", queue_name));
        }
        LOG(INFO) << "Queue: " << queue_name
                  << ", configured rate:" << peak_rate;
        int be_pkts =
            scheduler["two-rate-three-color"]["config"]
                     [is_rate_mode_in_packets ? "qos:be-pkts"
                                              : "be"]
                         .get<int>();
        queue_info[queue_name].scheduler_be_pkts = be_pkts;
      }
      break;
    }
  }

  std::string buffer_allocation_profile;
  for (auto &interface : qos_interfaces) {
    if (interface["interface-id"].get<std::string>() == "CPU") {
      buffer_allocation_profile =
          interface["output"]["config"]["buffer-allocation-profile"]
              .get<std::string>();
      break;
    }
  }

  auto &buffer_allocation_profiles =
      config["openconfig-qos:qos"]["buffer-allocation-profiles"]
            ["buffer-allocation-profile"];
  for (auto &profile : buffer_allocation_profiles) {
    if (profile["name"].get<std::string>() == buffer_allocation_profile) {
      for (auto &queue : profile["queues"]["queue"]) {
        std::string queue_name = queue["name"].get<std::string>();
        double buffer_limit =
            queue["config"]["static-shared-buffer-limit"].get<double>();
        queue_info[queue_name].shared_buffer_static_limit = buffer_limit;
      }
      break;
    }
  }

  return queue_info;
}

absl::StatusOr<absl::flat_hash_set<std::string>> ExtractCPUQueuesViaGnmiConfig(
    absl::string_view gnmi_config) {
  nlohmann::json config = nlohmann::json::parse(gnmi_config);
  if (!config.is_object()) {
    return absl::InvalidArgumentError("Could not parse gnmi configuration.");
  }

  absl::flat_hash_set<std::string> queues;
  auto &qos_interfaces =
      config["openconfig-qos:qos"]["interfaces"]["interface"];

  std::string cpu_scheduler_policy;
  for (auto &interface : qos_interfaces) {
    if (interface["interface-id"].get<std::string>() == "CPU") {
      cpu_scheduler_policy =
          interface["output"]["scheduler-policy"]["config"]["name"]
              .get<std::string>();
      break;
    }
  }

  auto &scheduler_policies =
      config["openconfig-qos:qos"]["scheduler-policies"]["scheduler-policy"];
  for (auto &policy : scheduler_policies) {
    if (policy["name"].get<std::string>() == cpu_scheduler_policy) {
      for (auto &scheduler : policy["schedulers"]["scheduler"]) {
        std::string queue_name =
            scheduler["inputs"]["input"][0]["config"]["queue"]
                .get<std::string>();
        queues.insert(queue_name);
      }
      break;
    }
  }
  return queues;
}

}  // namespace pins_test
