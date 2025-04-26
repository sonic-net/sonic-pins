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

#include "p4rt_app/p4runtime/p4info_reconcile.h"

#include <string>
#include <vector>

#include "absl/container/btree_set.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "gutil/status.h"
#include "p4_pdpi/ir.pb.h"
#include "p4rt_app/sonic/hashing.h"

namespace p4rt_app {
namespace {

template <typename T>
struct SetDifference {
  std::vector<T> deleted;
  std::vector<T> added;
  std::vector<T> intersection;
};

template <typename T>
SetDifference<T> CalculateSetDifference(const absl::btree_set<T>& from,
                                        const absl::btree_set<T>& to) {
  SetDifference<T> difference;
  auto from_iter = from.begin();
  auto to_iter = to.begin();
  while (from_iter != from.end() && to_iter != to.end()) {
    if (*from_iter == *to_iter) {
      difference.intersection.push_back(*from_iter);
      ++from_iter;
      ++to_iter;
    } else if (*from_iter < *to_iter) {
      difference.deleted.push_back(*from_iter);
      ++from_iter;
    } else {  // *from_iter > *to_iter
      difference.added.push_back(*to_iter);
      ++to_iter;
    }
  }
  while (from_iter != from.end()) {
    difference.deleted.push_back(*from_iter);
    ++from_iter;
  }
  while (to_iter != to.end()) {
    difference.added.push_back(*to_iter);
    ++to_iter;
  }
  return difference;
}

absl::Status CalculateHashingDifference(const pdpi::IrP4Info& from,
                                        const pdpi::IrP4Info& to,
                                        P4InfoReconcileTransition& transition) {
  auto from_hash_packet_fields = sonic::ExtractHashPacketFieldConfigs(from);
  if (!from_hash_packet_fields.ok()) {
    return gutil::InternalErrorBuilder()
           << "Failed to calculate hash packets fields from existing P4Info: "
           << from_hash_packet_fields.status().message();
  }
  auto from_hash_parameters = sonic::ExtractHashParamConfigs(from);
  if (!from_hash_parameters.ok()) {
    return gutil::InternalErrorBuilder()
           << "Failed to calculate hash parameter fields from existing P4Info: "
           << from_hash_parameters.status().message();
  }

  ASSIGN_OR_RETURN(auto to_hash_packet_fields,
                   sonic::ExtractHashPacketFieldConfigs(to),
                   _.SetPrepend() << "Failed to calculate hash packet fields "
                                  << "from new forwarding pipeline config. ");
  ASSIGN_OR_RETURN(auto to_hash_parameters, sonic::ExtractHashParamConfigs(to),
                   _.SetPrepend() << "failed to calculate hash parameters from "
                                  << "new forwarding pipeline config. ");

  // calculate packet field config diffs.
  SetDifference packet_field_diff =
      CalculateSetDifference(*from_hash_packet_fields, to_hash_packet_fields);
  absl::btree_set<std::string> to_packet_field_keys;
  for (const sonic::HashPacketFieldConfig& config : to_hash_packet_fields) {
    to_packet_field_keys.insert(to_packet_field_keys.end(), config.key);
  }
  for (const sonic::HashPacketFieldConfig& config : packet_field_diff.deleted) {
    // Skip delete of keys that we will replace.
    if (!to_packet_field_keys.contains(config.key)) {
      transition.hashing_packet_field_configs_to_delete.push_back(config.key);
    }
  }
  for (const sonic::HashPacketFieldConfig& config : packet_field_diff.added) {
    transition.hashing_packet_field_configs_to_set.push_back(config.key);
  }

  // Calculate whether the switch table is different.
  transition.update_switch_table =
      !transition.hashing_packet_field_configs_to_delete.empty() ||
      !transition.hashing_packet_field_configs_to_set.empty() ||
      *from_hash_parameters != to_hash_parameters;

  return absl::OkStatus();
}

}  // namespace

absl::StatusOr<P4InfoReconcileTransition> CalculateTransition(
    const pdpi::IrP4Info& from, const pdpi::IrP4Info& to) {
  P4InfoReconcileTransition transition;
  RETURN_IF_ERROR(CalculateHashingDifference(from, to, transition));
  return transition;
}

}  // namespace p4rt_app
