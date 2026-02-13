/*
 * Copyright 2025 Google LLC
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
#include "p4rt_app/p4runtime/queue_translator.h"

#include <memory>
#include <string>

#include "absl/status/statusor.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/string_view.h"
#include "gutil/collections.h"
#include "gutil/status.h"

namespace p4rt_app {

absl::StatusOr<std::unique_ptr<QueueTranslator>> QueueTranslator::Create(
    const std::vector<std::pair<std::string, std::string>>& name_id_pairs) {
  std::unique_ptr<QueueTranslator> translator = Empty();
  for (const auto& [name, id_string] : name_id_pairs) {
    int id;
    if (!absl::SimpleAtoi(id_string, &id)) {
      return gutil::InvalidArgumentErrorBuilder()
             << "Non-integer ID for Queue Name/ID pair: [" << name << " : "
             << id_string << "]";
    }
    if (!translator->name_to_id_.insert_or_assign(name, id).second) {
      return gutil::InvalidArgumentErrorBuilder()
             << "Duplicate IDs found for Queue Name '" << name << "'";
    }
    if (!translator->id_to_name_.insert_or_assign(id, name).second) {
      return gutil::InvalidArgumentErrorBuilder()
             << "Duplicate Names found for Queue ID '" << id << "'";
    }
  }
  return translator;
}

absl::StatusOr<std::string> QueueTranslator::IdToName(int queue_id) const {
  return gutil::FindOrStatus(id_to_name_, queue_id);
}

absl::StatusOr<int> QueueTranslator::NameToId(
    absl::string_view queue_name) const {
  return gutil::FindOrStatus(name_to_id_, queue_name);
}

absl::StatusOr<std::string> QueueTranslator::OptionallyTranslateIdToName(
    absl::string_view value) const {
  int queue_id;
  if (!absl::SimpleHexAtoi(value, &queue_id)) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Expected AppDB queue as hex string. Got '" << value << "'.";
  }
  absl::StatusOr<std::string> queue_name = IdToName(queue_id);
  return queue_name.ok() ? queue_name.value() : std::string(value);
}

std::string QueueTranslator::OptionallyTranslateNameToIdInHexString(
    absl::string_view value) const {
  absl::StatusOr<int> queue_id = NameToId(value);
  if (queue_id.ok()) {
    return absl::StrFormat("%#x", *queue_id);
  }
  if (int queue_num = 0; absl::SimpleAtoi(value, &queue_num) ||
                         absl::SimpleHexAtoi(value, &queue_num)) {
    // If the value is a number, format it as hex.
    return absl::StrFormat("%#x", queue_num);
  }
  return std::string(value);
}

std::string QueueTranslator::DumpDebugData() const {
  std::string rv;
  for (const auto& [name, id] : name_to_id_) {
    absl::StrAppend(&rv, name, " : ", id, "\n");
  }
  return rv;
}

}  // namespace p4rt_app
