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

#include "absl/status/statusor.h"
#include "absl/strings/numbers.h"
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

}  // namespace p4rt_app
