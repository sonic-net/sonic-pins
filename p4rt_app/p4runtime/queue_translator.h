/*
 * Copyright 2023 Google LLC
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
#ifndef PINS_P4RT_APP_P4RUNTIME_QUEUE_TRANSLATOR_H_
#define PINS_P4RT_APP_P4RUNTIME_QUEUE_TRANSLATOR_H_

#include <memory>
#include <string>

#include "absl/container/flat_hash_map.h"
#include "absl/memory/memory.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
namespace p4rt_app {

// QueueTranslator is an immutable bidirectional map that translates between
// a queue name (string) and ID (int).
class QueueTranslator {
 public:
  // Create a translator for the provided name and ID pairs.
  static absl::StatusOr<std::unique_ptr<QueueTranslator>> Create(
      const std::vector<std::pair<std::string, std::string>>& name_id_pairs);

  // Create an empty translator. All translations will fail.
  static std::unique_ptr<QueueTranslator> Empty() {
    return absl::WrapUnique(new QueueTranslator());
  }

  std::string DumpDebugData() const;

  ~QueueTranslator() = default;

  // Perform a translation between queue name and id.
  absl::StatusOr<std::string> IdToName(int queue_id) const;
  absl::StatusOr<int> NameToId(absl::string_view queue_name) const;

  // Perform a translation from queue id to name if id is found in id_to_name_
  // map, or return the queue id if value is already a number. Return invalid
  // argument error if the value is not a number.
  absl::StatusOr<std::string> OptionallyTranslateIdToName(
      absl::string_view value) const;
  // Perform a translation from queue name to id in hex string format if name is
  // found in name_to_id_ map or if the queue name is a number.
  std::string OptionallyTranslateNameToIdInHexString(
      absl::string_view value) const;

 protected:
  QueueTranslator() = default;

 private:
  absl::flat_hash_map<int, std::string> id_to_name_;
  absl::flat_hash_map<std::string, int> name_to_id_;
};

}  // namespace p4rt_app

#endif  // PINS_P4RT_APP_P4RUNTIME_QUEUE_TRANSLATOR_H_
