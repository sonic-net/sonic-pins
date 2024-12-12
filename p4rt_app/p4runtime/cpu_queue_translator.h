/*
 * Copyright 2024 Google LLC
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
#ifndef PINS_P4RT_APP_P4RUNTIME_CPU_QUEUE_TRANSLATOR_H_
#define PINS_P4RT_APP_P4RUNTIME_CPU_QUEUE_TRANSLATOR_H_

#include <memory>
#include <string>

#include "absl/container/flat_hash_map.h"
#include "absl/memory/memory.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
namespace p4rt_app {

// CpuQueueTranslator is an immutable bidirectional map that translates between
// CPU queue name (string) and ID (int).
class CpuQueueTranslator {
public:
  // Create a translator for the provided name and ID pairs.
  static absl::StatusOr<std::unique_ptr<CpuQueueTranslator>>
  Create(const std::vector<std::pair<std::string, std::string>> &name_id_pairs);

  // Create an empty translator. All translations will fail.
  static std::unique_ptr<CpuQueueTranslator> Empty() {
    return absl::WrapUnique(new CpuQueueTranslator());
  }

  ~CpuQueueTranslator() = default;

  // Perform a translation between queue name and id.
  absl::StatusOr<std::string> IdToName(int queue_id) const;
  absl::StatusOr<int> NameToId(absl::string_view queue_name) const;

protected:
  CpuQueueTranslator() = default;

private:
  absl::flat_hash_map<int, std::string> id_to_name_;
  absl::flat_hash_map<std::string, int> name_to_id_;
};

} // namespace p4rt_app

#endif // PINS_P4RT_APP_P4RUNTIME_CPU_QUEUE_TRANSLATOR_H_
