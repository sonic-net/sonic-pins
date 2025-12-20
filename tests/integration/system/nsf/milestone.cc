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

#include "tests/integration/system/nsf/milestone.h"

#include <string>
#include <tuple>
#include <vector>

#include "absl/log/log.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"

namespace pins_test {

namespace {

std::vector<std::tuple<NsfMilestone, std::string>> MilestoneToStringMapping() {
  return {
      {NsfMilestone::kAll, "all"},
      {NsfMilestone::kShutdown, "shutdown"},
      {NsfMilestone::kBootup, "bootup"},
  };
}

}  // namespace

bool AbslParseFlag(absl::string_view milestone_text, NsfMilestone* milestone,
                   std::string* error) {
  for (auto& [milestone_, string] : MilestoneToStringMapping()) {
    if (string == milestone_text) {
      *milestone = milestone_;
      return true;
    }
  }
  absl::StrAppend(error, "unknown milestone: '", milestone_text, "'");
  return false;
}

std::string AbslUnparseFlag(NsfMilestone milestone) {
  for (auto& [milestone_, string] : MilestoneToStringMapping()) {
    if (milestone_ == milestone) return string;
  }
  LOG(DFATAL) << "invalid milestone: " << static_cast<int>(milestone);
  return "<invalid_milestone>";
}

}  // namespace pins_test
