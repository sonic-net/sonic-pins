// Copyright 2020 Google LLC
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
#include "p4rt_app/tests/lib//app_db_entry_builder.h"

#include <iterator>
#include <optional>
#include <string>
#include <unordered_map>
#include <vector>

#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_join.h"

namespace p4rt_app {
namespace test_lib {

AppDbEntryBuilder& AppDbEntryBuilder::SetTableName(
    const std::string& table_name) {
  table_name_ = table_name;
  return *this;
}

AppDbEntryBuilder& AppDbEntryBuilder::SetAction(const std::string& action) {
  action_ = action;
  return *this;
}

AppDbEntryBuilder& AppDbEntryBuilder::SetPriority(int value) {
  priority_ = absl::StrFormat(R"("priority":%d)", value);
  return *this;
}

AppDbEntryBuilder& AppDbEntryBuilder::AddMatchField(const std::string& key,
                                                    const std::string& value) {
  match_fields_.push_back(absl::StrFormat(R"("match/%s":"%s")", key, value));
  return *this;
}

AppDbEntryBuilder& AppDbEntryBuilder::AddActionParam(const std::string& param,
                                                     const std::string& value) {
  action_params_.push_back(
      std::make_pair(absl::StrCat("param/", param), value));
  return *this;
}

std::string AppDbEntryBuilder::GetKey() const {
  std::vector<std::string> all_match_fields = match_fields_;
  if (priority_.has_value()) {
    all_match_fields.push_back(*priority_);
  }
  return absl::StrFormat("%s:{%s}", table_name_,
                         absl::StrJoin(all_match_fields, ","));
}

std::vector<std::pair<std::string, std::string>>
AppDbEntryBuilder::GetValueList() const {
  std::vector<std::pair<std::string, std::string>> result = {
      std::make_pair("action", action_)};
  result.insert(result.end(), action_params_.begin(), action_params_.end());
  return result;
}

std::unordered_map<std::string, std::string> AppDbEntryBuilder::GetValueMap()
    const {
  std::unordered_map<std::string, std::string> result;
  result["action"] = action_;
  std::copy(action_params_.begin(), action_params_.end(),
            std::inserter(result, result.begin()));
  return result;
}

}  // namespace test_lib
}  // namespace p4rt_app
