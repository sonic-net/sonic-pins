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
#ifndef PINS_P4RT_APP_TESTS_LIB_APP_DB_ENTRY_BUILDER_H_
#define PINS_P4RT_APP_TESTS_LIB_APP_DB_ENTRY_BUILDER_H_

#include <string>
#include <unordered_map>
#include <vector>

#include "absl/types/optional.h"

namespace p4rt_app {
namespace test_lib {

// The AppDbEntryBuilder is intended to be used by unit tests for representing
// AppDb entries. The P4RT AppDb keys can be long strings with many quotation
// mark characters, and this can make using string literals difficult to read.
//
// For example the following string literals:
//   "FIXED_TABLE:{\"match/field1\":\"123\",\"match/field2\":\"abc\"}"
//     or
//   R"(FIXED_TABLE:{"match/field1":"123","match/field2":"abc"})"
//
// Can be built with:
//   AppDbEntryBuilder{}
//       .SetTableName("FIXED_TABLE")
//       .AddMatchField("field1", "123")
//       .AddMatchField("field2", "abc");
class AppDbEntryBuilder {
 public:
  AppDbEntryBuilder& SetTableName(const std::string& table_name);
  AppDbEntryBuilder& SetAction(const std::string& action);
  AppDbEntryBuilder& SetPriority(int value);
  AppDbEntryBuilder& AddMatchField(const std::string& key,
                                   const std::string& value);
  AppDbEntryBuilder& AddActionParam(const std::string& param,
                                    const std::string& value);

  // Returns an AppDb entry key formatted as:
  //   <table_name>:{<match_0>,<match_1>,...,<match_N>}
  std::string GetKey() const;

  // Returns the AppDb values with the action name included.
  std::vector<std::pair<std::string, std::string>> GetValueList() const;
  std::unordered_map<std::string, std::string> GetValueMap() const;

 private:
  // The table name is always used when generating the AppDb key. If no value is
  // explicitly set an empty string will be used instead.
  std::string table_name_;

  // The action name is always used when generating the AppDb values. If no
  // value is explicitly set an empty action name will be used instead.
  std::string action_;

  // A match field priority can be explicitly set. It will appear as part of the
  // AppDb key only if it is set.
  absl::optional<std::string> priority_;

  // List of all match fields.
  //
  // The P4RT match fields are typically ordered alphabetically because we use
  // the nlohmann JSON library. The AppDbEntryBuilder will use the order objects
  // are added by the user.
  //
  // Values are automatically prefixed with "match/" by the AppDbEntryBuilder.
  std::vector<std::string> match_fields_;

  // List of all action parameters.
  //
  // Values are prefixed with "param/" by the AppDbEntryBuilder.
  std::vector<std::pair<std::string, std::string>> action_params_;
};

}  // namespace test_lib
}  // namespace p4rt_app

#endif  // PINS_P4RT_APP_TESTS_LIB_APP_DB_ENTRY_BUILDER_H_
