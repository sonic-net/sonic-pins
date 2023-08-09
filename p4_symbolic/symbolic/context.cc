// Copyright 2024 Google LLC
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

#include "p4_symbolic/symbolic/context.h"

#include <string>

#include "absl/strings/str_cat.h"

namespace p4_symbolic {
namespace symbolic {

std::string ConcreteTableMatch::to_string() const {
  if (!matched) {
    return "was not matched!";
  }
  return absl::StrCat("was matched on entry ", entry_index);
}

std::string ConcreteTrace::to_string() const {
  std::string result;
  absl::StrAppend(&result, "dropped = ", dropped, "\n");
  absl::StrAppend(&result, "got cloned = ", got_cloned);
  for (const auto &[table, match] : matched_entries) {
    absl::StrAppend(&result, "\n", table, " => ", match.to_string());
  }
  return result;
}

std::string ConcreteContext::to_string(bool verbose) const {
  auto result = absl::StrCat("ingress_port = ", ingress_port, "\n",
                             "egress_port = ", egress_port, "\n", "trace:\n",
                             trace.to_string());
  if (verbose) {
    auto ingress_string = absl::StrCat("ingress_headers", ":");
    auto parsed_string = absl::StrCat("parsed_headers", ":");
    auto egress_string = absl::StrCat("egress_headers", ":");
    for (const auto &[name, ingress_value] : ingress_headers) {
      absl::StrAppend(&ingress_string, "\n", name, " = ", ingress_value);
    }
    for (const auto &[name, parsed_value] : parsed_headers) {
      absl::StrAppend(&parsed_string, "\n", name, " = ", parsed_value);
    }
    for (const auto &[name, egress_value] : egress_headers) {
      absl::StrAppend(&egress_string, "\n", name, " = ", egress_value);
    }
    absl::StrAppend(&result, "\n\n", ingress_string, "\n\n", parsed_string,
                    "\n\n", egress_string);
  }
  return result;
}

}  // namespace symbolic
}  // namespace p4_symbolic
