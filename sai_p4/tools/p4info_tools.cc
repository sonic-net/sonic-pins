// Copyright 2021 Google LLC
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

#include "sai_p4/tools/p4info_tools.h"

#include <string>
#include <vector>

#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_pdpi/utils/annotation_parser.h"

namespace sai {

bool SetSaiHashSeed(p4::config::v1::P4Info& p4info, uint32_t seed) {
  bool set_any_hash = false;
  for (auto& action : *p4info.mutable_actions()) {
    for (auto& annotation : *action.mutable_preamble()->mutable_annotations()) {
      absl::StatusOr<std::string> result = pdpi::GetAnnotationBody(
          "sai_hash_seed", std::vector<std::string>({annotation}));
      if (result.ok() && *result == "0") {
        annotation.assign(absl::StrCat("@sai_hash_seed(", seed, ")"));
        set_any_hash = true;
      }
    }
  }
  return set_any_hash;
}

}  // namespace sai
