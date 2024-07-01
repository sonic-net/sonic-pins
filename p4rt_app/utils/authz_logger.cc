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
#include "p4rt_app/utils/authz_logger.h"

#include <algorithm>
#include <string>
#include <vector>

#include "absl/strings/str_split.h"
#include "glog/logging.h"

namespace p4rt_app {

void AuthzLogger::Log(const grpc::experimental::AuditContext& context) {
  if (!context.authorized()) {
    LOG(WARNING) << "User '" << context.principal()
                 << "' does not have permission to execute RPC "
                 << context.rpc_method();
  }
  // The full RPC method name will look like "/service/rpc_method".
  std::vector<absl::string_view> rpc_tokens =
      absl::StrSplit(context.rpc_method(), '/', absl::SkipEmpty());
  if (rpc_tokens.size() != 2 || context.rpc_method()[0] != '/') {
    LOG(ERROR) << "Invalid RPC method " << context.rpc_method();
    return;
  }
  recorder_->RecordAuthz(context.authorized(),
                         /*service=*/rpc_tokens[0],
                         /*rpc=*/rpc_tokens[1]);
}

}  // namespace p4rt_app
