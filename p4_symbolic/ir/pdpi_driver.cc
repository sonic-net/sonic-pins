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

#include "p4_symbolic/ir/pdpi_driver.h"

#include <memory>

#include "gutil/proto.h"
#include "p4_pdpi/ir.h"

namespace p4_symbolic {
namespace ir {

absl::StatusOr<pdpi::IrP4Info> ParseP4InfoFile(const std::string &p4info_path) {
  p4::config::v1::P4Info p4info;
  RETURN_IF_ERROR(gutil::ReadProtoFromFile(p4info_path.c_str(), &p4info));
  return pdpi::CreateIrP4Info(p4info);
}

}  // namespace ir
}  // namespace p4_symbolic
