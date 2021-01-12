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

// This file defines the API for transforming a bmv2 protobuf (representing
// the input bmv2 json file) together with a pdpi protobuf (representing the
// p4info file) into our IR protobuf for consumption.

#ifndef P4_SYMBOLIC_IR_IR_H_
#define P4_SYMBOLIC_IR_IR_H_

#include "gutil/status.h"
#include "p4_symbolic/bmv2/bmv2.pb.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/ir/table_entries.h"

namespace p4_symbolic {
namespace ir {

// Transforms bmv2 protobuf and pdpi protobuf into our IR protobuf.
absl::StatusOr<P4Program> Bmv2AndP4infoToIr(const bmv2::P4Program& bmv2,
                                            const pdpi::IrP4Info& pdpi);

}  // namespace ir
}  // namespace p4_symbolic

#endif  // P4_SYMBOLIC_IR_IR_H_
