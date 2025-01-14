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

#ifndef P4_SYMBOLIC_SYMBOLIC_V1MODEL_INTRINSIC_H_
#define P4_SYMBOLIC_SYMBOLIC_V1MODEL_INTRINSIC_H_

namespace p4_symbolic::symbolic::v1model {

// Possible values of the v1model `standard_metadata_t` field `instance_type` in
// BMv2. The semantics of these values is explained here:
// https://github.com/p4lang/behavioral-model/blob/main/docs/simple_switch.md
#define PKT_INSTANCE_TYPE_NORMAL 0
#define PKT_INSTANCE_TYPE_INGRESS_CLONE 1
#define PKT_INSTANCE_TYPE_EGRESS_CLONE 2
#define PKT_INSTANCE_TYPE_COALESCED 3
#define PKT_INSTANCE_TYPE_INGRESS_RECIRC 4
#define PKT_INSTANCE_TYPE_REPLICATION 5
#define PKT_INSTANCE_TYPE_RESUBMIT 6

}  // namespace p4_symbolic::symbolic::v1model

#endif  // PINS_P4_SYMBOLIC_SYMBOLIC_V1MODEL_INTRINSIC_H_
