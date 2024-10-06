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

// This file exposes the SAI header/metadata fields as Z3 expressions, making it
// easy to formulate constraints on these fields.

#ifndef PINS_P4_SYMBOLIC_SAI_FIELDS_H_
#define PINS_P4_SYMBOLIC_SAI_FIELDS_H_

#include "p4_symbolic/symbolic/symbolic.h"
#include "z3++.h"

namespace p4_symbolic {

// Symbolic version of `struct ethernet_t` in headers.p4.
struct SaiEthernet {
  z3::expr valid;
  z3::expr dst_addr;
  z3::expr src_addr;
  z3::expr ether_type;
};

// Symbolic version of `struct ipv4_t` in headers.p4.
struct SaiIpv4 {
  z3::expr valid;
  z3::expr version;
  z3::expr ihl;
  z3::expr dscp;
  z3::expr ecn;
  z3::expr total_len;
  z3::expr identification;
  z3::expr reserved;
  z3::expr do_not_fragment;
  z3::expr more_fragments;
  z3::expr frag_offset;
  z3::expr ttl;
  z3::expr protocol;
  z3::expr header_checksum;
  z3::expr src_addr;
  z3::expr dst_addr;
};

// Symbolic version of `struct headers_t` in metadata.p4.
struct SaiHeaders {
  SaiEthernet ethernet;
  SaiIpv4 ipv4;
};

// Symbolic version of `struct local_metadata_t` in metadata.p4.
struct SaiLocalMetadata {
  z3::expr admit_to_l3;
  z3::expr vrf_id;
  // TODO: add `packet_rewrites` fields.
  z3::expr mirror_session_id_valid;
  // TODO: add `mirror*` fields.
  // TODO: Add `color` field.
};

struct SaiFields {
  SaiHeaders headers;
  SaiLocalMetadata local_metadata;
};

absl::StatusOr<SaiFields> GetSaiFields(
    const symbolic::SymbolicPerPacketState& state);

}  // namespace p4_symbolic

#endif  // PINS_P4_SYMBOLIC_SAI_FIELDS_H_
