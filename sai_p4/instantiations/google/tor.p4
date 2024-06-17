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
#define SAI_INSTANTIATION_TOR

#include <v1model.p4>

// These headers have to come first, to override their fixed counterparts.
#include "roles.h"
#include "bitwidths.p4"
#include "minimum_guaranteed_sizes.p4"

#include "../../fixed/packet_io.p4"
#include "../../fixed/headers.p4"
#include "../../fixed/metadata.p4"
#include "../../fixed/parser.p4"
#include "../../fixed/packet_io.p4"
#include "../../fixed/routing.p4"
#include "../../fixed/ipv4_checksum.p4"
#include "../../fixed/mirroring_encap.p4"
#include "../../fixed/mirroring_clone.p4"
#include "../../fixed/l3_admit.p4"
#include "../../fixed/vlan.p4"
#include "../../fixed/ttl.p4"
#include "../../fixed/drop_martians.p4"
#include "../../fixed/packet_rewrites.p4"
#include "acl_egress.p4"
#include "acl_egress_dhcp_to_host.p4"
#include "acl_ingress.p4"
#include "acl_ingress_qos.p4"
#include "acl_pre_ingress.p4"
#include "acl_pre_ingress_metadata.p4"
#include "acl_pre_ingress_vlan.p4"
#include "admit_google_system_mac.p4"
//#include "hashing.p4"
#include "ids.h"
#include "versions.h"

control ingress(inout headers_t headers,
                inout local_metadata_t local_metadata,
                inout standard_metadata_t standard_metadata) {
  apply {
    packet_out_decap.apply(headers, local_metadata, standard_metadata);
    if (!local_metadata.bypass_ingress) {
      // The PRE_INGRESS stage handles VRF and VLAN assignment. We can also set
      // the pre-ingress metadata for certain types of traffic we want to handle
      // uniquely in later stages.
      vlan_untag.apply(headers, local_metadata, standard_metadata);
      acl_pre_ingress_vlan.apply(headers, local_metadata, standard_metadata);
      acl_pre_ingress_metadata.apply(
          headers, local_metadata, standard_metadata);
      acl_pre_ingress.apply(headers, local_metadata, standard_metadata);

      // Standard L3 pipeline for routing packets.
      admit_google_system_mac.apply(headers, local_metadata);
      l3_admit.apply(headers, local_metadata, standard_metadata);
//    hashing.apply(headers, local_metadata, standard_metadata);
      routing.apply(headers, local_metadata, standard_metadata);
      drop_martians.apply(headers, local_metadata, standard_metadata);

      // The INGRESS stage can redirect (e.g. drop, punt or copy) packets, apply
      // rate-limits or modify header data.
      acl_ingress.apply(headers, local_metadata, standard_metadata);
      acl_ingress_qos.apply(headers, local_metadata, standard_metadata);
      ttl.apply(headers, local_metadata, standard_metadata);
      mirroring_clone.apply(headers, local_metadata, standard_metadata);
    }
  }
}  // control ingress

control egress(inout headers_t headers,
               inout local_metadata_t local_metadata,
               inout standard_metadata_t standard_metadata) {
  apply {
    packet_rewrites.apply(headers, local_metadata, standard_metadata);
    mirroring_encap.apply(headers, local_metadata, standard_metadata);
    packet_in_encap.apply(headers, local_metadata, standard_metadata);
    acl_egress.apply(headers, local_metadata, standard_metadata);
    // TODO: Not enough SAI resources for the second EFP bank.
    // acl_egress_dhcp_to_host.apply(headers, local_metadata, standard_metadata);
    vlan_tag.apply(headers, local_metadata, standard_metadata);
  }
}  // control egress

#ifndef PKG_INFO_NAME
#define PKG_INFO_NAME "tor.p4"
#endif
@pkginfo(
  name = PKG_INFO_NAME,
  organization = "Google"
  // TODO(PINS): 
  // version = SAI_P4_PKGINFO_VERSION_HAS_PACKET_OUT_SUPPORT
)
V1Switch(packet_parser(), verify_ipv4_checksum(), ingress(), egress(),
         compute_ipv4_checksum(), packet_deparser()) main;
