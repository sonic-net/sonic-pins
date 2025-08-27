// Copyright 2025 Google LLC
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

#ifndef PINS_SAI_P4_INSTANTIATIONS_ANNOTATIONS_H_
#define PINS_SAI_P4_INSTANTIATIONS_ANNOTATIONS_H_

#include "absl/strings/string_view.h"

// This file lists meaningful annotations for sai p4 programs.

namespace sai {
namespace annotation {

// General SAI P4 annotations

// @format(<format>) indicates the expected format of the value on the wire.
//
// Applies to: table match fields, action parameters
// Values:
//   IPV4_ADDRESS: IPv4 address. E.g. 1.2.3.4
//   IPV6_ADDRESS: IPv6 address. E.g. 1234:5678:0:0::
//   MAC_ADDRESS: MAC address. E.g. aa:bb:cc:dd:ee:ff
inline constexpr absl::string_view kFormat = "format";

// TODO: Remove this annotation when we update acl_ingress.p4 to
// use the new standard meter annotations.
//
// @mode(<meter_mode>) indicates the mode of the meter object.
//
// Applies to: direct_meter objects
// Values:
//   single_rate_two_color: single rate meter creating red & green
//   single_rate_three_color: single rate meter creating red, yellow, & green
//   two_rate_three_color, two rate meter creating red, yellow, & green
inline constexpr absl::string_view kMeterMode = "mode";

// @refers_to(<table>, <match_field>) indicates that this field refers to one or
// more entries in a separate table identifiable by the value in the specified
// match_field.
//
// When using a refers-to value, the referenced entry must first exist.
//
// See go/p4-references-and-multicast, go/p4-use, and go/p4-sequencing for more
// information.
//
// Applies to: Table match fields, action parameters
// Values:
//   table: the name of table containing the entry being referenced.
//   key: the name of the table match field that corresponds to the value.
inline constexpr absl::string_view kRefersTo = "refers_to";

// TODO: Describe @referenced_by
inline constexpr absl::string_view kReferencedBy = "referenced_by";

// @entry_restriction(<restriction>) defines the set of rules indicating whether
// an entry is valid for this table. These rules can be used to reject an entry
// during a Write request.
//
// Applies to: table objects
// Value:
//   P4 constraints string: github.com/p4lang/p4-constraints
inline constexpr absl::string_view kEntryRestriction = "entry_restriction";

// @action_restriction(<restriction>) defines the set of rules indicating
// whether the set of action parameters is valid. These rules can be used to
// reject an entry during a Write request.
//
// Applies to: action objects
// Value:
//   P4 constraints string: github.com/p4lang/p4-constraints
inline constexpr absl::string_view kActionRestriction = "action_restriction";

// @unsupported indicates that this object is not fully supported today and
// should not be made available for use yet. This can be helpful for guarding a
// new feature while still enabling development, simulation and testing before
// full switch support is available. Any P4Runtime entity that refers to an
// unsupported object will be rejected by the switch.
//
// See go/unblocking-sai-p4 for more details.
//
// Applies to: action objects, table objects
inline constexpr absl::string_view kUnsupported = "unsupported";

// ACL-Related Annotations

// @sai_acl(<stage>) denotes an ACL table. The body indicates the stage of the
// ACL table.
//
// Applies to: table objects
// Values: PRE_INGRESS, INGRESS, EGRESS
inline constexpr absl::string_view kSaiAcl = "sai_acl";

// @sai_acl_priority(<priority>) denotes the relative priority of an ACL table.
//
// Applies to: table objects
// Value: Integer Priority (higher is higher)
inline constexpr absl::string_view kSaiAclPriority = "sai_acl_priority";

// @sai_field(<sai_field>) denotes the SAI match field referred to by this P4
// match key.
//
// Applies to: table match keys
// Value: SAI_ACL_TABLE_ATTR_FIELD_* values defined in in saiacl.h
inline constexpr absl::string_view kSaiField = "sai_field";

// @sai_udf(base=<base>, offset=<offset>, length=<length>) indicates a SAI UDF
// represented by this P4 match key.
//
// Applies to: table match keys
// Value:
//   <base>: SAI_UDF_BASE_L2, SAI_UDF_BASE_L3, SAI_UDF_BASE_L4
//   <offset>: Integer byte offset from base.
//   <length>: Integer length of UDF field in bytes.
inline constexpr absl::string_view kSaiUdf = "sai_udf";

// @composite_field(<field1>, [<field2>, ..., <fieldN>]) indicates this match
// key is a composite of multiple SAI match fields. The composite key bitwidth
// must be the sum of the bitwidths of each component field. Fields are ordered
// from MSB to LSB of the key value.
//
// Applies to: table match keys
// Value: Each <field> is must be either a @sai_field or @sai_udf annotation.
inline constexpr absl::string_view kCompositeField = "composite_field";

// @sai_action(<sai_action>[, color]) denotes the SAI action performed by this
// action.
//
// Applies to: action objects
// Values:
//   sai_action: Unparameterized SAI action, SAI_PACKET_ACTION_* defined in
//               saiacl.h
//   color: Optional parameter, limits sai_action to packets of X color.
//          SAI_PACKET_COLOR_RED, SAI_PACKET_COLOR_YELLOW,
//          SAI_PACKET_COLOR_GREEN
inline constexpr absl::string_view kSaiAction = "sai_action";

// @sai_action_param(<sai_param>) denotes the SAI action & value associated with
// this action parameter.
//
// Applies to: action parameters
// Values: SAI_ACL_ENTRY_ATTR_ACTION_* values from saiacl.h
//         Custom values may also exist depending on implementation.
inline constexpr absl::string_view kSaiActionParam = "sai_action_param";

// @sai_action_param_object_type(<sai_object_type>) indicates the SAI object
// type that this parameter may refer to.
//
// Applies to: action parameters
// values: SAI_OBJECT_TYPE_* defined in saibridge.h
inline constexpr absl::string_view kSaiActionParamObjectType =
    "sai_action_param_object_type";

// @nonessential_for_upgrade indicates that the entries in this table may be
// removed for a short period during a P4info reconciliation.
//
// Applies to: table objects
inline constexpr absl::string_view kNonessentialForUpgrade =
    "nonessential_for_upgrade";

// @reinstall_during_upgrade indicates that this table should be reinstalled
// during a P4Info reconcile even if there is no change to the table semantics.
// This may be used to test table reconciliation or, if combined with
// @nonessential_for_upgrade, used to provide space for another, essential
// table to reconcile.
//
// Applies to: table objects
inline constexpr absl::string_view kReinstallDuringUpgrade =
    "reinstall_during_upgrade";

// Hash-Related Annotations

// @sai_hash_seed(<seed>) sets the seed value for the hash configuration.
//
// Applies to: hash algorithm action object within ecmp or lag hashing config
//             control block.
// Values: Unsigned integer hash seed
inline constexpr absl::string_view kSaiHashSeed = "sai_hash_seed";

// @sai_hash_offset(<offset>) sets the offset value for the hash configuration.
//
// Applies to: hash algorithm action object within ecmp or lag hashing config
//             control block.
// Values: Unsigned integer hash offset
inline constexpr absl::string_view kSaiHashOffset = "sai_hash_offset";

// @sai_hash_algorithm(<algorithm>) sets the algorithm the hash configuration.
//
// Applies to: hash algorithm action object within ecmp or lag hashing config
//             control block.
// Values: One of:
//         SAI_HASH_ALGORITHM_CRC, SAI_HASH_ALGORITHM_XOR,
//         SAI_HASH_ALGORITHM_RANDOM, SAI_HASH_ALGORITHM_CRC_32LO,
//         SAI_HASH_ALGORITHM_CRC_32HI, SAI_HASH_ALGORITHM_CRC_CCITT,
//         SAI_HASH_ALGORITHM_CRC_XOR
inline constexpr absl::string_view kSaiHashAlgorithm = "sai_hash_algorithm";

// @sai_native_hash_field(<field>) adds the field to the associated hash
// computation. Multiple @sai_native_hash_field() annotations may be attached to
// a computation action.
//
// Applies to: hash config compute action objects
// Values: The subset of values in sai_native_hashfield_t:
//         SAI_NATIVE_HASH_FIELD_SRC_IPV4, SAI_NATIVE_HASH_FIELD_DST_IPV4,
//         SAI_NATIVE_HASH_FIELD_SRC_IPV6, SAI_NATIVE_HASH_FIELD_DST_IPV6,
//         SAI_NATIVE_HASH_FIELD_L4_DST_PORT, SAI_NATIVE_HASH_FIELD_L4_SRC_PORT,
//         SAI_NATIVE_HASH_FIELD_IPV6_FLOW_LABEL
inline constexpr absl::string_view kSaiNativeHashField =
    "sai_native_hash_field";

// @sai_lag_hash(<lag_hash_type>) specifies the type of packets to which this
// lag hash computation applies.
//
// Applies to: lag hash config compute action objects
// Values: SAI_SWITCH_ATTR_LAG_HASH_IPV4, SAI_SWITCH_ATTR_LAG_HASH_IPV6
inline constexpr absl::string_view kLagHash = "sai_lag_hash";

// @sai_ecmp_hash(<ecmp_hash_type>) specifies the type of packets to which this
// ecmp hash computation applies.
//
// Applies to: ecmp hash config compute action objects
// Values: SAI_SWITCH_ATTR_ECMP_HASH_IPV4, SAI_SWITCH_ATTR_ECMP_HASH_IPV6
inline constexpr absl::string_view kEcmpHash = "sai_ecmp_hash";

}  // namespace annotation
}  // namespace sai

#endif  // PINS_SAI_P4_INSTANTIATIONS_ANNOTATIONS_H_
