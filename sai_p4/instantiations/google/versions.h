#ifndef PINS_SAI_VERSIONS_H_
#define PINS_SAI_VERSIONS_H_

// --- PkgInfo versions --------------------------------------------------------
// For use in `@pkginfo(..., version = VERSION)` annotations.
// We use semantic versioning. Version numbers must increase monotonically.

// Indicates that the program has packet out support.
#define SAI_P4_PKGINFO_VERSION_HAS_PACKET_OUT_SUPPORT "1.0.0"

// Indicates that the program has packet in support.
#define SAI_P4_PKGINFO_VERSION_HAS_PACKET_IN_SUPPORT "1.1.0"

// Indicates that the program has acl_ingress_counting_table support.
#define SAI_P4_PKGINFO_VERSION_HAS_ACL_INGRESS_COUNTING_SUPPORT "1.2.0"

// Indicates that the program can support CPU Queue parameters as Names.
#define SAI_P4_PKGINFO_VERSION_HAS_CPU_QUEUE_NAME_SUPPORT "1.3.0"

// Indicates that the switch fully supports abstracted CPU Queue names.
// While Version 1.3.0 supported using CPU queue name instead of
// queue id, the new CPU queues dedicated for Controller bound
// packets are provisioned in 1.4.0.
#define SAI_P4_PKGINFO_VERSION_HAS_DEDICATED_CONTROLLER_CPU_QUEUES "1.4.0"

// Indicates that P4 program no longer contains
// mirror_port_to_pre_session_table.
// Removing a table is a breaking change and should have required a major
// version bump. We didn't because the next two major versions have been
// reserved and we can not skip major versions from the current version.
// This is ok since our infra doesn't care about semantic versioning's
// semantics.
#define SAI_P4_PKGINFO_VERSION_HAS_NO_MIRROR_PORT_TO_PRE_SESSION_TABLE "1.4.1"

// Indicates that the switch supports read requests for multicast group entries.
#define SAI_P4_PKGINFO_VERSION_SUPPORTS_PACKET_REPLICATION_ENGINE_READS "1.5.0"

// Indicates the program has ingress cloning support that allows cloning +
// punting the same packet.
#define SAI_P4_PKGINFO_VERSION_HAS_INGRESS_CLONING_SUPPORT "1.6.0"

// Indicates the switch supports multiple WCMP members with the same Nexthop.
#define SAI_P4_PKGINFO_VERSION_HAS_DUPLICATE_WCMP_MEMBER_SUPPORT "1.6.1"

// Indicates that switch respects ingress ACL resource guarantees.
#define SAI_P4_PKGINFO_VERSION_FIXED_INGRESS_ACL_RESOURCE "1.6.2"

// Indicates that the program does not support the `set_nexthop` action.
#define SAI_P4_PKGINFO_VERSION_HAS_NO_SET_NEXTHOP_SUPPORT "2.0.0"

// Indicates the switch supports P4Info ReconcileAndCommit for most cases.
#define SAI_P4_PKGINFO_VERSION_SUPPORTS_RECONCILE "2.1.0"

// Indicates the switch supports multicast group entry metadata.
#define SAI_P4_PKGINFO_VERSION_SUPPORTS_MULTICAST_METADATA "2.2.0"

// Indicates the switch supports the `acl_egress_l2_table` (if of the right
// instantiation).
#define SAI_P4_PKGINFO_VERSION_SUPPORTS_ACL_EGRESS_L2_TABLE "2.3.0"

// Indicates the switch uses int64_t for meter config (previously int).
#define SAI_P4_PKGINFO_VERSION_METER_CONFIG_USES_INT64 "2.5.0"

// Indicates the switch disables sub_port RIF VLAN configuration.
#define SAI_P4_PKGINFO_VERSION_DISABLE_SUB_PORT_RIF_VLAN_CONFIG "2.6.0"

// Indicates that the program supports ternary rather than optional route
// metadata in the acl_ingress_table.
#define SAI_P4_PKGINFO_VERSION_USES_TERNARY_ROUTE_METADATA "3.0.0"

// Indicates that the program supports all valid modifications to the
// `acl_ingress_table`.
#define SAI_P4_PKGINFO_VERSION_SUPPORTS_ACL_INGRESS_MODIFY "3.0.1"

// Indicates that the program supports reconciliation of populated ACL tables.
#define SAI_P4_PKGINFO_VERSION_SUPPORTS_ACL_RECONCILE "3.0.2"

// Indicates the switch executes batched updates in order, aborting every update
// after the first failed one.
#define SAI_P4_PKGINFO_VERSION_USES_FAIL_ON_FIRST "3.1.0"

// Indicates the switch supports 512 duplicate WCMP members per group in native
// mode.
#define SAI_P4_PKGINFO_VERSION_SUPPORTS_512_DUPLICATE_WCMP_MEMBERS_IN_NATIVE \
  "3.1.1"

// Indicates that the switch supports unicast_set_port_and_src_mac action, which
// at the SAI level translates to port type RIFs that do NOT program l3_admit
// table (i.e. MyMac at SAI) under the hood.
#define SAI_P4_PKGINFO_VERSION_SUPPORTS_UNICAST_SET_PORT_AND_SRC_MAC_ACTION \
  "3.2.0"

// Indicates the switch executes batched updates in order, aborting every update
// after the first failed one.
#define SAI_P4_PKGINFO_VERSION_USES_FAIL_ON_FIRST "3.2.1"

// Indicates that the switch uses "route_hit" instead of "ipmc_table_hit" as the
// name for ACL keys with
// `@sai_field(SAI_ACL_ENTRY_ATTR_FIELD_ROUTE_NPU_META_DST_HIT)`.
#define SAI_P4_PKGINFO_VERSION_USES_ROUTE_HIT_ACL_QUALIFIER_NAME "

// Indicates that the switch supports unicast_set_port_and_src_mac_and_vlan_id
// action, which at the SAI level translates to sub_port type RIFs that do NOT
// program l3_admit table (i.e. MyMac at SAI) under the hood.
#define SAI_P4_PKGINFO_VERSION_USES_UNICAST_SET_PORT_AND_SRC_MAC_AND_VLAN_\
ID_ACTION \
  "5.0.0"

// Macro that always points to the latest SAI P4 version.
#define SAI_P4_PKGINFO_VERSION_LATEST SAI_P4_PKGINFO_VERSION_USES_FAIL_ON_FIRST

#endif // PINS_SAI_VERSIONS_H_
