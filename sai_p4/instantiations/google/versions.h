#ifndef GOOGLE_SAI_VERSIONS_H_
#define GOOGLE_SAI_VERSIONS_H_

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

// Indicates that the program does not support the `set_nexthop` action.
#define SAI_P4_PKGINFO_VERSION_HAS_NO_SET_NEXTHOP_SUPPORT "2.0.0"

// Indicates that the program supports ternary rather than optional route
// metadata in the acl_ingress_table.
#define SAI_P4_PKGINFO_VERSION_USES_TERNARY_ROUTE_METADATA "3.0.0"

// Macro that always points to the latest SAI P4 version.
#define SAI_P4_PKGINFO_VERSION_LATEST \
  SAI_P4_PKGINFO_VERSION_HAS_DEDICATED_CONTROLLER_CPU_QUEUES

#endif  // GOOGLE_SAI_VERSIONS_H_
