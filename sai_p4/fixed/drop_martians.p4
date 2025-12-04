#ifndef SAI_DROP_MARTIANS_P4_
#define SAI_DROP_MARTIANS_P4_

// Drop certain special-use (aka martian) addresses.

const ipv6_addr_t IPV6_MULTICAST_MASK =
  0xff00_0000_0000_0000_0000_0000_0000_0000;
const ipv6_addr_t IPV6_MULTICAST_VALUE =
  0xff00_0000_0000_0000_0000_0000_0000_0000;

// ::1/128
const ipv6_addr_t IPV6_LOOPBACK_MASK =
  0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ffff;
const ipv6_addr_t IPV6_LOOPBACK_VALUE =
  0x0000_0000_0000_0000_0000_0000_0000_0001;

const ipv4_addr_t IPV4_MULTICAST_MASK = 0xf0_00_00_00;
const ipv4_addr_t IPV4_MULTICAST_VALUE = 0xe0_00_00_00;

const ipv4_addr_t IPV4_BROADCAST_VALUE = 0xff_ff_ff_ff;

// 127.0.0.0/8
const ipv4_addr_t IPV4_LOOPBACK_MASK = 0xff_00_00_00;
const ipv4_addr_t IPV4_LOOPBACK_VALUE = 0x7f_00_00_00;

// 0.X.Y.Z/8
const ipv4_addr_t IPV4_THIS_HOST_ON_THIS_NETWORK_MASK = 0xff_00_00_00;
const ipv4_addr_t IPV4_THIS_HOST_ON_THIS_NETWORK_VALUE = 0x00_00_00_00;

#define IS_MULTICAST_IPV6(address) \
  (address & IPV6_MULTICAST_MASK == IPV6_MULTICAST_VALUE)

#define IS_LOOPBACK_IPV6(address) \
  (address & IPV6_LOOPBACK_MASK == IPV6_LOOPBACK_VALUE)

#define IS_MULTICAST_IPV4(address) \
  (address & IPV4_MULTICAST_MASK == IPV4_MULTICAST_VALUE)

#define IS_BROADCAST_IPV4(address) \
  (address == IPV4_BROADCAST_VALUE)

#define IS_LOOPBACK_IPV4(address) \
  (address & IPV4_LOOPBACK_MASK == IPV4_LOOPBACK_VALUE)

#define IS_THIS_HOST_ON_THIS_NETWORK_IPV4(address) \
  (address & IPV4_THIS_HOST_ON_THIS_NETWORK_MASK == IPV4_THIS_HOST_ON_THIS_NETWORK_VALUE)

// I/G bit = 1 means multicast.
#define IS_UNICAST_MAC(address) \
  (address[40:40] == 0)

#define IS_IPV4_MULTICAST_MAC(address) \
  (address[47:24] == 0x01005E && address[23:23] == 0)

#define IS_IPV6_MULTICAST_MAC(address) \
  (address[47:32] == 0x3333)

// TODO: If it turns out that this logic does not apply to ACL 
// redirects, call logic after `routing_lookup` but before `acl_ingress`.
control drop_martians(in headers_t headers,
                      inout local_metadata_t local_metadata,
                      inout standard_metadata_t standard_metadata) {
  apply {
    bool acl_l3_redirect =
          (local_metadata.acl_ingress_ipmc_redirect ||
          local_metadata.acl_ingress_nexthop_redirect);

    // TODO: Remove the `acl_l3_redirect` check when the switch
    // correctly handles martians during ACL redirection.
    // Packets going through L2 multicast (and potentially other L2 forwarded
    // packets) bypass the martian check.
    bool bypass_martian_check =
        acl_l3_redirect || local_metadata.acl_ingress_l2mc_redirect;

    // Drop the packet if:
    // - Packet is not redirected by ingress ACL; or
    // - Src IPv6 address is in multicast range; or
    // - Src IPv4 address is in multicast or broadcast range; or
    // - Src/Dst IPv4/IPv6 address is a loopback address; or
    // - Dst IPv4 address is 0.X.Y.Z; or
    // - Src/Dst IPv4/IPv6 is the all-zero address.
    // Rationale:
    // Src IP multicast drop: https://www.rfc-editor.org/rfc/rfc1812#section-5.3.7
    // Src/Dst IP loopback drop: https://en.wikipedia.org/wiki/Localhost#Packet_processing
    //    "Packets received on a non-loopback interface with a loopback source
    //     or destination address must be dropped."
    // Drop Dst IP signifying "this host on this network" (i.e. 0.X.Y.Z):
    //    https://datatracker.ietf.org/doc/html/rfc6890#section-2.2.2
    // Dst IP all zeroes drop: https://en.wikipedia.org/wiki/0.0.0.0
    //    "RFC 1122 [...] prohibits this as a destination address."
    // Src IPv4 all zeros drop: https://www.rfc-editor.org/rfc/rfc1812#section-5.3.7
    // Src IPv6 all zeros drop: https://www.rfc-editor.org/rfc/rfc4291#section-2.5.2
    if (!bypass_martian_check &&
        ((headers.ipv6.isValid() &&
            (IS_MULTICAST_IPV6(headers.ipv6.src_addr) ||
             IS_LOOPBACK_IPV6(headers.ipv6.src_addr) ||
             IS_LOOPBACK_IPV6(headers.ipv6.dst_addr) ||
             headers.ipv6.src_addr == 0 ||
             headers.ipv6.dst_addr == 0)) ||
        (headers.ipv4.isValid() &&
            (IS_MULTICAST_IPV4(headers.ipv4.src_addr) ||
             IS_BROADCAST_IPV4(headers.ipv4.src_addr) ||
             IS_BROADCAST_IPV4(headers.ipv4.dst_addr) ||
             IS_LOOPBACK_IPV4(headers.ipv4.src_addr) ||
             IS_LOOPBACK_IPV4(headers.ipv4.dst_addr) ||
             IS_THIS_HOST_ON_THIS_NETWORK_IPV4(headers.ipv4.dst_addr) ||
             headers.ipv4.src_addr == 0 ||
             headers.ipv4.dst_addr == 0)))
       ) {
        mark_to_drop(standard_metadata);
    }

// TODO: Remove guard once p4-symbolic suports assertions.
#ifndef PLATFORM_P4SYMBOLIC
    if(headers.hop_by_hop_options.isValid()) {
        assert(headers.hop_by_hop_options.header_extension_length == 0);
    }

    if(headers.inner_hop_by_hop_options.isValid()) {
        assert(headers.inner_hop_by_hop_options.header_extension_length == 0);
    }
#endif

    // PINs switches drop packets with hop-by-hop options by choice, not by
    // necessity. All expected packets should be punted, so we mark them all to
    // drop by choice to get some deterministic behavior.
    if (!bypass_martian_check &&
        (headers.hop_by_hop_options.isValid() ||
        headers.inner_hop_by_hop_options.isValid())) {
        mark_to_drop(standard_metadata);
    }

    // TODO: Drop the rest of martian packets.
  }
}  // control drop_martians


#endif  // SAI_DROP_MARTIANS_P4_
