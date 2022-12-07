#ifndef SAI_DROP_MARTIANS_P4_
#define SAI_DROP_MARTIANS_P4_

// Drop certain special-use (aka martian) addresses.

const ipv6_addr_t IPV6_MULTICAST_MASK =
  0xff00_0000_0000_0000_0000_0000_0000_0000;
const ipv6_addr_t IPV6_MULTICAST_VALUE =
  0xff00_0000_0000_0000_0000_0000_0000_0000;

const ipv4_addr_t IPV4_MULTICAST_MASK = 0xf0_00_00_00;
const ipv4_addr_t IPV4_MULTICAST_VALUE = 0xe0_00_00_00;

const ipv4_addr_t IPV4_BROADCAST_VALUE = 0xff_ff_ff_ff;

#define IS_IPV6_MULTICAST(address) \
    (address & IPV6_MULTICAST_MASK == IPV6_MULTICAST_VALUE)

#define IS_IPV4_MULTICAST_OR_BROADCAST(address) \
    ((address & IPV4_MULTICAST_MASK == IPV4_MULTICAST_VALUE) || \
     (address == IPV4_BROADCAST_VALUE))

control drop_martians(in headers_t headers,
                      inout local_metadata_t local_metadata,
                      inout standard_metadata_t standard_metadata) {
  apply {
    // Drop the packet if:
    // - Src or dst IPv6 addresses are in multicast range; or
    // - Src or dst IPv4 addresses are in multicast or broadcast range.
    // Rationale:
    // Src IP multicast drop: https://www.rfc-editor.org/rfc/rfc1812#section-5.3.7
    // Dst IP multicast drop: multicast is not yet modeled and our switches drop
    // multicast packets for now.
    if ((headers.ipv6.isValid() &&
            (IS_IPV6_MULTICAST(headers.ipv6.src_addr) ||
             IS_IPV6_MULTICAST(headers.ipv6.dst_addr))) ||
        (headers.ipv4.isValid() &&
            (IS_IPV4_MULTICAST_OR_BROADCAST(headers.ipv4.src_addr) ||
             IS_IPV4_MULTICAST_OR_BROADCAST(headers.ipv4.dst_addr)))) {
        mark_to_drop(standard_metadata);
    }

    // TODO: Drop the rest of martian packets.
  }
}  // control drop_martians


#endif  // SAI_DROP_MARTIANS_P4_
