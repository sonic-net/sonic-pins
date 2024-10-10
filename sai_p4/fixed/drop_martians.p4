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

// I/G bit = 1 means multicast.
const ethernet_addr_t MAC_MULTICAST_MASK = 0x01_00_00_00_00_00;
const ethernet_addr_t MAC_MULTICAST_VALUE = 0x01_00_00_00_00_00;


#define IS_IPV6_MULTICAST(address) \
    (address & IPV6_MULTICAST_MASK == IPV6_MULTICAST_VALUE)

#define IS_IPV6_LOOPBACK(address) \
    (address & IPV6_LOOPBACK_MASK == IPV6_LOOPBACK_VALUE)

#define IS_IPV4_MULTICAST_OR_BROADCAST(address) \
    ((address & IPV4_MULTICAST_MASK == IPV4_MULTICAST_VALUE) || \
     (address == IPV4_BROADCAST_VALUE))

#define IS_IPV4_LOOPBACK(address) \
    (address & IPV4_LOOPBACK_MASK == IPV4_LOOPBACK_VALUE)

#define IS_MAC_MULTICAST(address) \
    (address & MAC_MULTICAST_MASK == MAC_MULTICAST_VALUE)


control drop_martians(in headers_t headers,
                      inout local_metadata_t local_metadata,
                      inout standard_metadata_t standard_metadata) {
  apply {
    // Drop the packet if:
    // - Src/Dst IPv6 addresses are in multicast range; or
    // - Src/Dst IPv4 addresses are in multicast or broadcast range; or
    // - I/G bit in dst MAC address is set (i.e. a multicast address); or
    // - Src/Dst IPv4/IPv6 address is a loopback address.
    // Rationale:
    // Src IP multicast drop: https://www.rfc-editor.org/rfc/rfc1812#section-5.3.7
    // Dst IP multicast drop: multicast is not yet modeled and our switches drop
    // multicast packets for now.
    // Src/Dst IP loopback drop: https://en.wikipedia.org/wiki/Localhost#Packet_processing
    //    "Packets received on a non-loopback interface with a loopback source
    //     or destination address must be dropped."
    // Dst MAC multicast drop: multicast is not yet modeled and our switches
    // drop multicast packets for now.
    if ((headers.ipv6.isValid() &&
            (IS_IPV6_MULTICAST(headers.ipv6.src_addr) ||
             // TODO: Rework conditions under which IPMC packets
             // get forwarded and remove this constraint.
             IS_IPV6_MULTICAST(headers.ipv6.dst_addr) ||
             IS_IPV6_LOOPBACK(headers.ipv6.src_addr) ||
             IS_IPV6_LOOPBACK(headers.ipv6.dst_addr))) ||
        (headers.ipv4.isValid() &&
            (IS_IPV4_MULTICAST_OR_BROADCAST(headers.ipv4.src_addr) ||
             // TODO: Rework conditions under which IPMC packets
             // get forwarded and update this constraint.
             IS_IPV4_MULTICAST_OR_BROADCAST(headers.ipv4.dst_addr) ||
             IS_IPV4_LOOPBACK(headers.ipv4.src_addr) ||
             IS_IPV4_LOOPBACK(headers.ipv4.dst_addr))) ||
        (headers.ethernet.isValid() &&
            IS_MAC_MULTICAST(headers.ethernet.dst_addr))) {
        mark_to_drop(standard_metadata);
    }

    // TODO: Drop the rest of martian packets.
  }
}  // control drop_martians


#endif  // SAI_DROP_MARTIANS_P4_
