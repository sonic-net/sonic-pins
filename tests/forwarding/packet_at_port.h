#ifndef PINS_TESTS_FORWARDING_PACKET_H_
#define PINS_TESTS_FORWARDING_PACKET_H_

#include <ostream>
#include <string>
#include <tuple>
#include <utility>

#include "absl/strings/escaping.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"

namespace pins {

// A packet, represented by the packet's data and the port that it was
// sent/received on.
struct PacketAtPort {
  // TODO Change it to string type port.
  int port;
  // This string represents the packet's serialized data (bytestring).
  std::string data;
};

inline bool operator==(const PacketAtPort& lhs, const PacketAtPort& rhs) {
  return lhs.port == rhs.port && lhs.data == rhs.data;
}

inline bool operator<(const PacketAtPort& lhs, const PacketAtPort& rhs) {
  return std::tie(lhs.port, lhs.data) < std::tie(rhs.port, rhs.data);
}

// Only intended for debugging purposes.  Do not assume output consistency.
template <typename Sink>
inline void AbslStringify(Sink& sink, const pins::PacketAtPort& packet) {
  absl::Format(&sink, "{port: %d length: %d data: \"%s\"}", packet.port,
               packet.data.size(), absl::BytesToHexString(packet.data));
};

inline std::ostream& operator<<(std::ostream& os,
                                const ::pins::PacketAtPort& packet) {
  return os << absl::StrCat(packet);
}

template <typename H>
H AbslHashValue(H h, const PacketAtPort& m) {
  return H::combine(std::move(h), m.port, m.data);
}

}  // namespace pins

#endif // PINS_TESTS_FORWARDING_PACKET_H_
