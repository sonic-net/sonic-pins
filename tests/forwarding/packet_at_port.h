#ifndef PINS_TESTS_FORWARDING_PACKET_H_
#define PINS_TESTS_FORWARDING_PACKET_H_

#include <cstdint>
#include <memory>
#include <ostream>
#include <string>
#include <utility>

#include "absl/strings/escaping.h"
#include "absl/strings/string_view.h"

namespace pins {

// A packet, represented by the packet's data and the port that it was
// sent/received on.
struct PacketAtPort {
  // TODO Change it to string type port.
  int port;
  std::string data;

  bool operator==(const PacketAtPort& other) const {
    return port == other.port && data == other.data;
  }

  bool operator<(const PacketAtPort& other) const {
    return std::tie(port, data) < std::tie(other.port, other.data);
  }

  template <typename H>
  friend H AbslHashValue(H h, const PacketAtPort& m);
};

inline std::ostream& operator<<(std::ostream& os,
                                const ::pins::PacketAtPort& packet) {
  return os << "{port: " << packet.port << " length: " << packet.data.size()
            << " data: \"" << absl::BytesToHexString(packet.data) << "\"}";
}

template <typename H>
H AbslHashValue(H h, const PacketAtPort& m) {
  return H::combine(std::move(h), m.port, m.data);
}

}  // namespace pins

#endif // PINS_TESTS_FORWARDING_PACKET_H_
