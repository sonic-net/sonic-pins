#include <ostream>

#include "absl/strings/ascii.h"
#include "absl/strings/str_join.h"
#include "tests/qos/gnmi_parsers.h"

// -- Pretty priners for golden testing ----------------------------------------

namespace std {

template <class T>
std::ostream& operator<<(std::ostream& os, const std::vector<T>& ts) {
  if (ts.empty()) return os << "<empty>";
  return os << absl::StrJoin(ts, ", ", absl::StreamFormatter());
}

template <class T, class U>
std::ostream& operator<<(std::ostream& os, const std::variant<T, U>& t_or_u) {
  struct Visitor {
    std::ostream& os;
    std::ostream& operator()(const T& t) { return os << t; }
    std::ostream& operator()(const U& u) { return os << u; }
  };
  return std::visit(Visitor{.os = os}, t_or_u);
}

}  // namespace std

namespace absl {

template <class T>
std::ostream& operator<<(std::ostream& os, const absl::StatusOr<T>& statusor) {
  if (statusor.ok()) return os << *statusor;
  return os << statusor.status().code() << ": " << statusor.status().message();
}

}  // namespace absl

// -- Actual test --------------------------------------------------------------

namespace pins_test {
namespace {

static constexpr absl::string_view kInputBanner =
    "-- INPUT "
    "-----------------------------------------------------------------------\n";

static constexpr absl::string_view kTestGnmiConfig =
    R"json(
{
   "openconfig-interfaces:interfaces" : {
      "interface" : [
          {
            "config" : {
               "name" : "Loopback0",
               "type" : "iana-if-type:softwareLoopback"
            },
            "name" : "Loopback0",
            "subinterfaces" : {
               "subinterface" : [
                  {
                     "config" : {
                        "index" : 0
                     },
                     "index" : 0,
                     "openconfig-if-ip:ipv4" : {
                        "addresses" : {
                           "address" : [
                              {
                                 "config" : {
                                    "ip" : "192.168.0.1",
                                    "prefix-length" : 27
                                 },
                                 "ip" : "192.168.0.1"
                              }
                           ]
                        }
                     },
                     "openconfig-if-ip:ipv6" : {
                        "addresses" : {
                           "address" : [
                              {
                                 "config" : {
                                    "ip" : "2607:f8b0:8096:3125::",
                                    "prefix-length" : 64
                                 },
                                 "ip" : "2607:f8b0:8096:3125::"
                              },
                              {
                                 "config" : {
                                    "ip" : "2607:f8b0:1234:5678::",
                                    "prefix-length" : 64
                                 },
                                 "ip" : "2607:f8b0:1234:5678::"
                              }
                           ]
                        }
                     }
                  }
               ]
            }
         }
      ]
   }
}
    )json";

void RunAllParsersAndPrintTheirOutput() {
  std::cout << kInputBanner << absl::StripAsciiWhitespace(kTestGnmiConfig)
            << "\n";

  // Test ParseLoopbackIps.
  std::cout << "-- OUTPUT: ParseLoopbackIps --\n";
  std::cout << ParseLoopbackIps(kTestGnmiConfig) << "\n";

  // Test ParseLoopbackIpv4s.
  std::cout << "-- OUTPUT: ParseLoopbackIpv4s --\n";
  std::cout << ParseLoopbackIpv4s(kTestGnmiConfig) << "\n";

  // Test ParseLoopbackIpv6s.
  std::cout << "-- OUTPUT: ParseLoopbackIpv6s --\n";
  std::cout << ParseLoopbackIpv6s(kTestGnmiConfig) << "\n";
}

}  // namespace
}  // namespace pins_test

int main() { pins_test::RunAllParsersAndPrintTheirOutput(); }
