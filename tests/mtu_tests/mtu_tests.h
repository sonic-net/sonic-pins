#ifndef PINS_TESTS_MTU_TESTS_MTU_TESTS_H_
#define PINS_TESTS_MTU_TESTS_MTU_TESTS_H_

#include "absl/base/config.h"
#include "absl/strings/string_view.h"
#include "lib/p4rt/p4rt_programming_context.h"
#include "lib/utils/generic_testbed_utils.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "thinkit/generic_testbed_fixture.h"
namespace pins_test {

struct NumPkts {
  int sent;
  int received;
};

class MtuRoutingTestFixture : public thinkit::GenericTestbedFixture<> {
protected:
  // Acquires testbed with 2 pairs of connected ports between SUT and
  // control switch. Sets up route from first to second port on SUT.
  void SetUp() override;

  // Generates test UDP packet with given payload length.
  std::string GenerateTestPacket(absl::string_view destination_ip,
                                 int payload_len);

  // Sends num_pkts/unlimited packets from egress_port. Collects packets on
  // ingress_port and returns number of packets sent and received.
  absl::StatusOr<NumPkts> SendTraffic(int num_pkts,
                                      absl::string_view egress_port,
                                      absl::string_view ingress_port,
                                      absl::string_view test_packet_str);

  // Set up route from source port to destination port on SUT.
  absl::Status SetupRoute(P4rtProgrammingContext *p4rt_context);

  InterfaceLink source_link_, destination_link_;
  int sut_source_port_id_, sut_destination_port_id_;
  std::unique_ptr<thinkit::GenericTestbed> testbed_;
  std::unique_ptr<gnmi::gNMI::StubInterface> stub_;
};

} // namespace pins_test

#endif // PINS_TESTS_MTU_TESTS_MTU_TESTS_H_
