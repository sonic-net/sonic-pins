#include "tests/mtu_tests/mtu_tests.h"

#include <memory>
#include <string>
#include <type_traits>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/numbers.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/synchronization/mutex.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/collections.h"
#include "gutil/proto.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "lib/basic_traffic/basic_p4rt_util.h"
#include "lib/basic_traffic/basic_traffic.h"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/p4rt/p4rt_programming_context.h"
#include "lib/utils/generic_testbed_utils.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/netaddr/ipv4_address.h"
#include "p4_pdpi/netaddr/ipv6_address.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/packetlib/packetlib.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_pdpi/pd.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "thinkit/control_device.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/proto/generic_testbed.pb.h"
#include "thinkit/switch.h"

namespace pins_test {

std::string MtuRoutingTestFixture::GenerateTestPacket(
    absl::string_view destination_ip, const int payload_len) {
  std::string payload(payload_len, 'x');
  std::string test_packet = absl::Substitute(
      R"pb(
        headers {
          ethernet_header {
            ethernet_destination: "02:03:04:05:06:07"
            ethernet_source: "00:01:02:03:04:05"
            ethertype: "0x0800"
          }
        }
        headers {
          ipv4_header {
            version: "0x4"
            ihl: "0x5"
            dscp: "0x03"
            ecn: "0x0"
            identification: "0x0000"
            flags: "0x0"
            fragment_offset: "0x0000"
            ttl: "0x20"
            protocol: "0x11"
            ipv4_source: "1.2.3.4"
            ipv4_destination: "$0"
          }
        }
        headers {
          udp_header { source_port: "0x0000" destination_port: "0x0000" }
        }
        payload: "$1")pb",
      destination_ip, payload);
  return test_packet;
}

absl::Status MtuRoutingTestFixture::SetupRoute(
    P4rtProgrammingContext* p4rt_context) {
  ASSIGN_OR_RETURN(auto port_id_from_sut_interface,
                   GetAllInterfaceNameToPortId(*stub_));
  ASSIGN_OR_RETURN(const pdpi::IrP4Info ir_p4info,
                   pdpi::CreateIrP4Info(GetParam().p4_info));
  RETURN_IF_ERROR(basic_traffic::ProgramRoutes(
      p4rt_context->GetWriteRequestFunction(), ir_p4info,
      port_id_from_sut_interface,
      {{.ingress_interface = source_link_.sut_interface,
        .egress_interface = destination_link_.sut_interface}}));
  return absl::OkStatus();
}

void MtuRoutingTestFixture::SetUp() {
  thinkit::GenericTestbedFixture<>::SetUp();
  thinkit::TestRequirements requirements =
      gutil::ParseProtoOrDie<thinkit::TestRequirements>(
          R"pb(interface_requirements {
                 count: 2
                 interface_mode: CONTROL_INTERFACE
               })pb");

  ASSERT_OK_AND_ASSIGN(testbed_, GetTestbedWithRequirements(requirements));
  std::vector<InterfaceLink> control_links =
      FromTestbed(GetAllControlLinks, *testbed_);
  ASSERT_OK_AND_ASSIGN(stub_, testbed_->Sut().CreateGnmiStub());
  ASSERT_OK_AND_ASSIGN(auto port_id_by_interface,
                       GetAllInterfaceNameToPortId(*stub_));

  // Set the `source_link_` to the first SUT control link.
  source_link_ = control_links[0];
  ASSERT_OK_AND_ASSIGN(
      std::string source_port_id_value,
      gutil::FindOrStatus(port_id_by_interface, source_link_.sut_interface));
  ASSERT_TRUE(absl::SimpleAtoi(source_port_id_value, &sut_source_port_id_));

  // Set the `destination_link_` to the second SUT control link.
  destination_link_ = control_links[1];
  ASSERT_OK_AND_ASSIGN(std::string destination_port_id_value,
                       gutil::FindOrStatus(port_id_by_interface,
                                           destination_link_.sut_interface));
  ASSERT_TRUE(
      absl::SimpleAtoi(destination_port_id_value, &sut_destination_port_id_));

  LOG(INFO) << "Source port: " << source_link_.sut_interface
            << " port id: " << sut_source_port_id_;
  LOG(INFO) << "Destination port: " << destination_link_.sut_interface
            << " port id: " << sut_destination_port_id_;
}

absl::StatusOr<NumPkts> MtuRoutingTestFixture::SendTraffic(
    const int num_pkts, absl::string_view egress_port,
    absl::string_view ingress_port, absl::string_view test_packet_str) {
  auto test_packet = gutil::ParseProtoOrDie<packetlib::Packet>(test_packet_str);
  ASSIGN_OR_RETURN(std::string test_packet_data,
                   packetlib::SerializePacket(test_packet));

  absl::Mutex mutex;
  std::vector<std::string> received_packets;
  int i;
  {
    ASSIGN_OR_RETURN(auto finalizer,
                     testbed_->ControlDevice().CollectPackets());

    LOG(INFO) << "Sending Packet to " << ingress_port << " from "
              << egress_port;
    LOG(INFO) << "Test packet data: " << test_packet_str;

    for (i = 0; i < num_pkts; i++) {
      RETURN_IF_ERROR(
          testbed_->ControlDevice().SendPacket(egress_port, test_packet_data))
          << "failed to inject the packet.";
      LOG(INFO) << "SendPacket completed";
    }
    RETURN_IF_ERROR(finalizer->HandlePacketsFor(
        absl::Seconds(30),
        [&](absl::string_view interface, absl::string_view packet) {
          packetlib::Packet parsed_packet = packetlib::ParsePacket(packet);
          if (interface == ingress_port &&
              parsed_packet.payload() == test_packet.payload()) {
            absl::MutexLock lock(&mutex);
            received_packets.push_back(std::string(packet));
          }
        }));
  }
  return NumPkts{i, static_cast<int>(received_packets.size())};
}

namespace {

using ::testing::HasSubstr;

constexpr absl::string_view kMtuRespParseStr = "openconfig-interfaces:mtu";
constexpr int kDefaultMtu = 9194;

// Map of mtu to payload length for packets that are expected to be
// successfully egressed out of port under test.
const auto* const kMtuPacketPayloadMap = new absl::flat_hash_map<int, int>(
    {{1500, 1400}, {5120, 5020}, {9216, 9116}});

// Map of mtu to pyload length for packets that are expected to be
// dropped on egress out of port under test.
const auto* const kMtuDropPacketPayloadMap =
    new absl::flat_hash_map<int, int>({{1500, 1600}, {5120, 5220}});

void SetPortMtu(gnmi::gNMI::StubInterface* stub, absl::string_view intf,
                const std::string& mtu) {
  // Set mtu on port under test on SUT.
  LOG(INFO) << "Setting mtu to " << mtu << " on port: " << intf;
  auto mtu_json_val = absl::Substitute("{\"mtu\":$0}", mtu);
  const std::string if_enabled_config_path =
      absl::StrCat("interfaces/interface[name=", intf, "]/config/mtu");
  ASSERT_OK(SetGnmiConfigPath(stub, if_enabled_config_path,
                              GnmiSetType::kUpdate, mtu_json_val));
  absl::SleepFor(absl::Seconds(5));

  // Perform state path verifications.
  // Verify /interfaces/interface[name=<port>]/state/mtu = mtu.
  std::string if_state_path =
      absl::StrCat("interfaces/interface[name=", intf, "]/state/mtu");
  ASSERT_OK_AND_ASSIGN(
      std::string state_path_response,
      GetGnmiStatePathInfo(stub, if_state_path, kMtuRespParseStr));
  EXPECT_THAT(state_path_response, HasSubstr(mtu));
}

TEST_P(MtuRoutingTestFixture, MtuTest) {
  testbed_->Environment().SetTestCaseID("cfb97855-fe79-494a-aef2-92821aef3b1f");
  // Get original mtu on port under test on SUT.
  std::string if_state_path = absl::StrCat(
      "interfaces/interface[name=", destination_link_.sut_interface,
      "]/state/mtu");
  ASSERT_OK_AND_ASSIGN(
      std::string state_path_response,
      GetGnmiStatePathInfo(stub_.get(), if_state_path, kMtuRespParseStr));
  int orig_mtu;
  ASSERT_TRUE(absl::SimpleAtoi(state_path_response, &orig_mtu));

  // Set up a route between the source and destination interfaces.
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<pdpi::P4RuntimeSession> p4_session,
      pdpi::P4RuntimeSession::CreateWithP4InfoAndClearTables(
          testbed_->Sut(), MtuRoutingTestFixture::GetParam().p4_info));
  P4rtProgrammingContext p4rt_context(p4_session.get(),
                                      pdpi::SetMetadataAndSendPiWriteRequest);
  ASSERT_OK(SetupRoute(&p4rt_context));

  // Configure test mtu values on port under test on SUT.
  for (const auto& [mtu, payload_length] : *kMtuPacketPayloadMap) {
    // Set mtu.
    SetPortMtu(stub_.get(), destination_link_.sut_interface,
               std::to_string(mtu));
    // Send packets of size > mtu and expect them to be dropped by port
    // under test.
    // Since max mtu (9194) can not be changed on control switch for a
    // generic testbed, verifying using traffic for an expected drop case
    // is not performed in this case.
    if (mtu < kDefaultMtu) {
      auto it = kMtuDropPacketPayloadMap->find(mtu);
      ASSERT_NE(it, kMtuDropPacketPayloadMap->end());
      auto test_packet = GenerateTestPacket(
          basic_traffic::PortIdToIP(sut_destination_port_id_),
          /*payload_len*/ it->second);
      ASSERT_OK_AND_ASSIGN(
          auto pkts,
          SendTraffic(/*num_pkts*/ 50,
                      /*egress_port*/ source_link_.peer_interface,
                      /*ingress_port*/ destination_link_.peer_interface,
                      test_packet));
      EXPECT_EQ(pkts.received, 0);
    }
    // Send packets of size < mtu and expect packets to be routed out of
    // port under test.
    auto test_packet = GenerateTestPacket(
        basic_traffic::PortIdToIP(sut_destination_port_id_), payload_length);
    ASSERT_OK_AND_ASSIGN(
        auto pkts,
        SendTraffic(/*num_pkts*/ 50,
                    /*egress_port*/ source_link_.peer_interface,
                    /*ingress_port*/ destination_link_.peer_interface,
                    test_packet));
    EXPECT_EQ(pkts.received, 50);
  }

  // Restore original mtu values on port under test on SUT.
  SetPortMtu(stub_.get(), destination_link_.sut_interface,
             std::to_string(orig_mtu));
}
}  // namespace
}  // namespace pins_test
