#include "tests/forwarding/tor_protocol_test.h"
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "absl/log/log.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "dvaas/dataplane_validation.h"
#include "dvaas/test_vector.pb.h"
#include "dvaas/validation_result.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
#include "lib/p4rt/p4rt_port.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/p4_runtime_session_extras.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "sai_p4/instantiations/google/test_tools/test_entries.h"
#include "tests/lib/switch_test_setup_helpers.h"
#include "thinkit/mirror_testbed.h"

// Tests ToR-specific behavior for expected protocol packets.

namespace pins_test {
namespace {
using ::gutil::ParseProtoOrDie;

pdpi::IrEntities EntitiesRewritingVlan() {
  return ParseProtoOrDie<pdpi::IrEntities>(R"pb(
    # ARP VLAN rewrite
    entities {
      table_entry {
        table_name: "acl_pre_ingress_vlan_table"
        priority: 3000
        matches {
          name: "ether_type"
          ternary {
            value { hex_str: "0x0806" }
            mask { hex_str: "0xffff" }
          }
        }
        action {
          name: "set_outer_vlan_id"
          params {
            name: "vlan_id"
            value { hex_str: "0xfff" }  # Default VLAN
}
        }
      }
    }
    # IPv4 VLAN rewrite
    entities {
      table_entry {
        table_name: "acl_pre_ingress_vlan_table"
        priority: 3000
        matches {
          name: "is_ipv4"
          optional { value { hex_str: "0x1" } }
        }
        action {
          name: "set_outer_vlan_id"
          params {
            name: "vlan_id"
            value { hex_str: "0xfff" }
          }
        }
      }
    }
    # IPv6 VLAN rewrite
    entities {
      table_entry {
        table_name: "acl_pre_ingress_vlan_table"
        priority: 3000
        matches {
          name: "is_ipv6"
          optional { value { hex_str: "0x1" } }
        }
        action {
          name: "set_outer_vlan_id"
          params {
            name: "vlan_id"
            value { hex_str: "0xfff" }
          }
        }
      }
    }
  )pb");
}

pdpi::IrEntities BlockReceivedBroadcastEntities() {
  return ParseProtoOrDie<pdpi::IrEntities>(R"pb(
    # Allow Broadcasts packets from CPU port
    entities {
      table_entry {
        table_name: "acl_ingress_qos_table"
        matches {
name: "dst_mac"
          ternary {
            value { mac: "ff:ff:ff:ff:ff:ff" }
            mask { mac: "ff:ff:ff:ff:ff:ff" }
          }
        }
        matches {
          # CPU Ingress (OPENFLOW_PORT_CONTROLLER)
          name: "in_port"
          optional { value { str: "4294967293" } }
        }
        priority: 4021
        action { name: "acl_forward" }
      }
    }
    # Block Broadcasts from non-CPU port
    entities {
      table_entry {
        table_name: "acl_ingress_qos_table"
        matches {
          name: "dst_mac"
          ternary {
            value { mac: "ff:ff:ff:ff:ff:ff" }
            mask { mac: "ff:ff:ff:ff:ff:ff" }
          }
        }
        priority: 4020
        action { name: "acl_drop" }
      }
    }
  )pb");
}

pdpi::IrEntity EntryDirectingBroadcastPacketsToMulticastGroup1() {
  return ParseProtoOrDie<pdpi::IrEntity>(R"pb(
    table_entry {
      table_name: "acl_ingress_table"
      matches {
        name: "dst_mac"
        ternary {
          value { mac: "ff:ff:ff:ff:ff:ff" }
          mask { mac: "ff:ff:ff:ff:ff:ff" }
        }
      }
      matches {
        # Ingress from CPU port
        name: "in_port"
        optional { value { str: "4294967293" } }
      }
priority: 4021
      action {
        name: "redirect_to_l2mc_group"
        params {
          name: "multicast_group_id"
          value { hex_str: "0x0001" }
        }
      }
    }
  )pb");
}

const packetlib::Packet& ArpProbePacket() {
  const auto* const kPacket =
      new packetlib::Packet(ParseProtoOrDie<packetlib::Packet>(R"pb(
        headers {
          ethernet_header {
            ethernet_destination: "ff:ff:ff:ff:ff:ff"
            ethernet_source: "02:32:0a:f6:ad:de"
            ethertype: "0x0806"
          }
        }
        headers {
          arp_header {
            hardware_type: "0x0001"
            protocol_type: "0x0800"
            hardware_length: "0x06"
            protocol_length: "0x04"
            operation: "0x0001"
            sender_hardware_address: "02:32:0a:f6:ad:de"
            sender_protocol_address: "10.246.173.222"
            target_hardware_address: "ff:ff:ff:ff:ff:ff"  # Broadcast MAC
            target_protocol_address: "10.246.173.211"
          }
        }
        payload: "test packet #1: ARP Probe"
      )pb"));
  return *kPacket;
}

const packetlib::Packet& Ndv6NsPacket() {
  const auto* const kPacket =
      new packetlib::Packet(ParseProtoOrDie<packetlib::Packet>(R"pb(
        headers {
          ethernet_header {
            ethernet_destination: "ff:ff:ff:ff:ff:ff"
            ethernet_source: "02:32:00:00:00:00"
            ethertype: "0x86dd"
          }
        }
headers {
          ipv6_header {
            version: "0x6"
            dscp: "0x38"
            ecn: "0x0"
            flow_label: "0x00000"
            # payload_length: Auto Calculated
            next_header: "0x3a"
            hop_limit: "0xff"
            ipv6_source: "::"
            ipv6_destination: "ff02::1:ff00:0"
          }
        }
        headers {
          icmp_header {
            type: "0x87"
            code: "0x00"
            # checksum: Auto Calculated
            rest_of_header: "0x00000000"
          }
        }
        payload: "test packet #2: NDv6 NS"
      )pb"));
  return *kPacket;
}

const packetlib::Packet& VlanTaggedArpPacket() {
  const auto* const kPacket =
      new packetlib::Packet(ParseProtoOrDie<packetlib::Packet>(R"pb(
        headers {
          ethernet_header {
            ethernet_destination: "ff:ff:ff:ff:ff:ff"
            ethernet_source: "02:32:0a:f6:ad:de"
            ethertype: "0x8100"
          }
        }
        headers {
          vlan_header {
            priority_code_point: "0x0"
            drop_eligible_indicator: "0x0"
            vlan_identifier: "0x002"
            ethertype: "0x0806"
          }
        }
        headers {
          arp_header {
            hardware_type: "0x0001"
            protocol_type: "0x0800"
            hardware_length: "0x06"
            protocol_length: "0x04"
            operation: "0x0001"
sender_hardware_address: "02:32:0a:f6:ad:de"
            sender_protocol_address: "10.246.173.222"
            target_hardware_address: "ff:ff:ff:ff:ff:ff"
            target_protocol_address: "10.246.173.211"
          }
        }
        payload: "test packet #3: VLAN-Tagged ARP probe"
      )pb"));
  return *kPacket;
}

class MulticastGroupBuilder {
 public:
  explicit MulticastGroupBuilder(pdpi::IrP4Info ir_p4info, int group_id)
      : ir_p4info_(std::move(ir_p4info)), group_id_(group_id), index_(0) {}

  void AddPort(const pins_test::P4rtPortId& port_id) {
    entry_builder_.AddL2MrifEntry(port_id.GetP4rtEncoding(), ++index_);
    replicas_.push_back(
        {.egress_port = port_id.GetP4rtEncoding(), .instance = index_});
  }

  absl::StatusOr<pdpi::IrEntities> Entities() {
    return entry_builder_.AddMulticastGroupEntry(group_id_, replicas_)
        .GetDedupedIrEntities(ir_p4info_);
  }
  int MemberCount() const { return index_; }

 private:
  sai::EntryBuilder entry_builder_;
  pdpi::IrP4Info ir_p4info_;
  int group_id_;
  int index_;
  pdpi::IrEntities entities_;
  std::vector<sai::Replica> replicas_;
};

dvaas::PacketTestVector MulticastTestVector(
    const packetlib::Packet& packet, const packetlib::Packet& result_packet,
    const std::vector<MirroredPort>& multicast_ports) {
  dvaas::PacketTestVector test_vector;
  test_vector.mutable_input()->set_type(dvaas::SwitchInput::SUBMIT_TO_INGRESS);
  *test_vector.mutable_input()->mutable_packet()->mutable_parsed() = packet;
  dvaas::SwitchOutput& output = *test_vector.add_acceptable_outputs();
  for (const MirroredPort& port : multicast_ports) {
    dvaas::Packet& expected_packet = *output.add_packets();
    expected_packet.set_port(port.sut.GetP4rtEncoding());
    *expected_packet.mutable_parsed() = result_packet;
  }
  return test_vector;
}
}  // namespace

void TorProtocolTest::SetUp() {
  GetParam().testbed->SetUp();
  ASSERT_OK_AND_ASSIGN(ir_p4info_, pdpi::CreateIrP4Info(GetParam().sut.p4info));
  ASSERT_OK(pins_test::ConfigureSwitchPair(
      testbed().Sut(),
      {
          .gnmi_config = GetParam().sut.gnmi_config,
          .p4info = GetParam().sut.p4info,
      },
      testbed().ControlSwitch(),
      {
          .gnmi_config = GetParam().control_switch.gnmi_config,
          .p4info = GetParam().control_switch.p4info,
      }));
  ASSERT_OK_AND_ASSIGN(sut_p4rt_session_,
                       pdpi::P4RuntimeSession::Create(testbed().Sut()));
}

TEST_P(TorProtocolTest, Ndv6PacketsFromControllerAreMulticast) {

  // Set up entries.
  MulticastGroupBuilder mcast_builder(ir_p4info(), /*group_id=*/1);
  ASSERT_OK_AND_ASSIGN(std::vector<MirroredPort> mirrored_ports,
                       MirroredPorts(testbed()));
  ASSERT_THAT(mirrored_ports, testing::SizeIs(testing::Ge(4)));

  std::vector<MirroredPort> multicast_ports;
  multicast_ports.reserve(mirrored_ports.size() / 2);
  for (int i = 0; i < mirrored_ports.size(); i += 2) {
    mcast_builder.AddPort(mirrored_ports[i].sut);
    multicast_ports.push_back(mirrored_ports[i]);
  }
  ASSERT_OK_AND_ASSIGN(pdpi::IrEntities multicast_entities,
                       mcast_builder.Entities());
  *multicast_entities.add_entities() =
      EntryDirectingBroadcastPacketsToMulticastGroup1();
  multicast_entities.mutable_entities()->MergeFrom(
      BlockReceivedBroadcastEntities().entities());

  if (GetParam().rewrite_vlan) {
    LOG(INFO) << "Testing VLAN rewrite";
    multicast_entities.mutable_entities()->MergeFrom(
        EntitiesRewritingVlan().entities());
  }
  LOG(INFO) << "Installing forwarding entities";
 ASSERT_OK(pdpi::InstallIrEntities(sut_p4rt_session(), multicast_entities));

  dvaas::DataplaneValidationParams dvaas_params = GetParam().dvaas_params;
  dvaas_params.packet_test_vector_override = {
      MulticastTestVector(ArpProbePacket(), ArpProbePacket(), multicast_ports),
      MulticastTestVector(Ndv6NsPacket(), Ndv6NsPacket(), multicast_ports),
  };

  if (GetParam().rewrite_vlan) {
    // Expect the vlan tag to be removed.
    packetlib::Packet expected = ArpProbePacket();
    *expected.mutable_payload() = VlanTaggedArpPacket().payload();
    dvaas_params.packet_test_vector_override.push_back(
        MulticastTestVector(VlanTaggedArpPacket(), expected, multicast_ports));
  }

  ASSERT_OK_AND_ASSIGN(
      dvaas::ValidationResult validation_result,
      GetParam().dvaas->ValidateDataplane(testbed(), dvaas_params));
  validation_result.LogStatistics();
  EXPECT_OK(validation_result.HasSuccessRateOfAtLeast(1));
}

}  // namespace pins_test

