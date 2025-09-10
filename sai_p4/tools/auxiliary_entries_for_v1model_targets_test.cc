#include "sai_p4/tools/auxiliary_entries_for_v1model_targets.h"

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/proto_matchers.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "proto/gnmi/gnmi_mock.grpc.pb.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"

namespace {

using testing::DoAll;
using testing::Return;
using testing::SetArgPointee;

TEST(AuxiliaryIrEntitiesForV1ModelTarget, GenerateAuxiliaryLoopbackEntities) {
  gnmi::GetResponse response;
  *response.add_notification()
       ->add_update()
       ->mutable_val()
       ->mutable_json_ietf_val() = R"(
    {
      "openconfig-interfaces:interfaces": {
        "interface": [
          {
            "name":"EthernetEnabled0",
            "state":{
              "loopback-mode":"ASIC_MAC_LOCAL",
              "openconfig-p4rt:id": 2
            }
          },
          {
            "name":"EthernetEnabled1",
            "state":{
              "loopback-mode":"NOT_ASIC_MAC_LOCAL",
              "openconfig-p4rt:id": 4
            }
          },
          {
            "name":"EthernetEnabled2",
            "state":{
              "loopback-mode":"ASIC_MAC_LOCAL",
              "openconfig-p4rt:id": 5
            }
          },
          {
            "name":"EthernetEnabled3",
            "state":{
              "loopback-mode":"NONE",
              "openconfig-p4rt:id": 6
            }
          },
          {
            "name":"EthernetEnabled4",
            "state":{
              "openconfig-p4rt:id": 7
            }
          }
        ]
      }
    })";

  auto expected_entities = gutil::ParseProtoOrDie<pdpi::IrEntities>(
      R"pb(
        entities {
          table_entry {
            table_name: "egress_port_loopback_table"
            matches {
              name: "out_port"
              exact { str: "2" }
            }
            action { name: "egress_loopback" }
          }
        }
        entities {
          table_entry {
            table_name: "egress_port_loopback_table"
            matches {
              name: "out_port"
              exact { str: "5" }
            }
            action { name: "egress_loopback" }
          }
        }
      )pb");

  gnmi::MockgNMIStub mock_gnmi_stub;
  EXPECT_CALL(mock_gnmi_stub, Get)
      .WillRepeatedly(
          DoAll(SetArgPointee<2>(response), Return(grpc::Status::OK)));

  pdpi::IrP4Info ir_p4info = sai::GetIrP4Info(sai::Instantiation::kTor);
  pdpi::IrEntities ir_entities;

  ASSERT_OK_AND_ASSIGN(pdpi::IrEntities auxiliary_ir_entities,
                       sai::CreateV1ModelAuxiliaryEntities(
                           ir_entities, mock_gnmi_stub, ir_p4info));
  EXPECT_THAT(auxiliary_ir_entities, gutil::EqualsProto(expected_entities));
}

TEST(AuxiliaryIrEntitiesForV1ModelTarget,
     GenerateAuxiliaryVlanMembershipTableEntries) {
  gnmi::GetResponse response;
  *response.add_notification()
       ->add_update()
       ->mutable_val()
       ->mutable_json_ietf_val() = R"(
    {
      "openconfig-interfaces:interfaces": {
        "interface": [
          {
            "name":"EthernetEnabled0",
            "state":{
              "loopback-mode":"ASIC_MAC_LOCAL",
              "openconfig-p4rt:id": 2
            }
          }
        ]
      }
    })";

  gnmi::MockgNMIStub mock_gnmi_stub;
  EXPECT_CALL(mock_gnmi_stub, Get)
      .WillRepeatedly(
          DoAll(SetArgPointee<2>(response), Return(grpc::Status::OK)));

  pdpi::IrP4Info ir_p4info = sai::GetIrP4Info(sai::Instantiation::kTor);

  ASSERT_OK_AND_ASSIGN(pdpi::IrEntities auxiliary_ir_entities,
                       sai::CreateV1ModelAuxiliaryEntities(
                           gutil::ParseProtoOrDie<pdpi::IrEntities>(
                               R"pb(
                                 entities {
                                   table_entry {
                                     table_name: "vlan_membership_table"
                                     matches {
                                       name: "vlan_id"
                                       exact { hex_str: "0x1" }
                                     }
                                     matches {
                                       name: "port"
                                       exact { str: "1" }
                                     }
                                     action { name: "make_tagged_member" }
                                   }
                                 }
                                 entities {
                                   table_entry {
                                     table_name: "vlan_membership_table"
                                     matches {
                                       name: "vlan_id"
                                       exact { hex_str: "0x2" }
                                     }
                                     matches {
                                       name: "port"
                                       exact { str: "2" }
                                     }
                                     action { name: "make_untagged_member" }
                                   }
                                 }
                               )pb"),
                           mock_gnmi_stub, ir_p4info));

  EXPECT_THAT(
      auxiliary_ir_entities,
      gutil::EqualsProto(gutil::ParseProtoOrDie<pdpi::IrEntities>(
          R"pb(
            entities {
              table_entry {
                table_name: "egress_port_loopback_table"
                matches {
                  name: "out_port"
                  exact { str: "2" }
                }
                action { name: "egress_loopback" }
              }
            }
            entities {
              table_entry {
                table_name: "v1model_auxiliary_vlan_membership_table"
                matches {
                  name: "vlan_id"
                  exact { hex_str: "0x1" }
                }
                matches {
                  name: "port"
                  exact { str: "1" }
                }
                action { name: "v1model_auxiliary_make_tagged_member" }
              }
            }
            entities {
              table_entry {
                table_name: "v1model_auxiliary_vlan_membership_table"
                matches {
                  name: "vlan_id"
                  exact { hex_str: "0x2" }
                }
                matches {
                  name: "port"
                  exact { str: "2" }
                }
                action { name: "v1model_auxiliary_make_untagged_member" }
              }
            }
          )pb")));
}

}  // namespace

