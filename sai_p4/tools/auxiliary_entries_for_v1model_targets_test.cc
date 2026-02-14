#include "sai_p4/tools/auxiliary_entries_for_v1model_targets.h"

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto_matchers.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
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

  pdpi::IrEntities ir_entities;

  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities auxiliary_ir_entities,
      sai::CreateV1ModelAuxiliaryEntities(ir_entities, mock_gnmi_stub));
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
                           mock_gnmi_stub));

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

// TODO: Remove this test once auxiliary vlan membership entries
// are no longer generated for SUB_PORT RIFS.
TEST(AuxiliaryIrEntitiesForV1ModelTarget,
     GenerateAuxiliaryVlanMembershipTableForSubRifPortEntries) {
  gnmi::GetResponse response;
  *response.add_notification()
       ->add_update()
       ->mutable_val()
       ->mutable_json_ietf_val() = R"(
    {
      "openconfig-interfaces:interfaces": {
        "interface": [
        ]
      }
    })";

  gnmi::MockgNMIStub mock_gnmi_stub;
  EXPECT_CALL(mock_gnmi_stub, Get)
      .WillRepeatedly(
          DoAll(SetArgPointee<2>(response), Return(grpc::Status::OK)));

  ASSERT_OK_AND_ASSIGN(pdpi::IrEntities auxiliary_ir_entities,
                       sai::CreateV1ModelAuxiliaryEntities(
                           gutil::ParseProtoOrDie<pdpi::IrEntities>(
                               R"pb(
                                 entities {
                                   table_entry {
                                     table_name: "router_interface_table"
                                     action {
                                       name: "unicast_set_port_and_src_mac_and_vlan_id"
                                       params {
                                         name: "vlan_id"
                                         value { hex_str: "0x1" }
                                       }
                                       params {
                                         name: "port"
                                         value { str: "1" }
                                       }
                                     }
                                   }
                                 }
                               )pb"),
                           mock_gnmi_stub));

  EXPECT_THAT(auxiliary_ir_entities,
              gutil::EqualsProto(gutil::ParseProtoOrDie<pdpi::IrEntities>(
                  R"pb(
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
                  )pb")));
}

TEST(AuxiliaryIrEntitiesForV1ModelTarget,
     GeneratesAuxiliaryL3AdmitTableEntriesForRifs) {
  gnmi::GetResponse response;
  *response.add_notification()
       ->add_update()
       ->mutable_val()
       ->mutable_json_ietf_val() = R"(
    {
      "openconfig-interfaces:interfaces": {
        "interface": [
        ]
      }
    })";

  gnmi::MockgNMIStub mock_gnmi_stub;
  EXPECT_CALL(mock_gnmi_stub, Get)
      .WillRepeatedly(
          DoAll(SetArgPointee<2>(response), Return(grpc::Status::OK)));

  ASSERT_OK_AND_ASSIGN(
      const pdpi::IrEntities auxiliary_ir_entities,
      sai::CreateV1ModelAuxiliaryEntities(
          gutil::ParseProtoOrDie<pdpi::IrEntities>(
              R"pb(
                entities {
                  table_entry {
                    table_name: "router_interface_table"
                    matches {
                      name: "router_interface_id"
                      exact { str: "1" }
                    }
                    action {
                      name: "set_port_and_src_mac"
                      params {
                        name: "port"
                        value { str: "1" }
                      }
                      params {
                        name: "src_mac"
                        value { mac: "02:2a:10:00:00:03" }
                      }
                    }
                  }
                }
              )pb"),
          mock_gnmi_stub));

  EXPECT_THAT(auxiliary_ir_entities,
              gutil::EqualsProto(gutil::ParseProtoOrDie<pdpi::IrEntities>(
                  R"pb(
                    entities {
                      table_entry {
                        table_name: "l3_admit_table"
                        matches {
                          name: "in_port"
                          optional { value { str: "1" } }
                        }
                        matches {
                          name: "dst_mac"
                          ternary {
                            value { mac: "02:2a:10:00:00:03" }
                            mask { mac: "ff:ff:ff:ff:ff:ff" }
                          }
                        }
                        priority: 1
                        action { name: "admit_to_l3" }
                      }
                    }
                  )pb")));
}

}  // namespace

