#include "dvaas/failure_post_processing.h"

#include <string>
#include <vector>

#include "absl/status/statusor.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/proto.h"
#include "gutil/proto_matchers.h"
#include "gutil/status_matchers.h"  // IWYU pragma: keep
#include "gutil/testing.h"

namespace dvaas {
namespace {

using ::gutil::EqualsProto;
using ::gutil::IsEmptyProto;
using ::testing::UnorderedPointwise;
using ::testing::ValuesIn;

class DoEntityMinimizationTest
    : public testing::TestWithParam<MinimizationAlgorithm> {
 public:
  void SetEntitiesOnSwitch(const pdpi::IrEntities& entities) {
    entities_on_switch_ = entities;
  }

  const pdpi::IrEntities& GetEntitiesOnSwitch() { return entities_on_switch_; }

  void DeleteEntitiesFromSwitch(const pdpi::IrEntities& entities_to_delete) {
    // Remove `entities_to_delete` from `entities_on_switch_`.
    for (int i = entities_on_switch_.entities_size() - 1; i >= 0; --i) {
      for (const auto& ir_entity : entities_to_delete.entities()) {
        if (gutil::ProtoEqual(ir_entity, entities_on_switch_.entities(i))) {
          entities_on_switch_.mutable_entities()->DeleteSubrange(i, 1);
          break;
        }
      }
    }
  }

 private:
  pdpi::IrEntities entities_on_switch_;
};

std::vector<MinimizationAlgorithm> GetMinimizationParams() {
  return {
      kRemoveEntitiesOneByOne,
      kTableBasedBisection,
  };
}

TEST_P(DoEntityMinimizationTest, EntityCanNeverBeRemoved) {
  pdpi::IrEntities entities_to_minimize =
      gutil::ParseProtoOrDie<pdpi::IrEntities>(R"pb(
        entities {
          table_entry {
            table_name: "egress_port_loopback_table_1"
            matches {
              name: "out_port"
              exact { str: "1" }
            }
            action { name: "egress_loopback" }
          }
        }
        entities {
          table_entry {
            table_name: "egress_port_loopback_table_2"
            matches {
              name: "out_port"
              exact { str: "2" }
            }
            action { name: "egress_loopback" }
          }
        }
        entities {
          packet_replication_engine_entry {
            multicast_group_entry { multicast_group_id: 7 }
          }
        }
      )pb");
  SetEntitiesOnSwitch(entities_to_minimize);
  const pdpi::IrEntities expected_entities = entities_to_minimize;
  ASSERT_OK(dvaas::DoEntityMinimization(
      /*test_if_entities_can_be_removed=*/
      [](const pdpi::IrEntities& entities) -> absl::StatusOr<bool> {
        return false;
      },
      entities_to_minimize, GetParam()));
  EXPECT_THAT(GetEntitiesOnSwitch(), EqualsProto(expected_entities));
}

TEST_P(DoEntityMinimizationTest, EntityCanAlwaysBeRemoved) {
  pdpi::IrEntities entities_to_minimize;
  ASSERT_OK(dvaas::DoEntityMinimization(
      /*test_if_entities_can_be_removed=*/
      [this](const pdpi::IrEntities& entities) -> absl::StatusOr<bool> {
        DeleteEntitiesFromSwitch(entities);
        return true;
      },
      entities_to_minimize, GetParam()));
  EXPECT_TRUE(IsEmptyProto(GetEntitiesOnSwitch()));
}

TEST_P(DoEntityMinimizationTest,
       EveryOtherEntityCanBeRemovedWithEvenNumberOfEntities) {
  pdpi::IrEntities entities_to_minimize =
      gutil::ParseProtoOrDie<pdpi::IrEntities>(R"pb(
        entities {
          table_entry {
            table_name: "egress_port_loopback_table"
            matches {
              name: "out_port"
              exact { str: "1" }
            }
            action { name: "egress_loopback" }
          }
        }
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
              exact { str: "3" }
            }
            action { name: "egress_loopback" }
          }
        }
        entities {
          table_entry {
            table_name: "egress_port_loopback_table"
            matches {
              name: "out_port"
              exact { str: "4" }
            }
            action { name: "egress_loopback" }
          }
        }
      )pb");
  SetEntitiesOnSwitch(entities_to_minimize);
  auto test_if_entities_can_be_removed =
      [this](const pdpi::IrEntities& entities) -> absl::StatusOr<bool> {
    bool can_be_removed = true;
    for (const auto& entity : entities.entities()) {
      int port = std::stoi(entity.table_entry().matches().at(0).exact().str());
      if (port % 2 == 0) {
        can_be_removed = false;
        break;
      }
    }
    if (!can_be_removed) return false;
    DeleteEntitiesFromSwitch(entities);
    return true;
  };
  ASSERT_OK(dvaas::DoEntityMinimization(test_if_entities_can_be_removed,
                                        entities_to_minimize, GetParam()));
  EXPECT_THAT(GetEntitiesOnSwitch().entities(),
              UnorderedPointwise(EqualsProto(),
                                 gutil::ParseProtoOrDie<pdpi::IrEntities>(R"pb(
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
                                         exact { str: "4" }
                                       }
                                       action { name: "egress_loopback" }
                                     }
                                   }
                                 )pb")
                                     .entities()));
}

TEST_P(DoEntityMinimizationTest,
       EveryOtherEntityCanBeRemovedWithOddNumberOfEntities) {
  pdpi::IrEntities entities_to_minimize =
      gutil::ParseProtoOrDie<pdpi::IrEntities>(R"pb(
        entities {
          table_entry {
            table_name: "egress_port_loopback_table"
            matches {
              name: "out_port"
              exact { str: "1" }
            }
            action { name: "egress_loopback" }
          }
        }
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
              exact { str: "3" }
            }
            action { name: "egress_loopback" }
          }
        }
        entities {
          table_entry {
            table_name: "egress_port_loopback_table"
            matches {
              name: "out_port"
              exact { str: "4" }
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
  SetEntitiesOnSwitch(entities_to_minimize);
  auto test_if_entities_can_be_removed =
      [this](const pdpi::IrEntities& entities) -> absl::StatusOr<bool> {
    bool can_be_removed = true;
    for (const auto& entity : entities.entities()) {
      int port = std::stoi(entity.table_entry().matches().at(0).exact().str());
      if (port % 2 == 0) {
        can_be_removed = false;
        break;
      }
    }
    if (!can_be_removed) return false;
    for (const auto& entity : entities.entities()) {
      int port = std::stoi(entity.table_entry().matches().at(0).exact().str());
      if (port % 2 != 0) {
        DeleteEntitiesFromSwitch(entities);
      }
    }
    return true;
  };
  ASSERT_OK(dvaas::DoEntityMinimization(test_if_entities_can_be_removed,
                                        entities_to_minimize, GetParam()));
  EXPECT_THAT(GetEntitiesOnSwitch().entities(),
              UnorderedPointwise(EqualsProto(),
                                 gutil::ParseProtoOrDie<pdpi::IrEntities>(R"pb(
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
                                         exact { str: "4" }
                                       }
                                       action { name: "egress_loopback" }
                                     }
                                   }
                                 )pb")
                                     .entities()));
}

TEST_P(DoEntityMinimizationTest, MinimizationsStartsFromLastTable) {
  pdpi::IrEntities entities_to_minimize =
      gutil::ParseProtoOrDie<pdpi::IrEntities>(R"pb(
        entities {
          table_entry {
            table_name: "egress_port_loopback_table_1"
            matches {
              name: "out_port"
              exact { str: "1" }
            }
            action { name: "egress_loopback" }
          }
        }
        entities {
          table_entry {
            table_name: "egress_port_loopback_table_3"
            matches {
              name: "out_port"
              exact { str: "3" }
            }
            action { name: "egress_loopback" }
          }
        }
        # Delete the last and only entity in the table.
        entities {
          table_entry {
            table_name: "egress_port_loopback_table_2"
            matches {
              name: "out_port"
              exact { str: "2" }
            }
            action { name: "egress_loopback" }
          }
        }
      )pb");
  SetEntitiesOnSwitch(entities_to_minimize);
  bool deleted_first_entity = false;
  auto test_if_entities_can_be_removed =
      [this, &deleted_first_entity](
          const pdpi::IrEntities& entities) -> absl::StatusOr<bool> {
    if (deleted_first_entity) return false;
    if (entities.entities_size() == 1) {
      deleted_first_entity = true;
      DeleteEntitiesFromSwitch(entities);
      return true;
    }
    return false;
  };
  ASSERT_OK(dvaas::DoEntityMinimization(test_if_entities_can_be_removed,
                                        entities_to_minimize, GetParam()));
  EXPECT_THAT(
      GetEntitiesOnSwitch().entities(),
      UnorderedPointwise(EqualsProto(),
                         gutil::ParseProtoOrDie<pdpi::IrEntities>(R"pb(
                           entities {
                             table_entry {
                               table_name: "egress_port_loopback_table_1"
                               matches {
                                 name: "out_port"
                                 exact { str: "1" }
                               }
                               action { name: "egress_loopback" }
                             }
                           }
                           entities {
                             table_entry {
                               table_name: "egress_port_loopback_table_3"
                               matches {
                                 name: "out_port"
                                 exact { str: "3" }
                               }
                               action { name: "egress_loopback" }
                             }
                           }
                         )pb")
                             .entities()));
}

TEST_P(DoEntityMinimizationTest, NoEntitiesToMinimizeWorks) {
  pdpi::IrEntities entities_to_minimize;
  ASSERT_OK(dvaas::DoEntityMinimization(
      /*test_if_entities_can_be_removed=*/
      [this](const pdpi::IrEntities& entities) -> absl::StatusOr<bool> {
        DeleteEntitiesFromSwitch(entities);
        return true;
      },
      entities_to_minimize, GetParam()));
  EXPECT_THAT(GetEntitiesOnSwitch(), EqualsProto(entities_to_minimize));
}

TEST_P(DoEntityMinimizationTest,
       OneEntityCannotBeRemovedFromAnOddNumberOfEntities) {
  pdpi::IrEntities entities_to_minimize =
      gutil::ParseProtoOrDie<pdpi::IrEntities>(R"pb(
        entities {
          table_entry {
            table_name: "egress_port_loopback_table_1"
            matches {
              name: "out_port"
              exact { str: "1" }
            }
            action { name: "egress_loopback" }
          }
        }
        entities {
          table_entry {
            table_name: "egress_port_loopback_table_2"
            matches {
              name: "out_port"
              exact { str: "2" }
            }
            action { name: "egress_loopback" }
          }
        }
        entities {
          packet_replication_engine_entry {
            multicast_group_entry { multicast_group_id: 7 }
          }
        }
      )pb");
  SetEntitiesOnSwitch(entities_to_minimize);
  const pdpi::IrEntities expected_entities = entities_to_minimize;
  ASSERT_OK(dvaas::DoEntityMinimization(
      /*test_if_entities_can_be_removed=*/
      [this](const pdpi::IrEntities& entities) -> absl::StatusOr<bool> {
        for (const pdpi::IrEntity& entity : entities.entities()) {
          if (entity.has_packet_replication_engine_entry()) {
            return false;
          }
        }
        DeleteEntitiesFromSwitch(entities);
        return true;
      },
      entities_to_minimize, GetParam()));
  EXPECT_THAT(GetEntitiesOnSwitch(),
              EqualsProto(gutil::ParseProtoOrDie<pdpi::IrEntities>(R"pb(
                entities {
                  packet_replication_engine_entry {
                    multicast_group_entry { multicast_group_id: 7 }
                  }
                }
              )pb")));
}

TEST(HasSameFailureTest, HasSameFailureWorks) {
  PacketTestOutcome original_test_outcome = gutil::ParseProtoOrDie<
      PacketTestOutcome>(R"pb(
    test_result { failure { description: "Test failed" } }
    test_run {
      labels { labels: "label1" }
      input_packet_injection_time: "1"
      test_vector {
        input {
          type: DATAPLANE
          packet {
            port: "29"
            parsed { payload: "test packet #1: Dummy payload" }
            hex: "021a0ad0628b3647086f88a186dd668000000025112020000000000000000000000000000000280003f0c20008000000000000002000000003ea0025371274657374207061636b65742023313a2044756d6d79207061796c6f6164"
          }
        }
        acceptable_outputs {
          packets { port: "1" }
          packets { port: "2" }
          packet_ins { hex: "1" }
          packet_ins { hex: "2" }
        }
        acceptable_outputs {
          packet_trace {
            events { packet_replication { number_of_packets_replicated: 1 } }
          }
        }
      }
    }
  )pb");
  PacketTestOutcome new_test_outcome = original_test_outcome;
  // Reset/clear the values of ignored fields.
  new_test_outcome.mutable_test_run()->mutable_labels()->set_labels(0,
                                                                    "label2");
  new_test_outcome.mutable_test_run()->set_input_packet_injection_time("2");
  new_test_outcome.mutable_test_run()
      ->mutable_test_vector()
      ->mutable_acceptable_outputs(1)
      ->clear_packet_trace();

  // Swap the first and second packet.
  dvaas::Packet packet =
      new_test_outcome.test_run().test_vector().acceptable_outputs(0).packets(
          0);
  *new_test_outcome.mutable_test_run()
       ->mutable_test_vector()
       ->mutable_acceptable_outputs(0)
       ->mutable_packets(0) =
      new_test_outcome.test_run().test_vector().acceptable_outputs(0).packets(
          1);
  *new_test_outcome.mutable_test_run()
       ->mutable_test_vector()
       ->mutable_acceptable_outputs(0)
       ->mutable_packets(1) = packet;

  // Swap the first and second packet_ins.
  dvaas::PacketIn packet_in = new_test_outcome.test_run()
                                  .test_vector()
                                  .acceptable_outputs(0)
                                  .packet_ins(0);
  *new_test_outcome.mutable_test_run()
       ->mutable_test_vector()
       ->mutable_acceptable_outputs(0)
       ->mutable_packet_ins(0) = new_test_outcome.test_run()
                                     .test_vector()
                                     .acceptable_outputs(0)
                                     .packet_ins(1);
  *new_test_outcome.mutable_test_run()
       ->mutable_test_vector()
       ->mutable_acceptable_outputs(0)
       ->mutable_packet_ins(1) = packet_in;

  // Swap the first and second acceptable_outputs.
  dvaas::SwitchOutput acceptable_output =
      new_test_outcome.test_run().test_vector().acceptable_outputs(0);
  *new_test_outcome.mutable_test_run()
       ->mutable_test_vector()
       ->mutable_acceptable_outputs(0) =
      new_test_outcome.test_run().test_vector().acceptable_outputs(1);
  *new_test_outcome.mutable_test_run()
       ->mutable_test_vector()
       ->mutable_acceptable_outputs(1) = acceptable_output;

  EXPECT_TRUE(HasSameFailure(original_test_outcome, new_test_outcome));
}

INSTANTIATE_TEST_SUITE_P(INSTANTIATE_TEST_SUITE_P, DoEntityMinimizationTest,
                         ValuesIn(GetMinimizationParams()));

}  // namespace
}  // namespace dvaas

