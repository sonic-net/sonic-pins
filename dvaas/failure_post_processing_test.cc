#include "dvaas/failure_post_processing.h"

#include "absl/status/statusor.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/proto_matchers.h"
#include "gutil/gutil/status_matchers.h"  // IWYU pragma: keep
#include "gutil/gutil/testing.h"

namespace dvaas {
namespace {

using ::gutil::EqualsProto;
using ::gutil::IsEmptyProto;

TEST(EntityMinimizationLoopTest, EntityCanNeverBeRemoved) {
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
          packet_replication_engine_entry {
            multicast_group_entry { multicast_group_id: 7 }
          }
        }
      )pb");
  const pdpi::IrEntities expected_entities = entities_to_minimize;
  ASSERT_OK(dvaas::EntityMinimizationLoop(
      /*test_if_entity_can_be_removed=*/
      [](const pdpi::IrEntity& entity_to_remove,
         const pdpi::IrEntities& current_entities) -> absl::StatusOr<bool> {
        return false;
      },
      entities_to_minimize));
  EXPECT_THAT(entities_to_minimize, EqualsProto(expected_entities));
}

TEST(EntityMinimizationLoopTest, EntityCanAlwaysBeRemoved) {
  pdpi::IrEntities entities_to_minimize;
  ASSERT_OK(dvaas::EntityMinimizationLoop(
      /*test_if_entity_can_be_removed=*/
      [](const pdpi::IrEntity& entity_to_remove,
         const pdpi::IrEntities& current_entities) -> absl::StatusOr<bool> {
        return true;
      },
      entities_to_minimize));
  EXPECT_TRUE(IsEmptyProto(entities_to_minimize));
}

TEST(EntityMinimizationLoopTest, EveryOtherEntityCanBeRemoved) {
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
  bool turn = true;
  ASSERT_OK(dvaas::EntityMinimizationLoop(
      /*test_if_entity_can_be_removed=*/
      [&turn](
          const pdpi::IrEntity& entity_to_remove,
          const pdpi::IrEntities& current_entities) -> absl::StatusOr<bool> {
        turn = !turn;
        return turn;
      },
      entities_to_minimize));
  EXPECT_THAT(entities_to_minimize,
              EqualsProto(gutil::ParseProtoOrDie<pdpi::IrEntities>(R"pb(
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
                      exact { str: "2" }
                    }
                    action { name: "egress_loopback" }
                  }
                }
              )pb")));
}

}  // namespace
}  // namespace dvaas
