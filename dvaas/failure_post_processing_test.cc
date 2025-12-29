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

TEST(EntityMinimizationLoopTest, HasSameFailureWorks) {
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

}  // namespace
}  // namespace dvaas
