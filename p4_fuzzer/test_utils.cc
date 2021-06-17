#include "p4_fuzzer/test_utils.h"

#include "absl/random/random.h"
#include "absl/status/status.h"
#include "absl/strings/substitute.h"
#include "gutil/testing.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_fuzzer/fuzz_util.h"
#include "p4_fuzzer/fuzzer_config.h"
#include "p4_fuzzer/switch_state.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "sai_p4/instantiations/google/sai_p4info.h"

namespace p4_fuzzer {
absl::StatusOr<pdpi::IrP4Info> ConstructIrInfo(
    const TestP4InfoOptions& options) {
  return pdpi::CreateIrP4Info(
      gutil::ParseProtoOrDie<p4::config::v1::P4Info>(absl::Substitute(
          R"pb(
            tables {
              preamble {
                id: $0
                name: "ingress.routing.wcmp_group_table"
                alias: "wcmp_group_table"
                annotations: "@p4runtime_role(\"sdn_controller\")"
                annotations: "@oneshot"
              }
              match_fields {
                id: $6
                name: "wcmp_group_id"
                match_type: $7
                type_name { name: "wcmp_group_id_t" }
              }
              action_refs { id: $1 annotations: "@proto_id(1)" }
              action_refs {
                id: $2
                annotations: "@defaultonly"
                scope: DEFAULT_ONLY
              }
              const_default_action_id: $2
              implementation_id: $3
              size: 4096
            }
            actions {
              preamble {
                id: $1
                name: "ingress.routing.set_nexthop_id"
                alias: "set_nexthop_id"
              }
              params {
                id: 1
                name: "nexthop_id"
                type_name { name: "nexthop_id_t" }
              }
            }
            actions { preamble { id: $2 name: "NoAction" alias: "NoAction" } }
            action_profiles {
              preamble {
                id: $3
                name: "ingress.routing.wcmp_group_selector"
                alias: "wcmp_group_selector"
              }
              table_ids: $0
              with_selector: true
              size: $4
              max_group_size: $5
            }
            type_info {
              new_types {
                key: "nexthop_id_t"
                value { translated_type { sdn_string {} } }
              }
              new_types {
                key: "wcmp_group_id_t"
                value { translated_type { sdn_string {} } }
              }
            }
          )pb",
          options.action_selector_table_id, options.action_id,
          options.action_no_op_id, options.action_profile_id,
          options.action_profile_size, options.action_profile_max_group_size,
          options.table_match_field_id, options.table_match_field_type)));
}

absl::StatusOr<FuzzerTestState> ConstructFuzzerTestState(
    const TestP4InfoOptions& options) {
  ASSIGN_OR_RETURN(const pdpi::IrP4Info ir_info, ConstructIrInfo(options));
  const FuzzerConfig config{
      .info = ir_info,
      .ports = {"1"},
      .qos_queues = {"0x1"},
      .role = "sdn_controller",
  };
  return FuzzerTestState{
      .config = config,
      .switch_state = SwitchState(ir_info),
  };
}

FuzzerTestState ConstructFuzzerTestStateFromSaiMiddleBlock() {
  auto ir_info = sai::GetIrP4Info(sai::Instantiation::kMiddleblock);
  const FuzzerConfig config{
      .info = ir_info,
      .ports = {"1"},
      .qos_queues = {"0x1"},
      .role = "sdn_controller",
  };
  auto fuzzer_state = FuzzerTestState{
      .config = config,
      .switch_state = SwitchState(ir_info),
  };
  return fuzzer_state;
}
}  // namespace p4_fuzzer
