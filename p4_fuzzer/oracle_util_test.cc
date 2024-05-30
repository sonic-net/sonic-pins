#include "p4_fuzzer/oracle_util.h"

#include <utility>

#include "absl/status/status.h"
#include "devtools/build/runtime/get_runfiles_dir.h"
#include "file/base/helpers.h"
#include "file/base/options.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status.h"
#include "net/google::protobuf/contrib/parse_proto/parse_text_proto.h"
#include "platforms/networking/orion/core/sfe/sfe.pb.h"
#include "util/task/canonical_errors.h"

namespace switchstack {
namespace testing {
namespace hercules {
namespace {

using ::absl::StatusCode;
using ::google::protobuf::contrib::parse_proto::ParseTextProtoOrDie;
using ::orion::core::sfe::P4Entity;
using ::orion::core::sfe::P4Update;
using ::orion::p4::test::PdToPiUpdate;
using ::p4::v1::Update;
using ::p4::v1::WriteRequest;
using ::testing::Not;
using ::testing::status::IsOk;

constexpr char kDecapFlow[] = R"(
type: INSERT
entity {
  flow_entry {
    priority: 900
    table_entry {
      decap_table_entry {
        match {
          hdr_ethernet_ether_type {
            mask: 0xffff
            value: 2048
          }
          hdr_ipv4_base_src_addr {
            mask: 4294967295
            value: 1869573999
          }
          hdr_ipv4_base_dst_addr {
            mask: 4294967295
            value: 170408329
          }
        }
        action {
          ip_decap {
          }
        }
      }
    }
  }
}
)";

util::Status CheckWellformed(P4Update pd) {
  ASSIGN_OR_RETURN(Update pi, PdToPiUpdate(pd));
  return IsWellformedUpdate(pi);
}

TEST(OracleUtilTest, IsWellformedUpdate) {
  // Starting with PD because it's easier to read and write.
  P4Update pd = ParseTextProtoOrDie(kDecapFlow);

  // Regular update is fine
  EXPECT_OK(CheckWellformed(pd));

  // Wrong eth type (but still matching on IPv4 fields)
  pd.mutable_entity()
      ->mutable_flow_entry()
      ->mutable_table_entry()
      ->mutable_decap_table_entry()
      ->mutable_match()
      ->mutable_hdr_ethernet_ether_type()
      ->set_value(1234);
  EXPECT_THAT(CheckWellformed(pd), Not(IsOk()));

  // Missing eth_type (but still matching on IPv4 fields)
  pd.mutable_entity()
      ->mutable_flow_entry()
      ->mutable_table_entry()
      ->mutable_decap_table_entry()
      ->mutable_match()
      ->clear_hdr_ethernet_ether_type();
  EXPECT_THAT(CheckWellformed(pd), Not(IsOk()));
}

TEST(OracleUtilTest, IsWellformedLackOfPriority) {
  P4Update pd = ParseTextProtoOrDie(R"(
    type: INSERT
    entity {
      flow_entry {
        priority: 0
        cookie: 9223372036855300096
        table_entry {
          punt_table_entry {
            match {
              hdr_ethernet_ether_type { mask: 65535 value: 34525 }
              hdr_ipv6_base_dst_addr {
                mask: "\377\377\377\377\377\377\377\377\000\000\000\000\000\000\000\000"
                value: "&\007\370\260\321\001P\004\000\000\000\000\000\000\000\000"
              }
            }
            action { set_queue_and_send_to_cpu { queue_id: 2 } }
          }
        }
        meter_config { cir: 28672 cburst: 57344 pir: 28672 pburst: 57344 }
      }
    }
  )");

  // Priority cannot be 0 if there are ternary matches
  EXPECT_THAT(CheckWellformed(pd), Not(IsOk()));
}

constexpr char kVrfClassifierFlow[] = R"(
flow_entry {
  priority: 1134
  cookie: 9223372036854841344
  table_entry {
    vrf_classifier_table_entry {
      match {
        hdr_ethernet_ether_type {
          mask: 65535
          value: 2048
        }
        standard_metadata_ingress_port {
          mask: 4294967295
          value: 1025
        }
      }
      action {
        set_vrf {
          vrf_id: 117
        }
      }
    }
  }
}
)";

SwitchState EmptyState() { return {}; }

// Add a flow to a state.
void AddFlow(const P4Entity& flow, SwitchState* state) {
  P4Update update;
  update.set_type(orion::core::sfe::P4Update::INSERT);
  *update.mutable_entity() = flow;
  CHECK_OK(state->ApplyUpdate(PdToPiUpdate(update).value()));
}

// Get a VRF classifier flow (n can be varied to get different flows).
P4Entity GetVrfClassifierFlow(int n) {
  P4Entity flow = ParseTextProtoOrDie(kVrfClassifierFlow);
  flow.mutable_flow_entry()
      ->mutable_table_entry()
      ->mutable_vrf_classifier_table_entry()
      ->mutable_match()
      ->mutable_hdr_ethernet_ether_type()
      ->set_value(n);
  return flow;
}

// An update and it's corresponding status.
struct PdUpdateStatus {
  P4Update update;
  StatusCode status;
};

// Checks whether the update+state combo is plausible or not
util::Status Check(const std::vector<PdUpdateStatus>& updates,
                   const SwitchState& state, bool valid) {
  WriteRequest request;
  std::vector<::p4::v1::Error> statuses;
  for (const auto& update : updates) {
    ASSIGN_OR_RETURN(Update pi, PdToPiUpdate(update.update));
    *request.add_updates() = pi;
    ::p4::v1::Error status;
    status.set_canonical_code(static_cast<int32>(update.status));
    statuses.push_back(status);
  }
  absl::optional<std::vector<std::string>> oracle =
      WriteRequestOracle(request, statuses, state);
  if (valid) {
    if (oracle.has_value()) {
      std::string explanation = absl::StrCat(
          "Expected the write request and statuses to be a valid combination, "
          "but they are not.",
          "\n", "errors reported:");
      for (const auto& error : oracle.value()) {
        explanation += absl::StrCat("\n", error);
      }
      return util::InvalidArgumentError(explanation);
    }
  } else {
    if (!oracle.has_value()) {
      return util::InvalidArgumentError(
          "Expected the write request and statuses to not be a valid "
          "combination, "
          "but they are according to the oracle.");
    }
  }
  return util::OkStatus();
}

PdUpdateStatus MakeInsert(const P4Entity& entity, StatusCode status) {
  P4Update update;
  update.set_type(orion::core::sfe::P4Update::INSERT);
  *update.mutable_entity() = entity;
  return {update, status};
}

PdUpdateStatus MakeDelete(const P4Entity& entity, StatusCode status) {
  P4Update update;
  update.set_type(orion::core::sfe::P4Update::DELETE);
  *update.mutable_entity() = entity;
  return {update, status};
}

TEST(OracleUtilTest, BatchInsertDelete) {
  P4Entity flow = ParseTextProtoOrDie(kVrfClassifierFlow);

  // Insert/delete is fine in either order.
  EXPECT_OK(Check(
      {MakeInsert(flow, StatusCode::kOk), MakeDelete(flow, StatusCode::kOk)},
      EmptyState(), /*valid=*/true));
  EXPECT_OK(Check(
      {MakeDelete(flow, StatusCode::kOk), MakeInsert(flow, StatusCode::kOk)},
      EmptyState(), /*valid=*/true));

  // It is also fine for the delete to fail (in either order).
  EXPECT_OK(Check({MakeDelete(flow, StatusCode::kNotFound),
                   MakeInsert(flow, StatusCode::kOk)},
                  EmptyState(), /*valid=*/true));
  EXPECT_OK(Check({MakeInsert(flow, StatusCode::kOk),
                   MakeDelete(flow, StatusCode::kNotFound)},
                  EmptyState(), /*valid=*/true));
}

TEST(OracleUtilTest, BatchDoubleInsert) {
  P4Entity flow = ParseTextProtoOrDie(kVrfClassifierFlow);

  // Double insert is not okay.
  EXPECT_OK(Check(
      {MakeInsert(flow, StatusCode::kOk), MakeInsert(flow, StatusCode::kOk)},
      EmptyState(), /*valid=*/false));

  // If one is rejected, it's fine.
  EXPECT_OK(Check({MakeInsert(flow, StatusCode::kAlreadyExists),
                   MakeInsert(flow, StatusCode::kOk)},
                  EmptyState(), /*valid=*/true));
  EXPECT_OK(Check({MakeInsert(flow, StatusCode::kOk),
                   MakeInsert(flow, StatusCode::kAlreadyExists)},
                  EmptyState(), /*valid=*/true));
}

TEST(OracleUtilTest, BatchResources) {
  // Create a state that's full.
  SwitchState full;
  for (int i = 1; i <= 512; i++) {
    AddFlow(GetVrfClassifierFlow(i), &full);
  }

  P4Entity new_flow = GetVrfClassifierFlow(513);

  // Inserting into full table is okay.
  EXPECT_OK(
      Check({MakeInsert(new_flow, StatusCode::kOk)}, full, /*valid=*/true));

  // Resource exhasted is okay too.
  EXPECT_OK(Check({MakeInsert(new_flow, StatusCode::kResourceExhausted)}, full,
                  /*valid=*/true));
}

TEST(OracleUtilTest, BatchResourcesAlmostFull) {
  // Create a state that's almost full (1 entry remaining).
  SwitchState almost_full;
  for (int i = 1; i <= 511; i++) {
    AddFlow(GetVrfClassifierFlow(i), &almost_full);
  }

  P4Entity new_flow1 = GetVrfClassifierFlow(513);
  P4Entity new_flow2 = GetVrfClassifierFlow(514);

  // Resource exhasted is not okay.
  EXPECT_OK(Check({MakeInsert(new_flow1, StatusCode::kResourceExhausted)},
                  almost_full, /*valid=*/false));

  // Inserting two flows, one of them can fail.
  EXPECT_OK(Check({MakeInsert(new_flow1, StatusCode::kOk),
                   MakeInsert(new_flow2, StatusCode::kResourceExhausted)},
                  almost_full, /*valid=*/true));
  EXPECT_OK(Check({MakeInsert(new_flow1, StatusCode::kResourceExhausted),
                   MakeInsert(new_flow2, StatusCode::kOk)},
                  almost_full, /*valid=*/true));
}

}  // namespace
}  // namespace hercules
}  // namespace testing
}  // namespace switchstack
