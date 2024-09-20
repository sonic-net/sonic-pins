#include "p4_fuzzer/oracle_util.h"

#include <utility>

#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/collections.h"
#include "p4/v1/p4runtime.pb.h"
#include "gutil/status.h"
#include "google/rpc/code.pb.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_fuzzer/test_utils.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/netaddr/ipv4_address.h"
#include "p4_pdpi/pd.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"

namespace p4_fuzzer {
namespace {

using ::absl::StatusCode;
using ::p4::v1::TableEntry;
using ::p4::v1::Update;
using ::p4::v1::WriteRequest;

int AclIngressTableSize() {
  auto table = gutil::FindOrStatus(
      sai::GetIrP4Info(sai::Instantiation::kMiddleblock).tables_by_name(),
      "acl_ingress_table");
  CHECK(table.ok());  // Crash ok
  return table->size();
}

// Returns a ingress ACL table entry. Use integer arguments to vary match or
// action arguments.
TableEntry GetIngressAclTableEntry(int match, int action) {
  pdpi::IrTableEntry ir_table_entry =
      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
        table_name: "acl_ingress_table"
        matches {
          name: "is_ipv4"
          optional { value { hex_str: "0x1" } }
        }
        matches {
          name: "dst_ip"
          ternary {
            value { ipv4: "0.0.0.0" }
            mask { ipv4: "255.255.255.255" }
          }
        }
        priority: 10
        action {
          name: "acl_mirror"
          params {
            name: "mirror_session_id"
            value { str: "session" }
          }
        }
      )pb");
  *ir_table_entry.mutable_action()
       ->mutable_params(0)
       ->mutable_value()
       ->mutable_str() = absl::StrCat("session-", action);
  *ir_table_entry.mutable_matches(1)
       ->mutable_ternary()
       ->mutable_value()
       ->mutable_ipv4() =
      netaddr::Ipv4Address::OfBitset(std::bitset<32>(match)).ToString();
  auto result = pdpi::IrTableEntryToPi(
      sai::GetIrP4Info(sai::Instantiation::kMiddleblock), ir_table_entry);
  CHECK(result.ok()) << result.status();  // Crash OK
  return *result;
}

// Checks whether the update+state combo is plausible or not
absl::Status Check(const std::vector<UpdateStatus>& updates,
                   const FuzzerTestState& fuzzer_state, bool valid) {
  WriteRequest request;
  std::vector<pdpi::IrUpdateStatus> statuses;
  for (const auto& [update, status] : updates) {
    *request.add_updates() = update;
    pdpi::IrUpdateStatus ir_update_status;
    ir_update_status.set_code(static_cast<google::rpc::Code>(status.code()));
    statuses.push_back(ir_update_status);
  }
  absl::optional<std::vector<std::string>> oracle = WriteRequestOracle(
      fuzzer_state.config.info, request, statuses, fuzzer_state.switch_state);
  if (valid) {
    if (oracle.has_value()) {
      std::string explanation = absl::StrCat(
          "Expected the write request and statuses to be a valid combination, "
          "but they are not.",
          "\n", "errors reported:");
      for (const auto& error : oracle.value()) {
        explanation += absl::StrCat("\n", error);
      }
      return gutil::InvalidArgumentErrorBuilder() << explanation;
    }
  } else {
    if (!oracle.has_value()) {
      return gutil::InvalidArgumentErrorBuilder()
             << "Expected the write request and statuses to not be a valid "
                "combination, "
                "but they are according to the oracle.";
    }
  }
  return absl::OkStatus();
}

UpdateStatus MakeInsert(const TableEntry& table_entry, StatusCode status) {
  p4::v1::Update update;
  update.set_type(p4::v1::Update::INSERT);
  *update.mutable_entity()->mutable_table_entry() = table_entry;
  pdpi::IrUpdateStatus ir_update_status;
  ir_update_status.set_code(static_cast<google::rpc::Code>(status));
  return {update,ir_update_status};
}

UpdateStatus MakeDelete(const TableEntry& table_entry, StatusCode status) {
  p4::v1::Update update;
  update.set_type(p4::v1::Update::DELETE);
  *update.mutable_entity()->mutable_table_entry() = table_entry;
  pdpi::IrUpdateStatus ir_update_status;
  ir_update_status.set_code(static_cast<google::rpc::Code>(status));
  return {update,ir_update_status};
}

// Add a table entry to a state.
void AddTableEntry(const TableEntry& table_entry, SwitchState* state) {
  auto status =
      state->ApplyUpdate(MakeInsert(table_entry, absl::StatusCode::kOk).update);
  CHECK(status.ok());
}

// TODO: Enable this test after batching is handled correctly.
TEST(OracleUtilTest, DISABLED_SameKeyInBatch) {
  // Two entries, same key but different values/actions.
  TableEntry table_entry_1 = GetIngressAclTableEntry(/*match=*/0, /*action=*/1);
  TableEntry table_entry_2 = GetIngressAclTableEntry(/*match=*/0, /*action=*/2);
  FuzzerTestState fuzzer_state = ConstructFuzzerTestStateFromSaiMiddleBlock();

  // Same key should be rejected.
  EXPECT_OK(
      Check({MakeInsert(table_entry_1, absl::StatusCode::kOk),
             MakeInsert(table_entry_2, absl::StatusCode::kInvalidArgument)},
            fuzzer_state, /*valid=*/false));
  EXPECT_OK(
      Check({MakeInsert(table_entry_1, absl::StatusCode::kInvalidArgument),
             MakeInsert(table_entry_2, absl::StatusCode::kOk)},
            fuzzer_state, /*valid=*/false));
  EXPECT_OK(
      Check({MakeInsert(table_entry_1, absl::StatusCode::kInvalidArgument),
             MakeInsert(table_entry_2, absl::StatusCode::kInvalidArgument)},
            fuzzer_state, /*valid=*/true));

  // Even if some are insert and some are delete
  EXPECT_OK(
      Check({MakeDelete(table_entry_1, absl::StatusCode::kInvalidArgument),
             MakeInsert(table_entry_2, absl::StatusCode::kInvalidArgument)},
            fuzzer_state, /*valid=*/true));
}

TEST(OracleUtilTest, BatchResources) {
  // Create a state that's full.
  FuzzerTestState full_state = ConstructFuzzerTestStateFromSaiMiddleBlock();
  for (int i = 1; i <= AclIngressTableSize(); i++) {
    AddTableEntry(GetIngressAclTableEntry(/*match=*/i, /*action=*/0),
                  &full_state.switch_state);
  }

  TableEntry next = GetIngressAclTableEntry(
      /*match=*/AclIngressTableSize() + 1, /*action=*/0);

  // Inserting into full table is okay.
  EXPECT_OK(Check({MakeInsert(next, absl::StatusCode::kOk)}, full_state,
                  /*valid=*/true));

  // Resource exhasted is okay too.
  EXPECT_OK(Check({MakeInsert(next, absl::StatusCode::kResourceExhausted)},
                  full_state,
                  /*valid=*/true));
}

TEST(OracleUtilTest, BatchResourcesAlmostFull) {
  // Create a state that's almost full (1 entry remaining).
  FuzzerTestState almost_full = ConstructFuzzerTestStateFromSaiMiddleBlock();
  for (int i = 1; i <= AclIngressTableSize() - 1; i++) {
    AddTableEntry(GetIngressAclTableEntry(/*match=*/i, /*action=*/0),
                  &almost_full.switch_state);
  }

  TableEntry next1 = GetIngressAclTableEntry(
      /*match=*/AclIngressTableSize() + 1, /*action=*/0);
  TableEntry next2 = GetIngressAclTableEntry(
      /*match=*/AclIngressTableSize() + 2, /*action=*/0);

  // Resource exhausted is not okay.
  EXPECT_OK(Check({MakeInsert(next1, absl::StatusCode::kResourceExhausted)},
                  almost_full, /*valid=*/false));

  // Inserting two flows, one of them can fail.
  EXPECT_OK(Check({MakeInsert(next1, absl::StatusCode::kOk),
                   MakeInsert(next2, absl::StatusCode::kResourceExhausted)},
                  almost_full, /*valid=*/true));
  EXPECT_OK(Check({MakeInsert(next1, absl::StatusCode::kResourceExhausted),
                   MakeInsert(next2, absl::StatusCode::kOk)},
                  almost_full, /*valid=*/true));
  EXPECT_OK(Check({MakeInsert(next1, absl::StatusCode::kOk),
                   MakeInsert(next2, absl::StatusCode::kOk)},
                  almost_full, /*valid=*/true));
}
}  // namespace p4_fuzzer
}
