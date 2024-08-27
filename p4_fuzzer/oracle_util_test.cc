#include "p4_fuzzer/oracle_util.h"

#include <utility>

#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/collections.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/netaddr/ipv4_address.h"
#include "p4_pdpi/pd.h"
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

SwitchState EmptyState() {
  return SwitchState(sai::GetIrP4Info(sai::Instantiation::kMiddleblock));
}

// An update and it's corresponding status.
struct UpdateStatus {
  p4::v1::Update update;
  StatusCode status;
};

// Checks whether the update+state combo is plausible or not
absl::Status Check(const std::vector<UpdateStatus>& updates,
                   const SwitchState& state, bool valid) {
  WriteRequest request;
  std::vector<p4::v1::Error> statuses;
  for (const auto& [update, status] : updates) {
    *request.add_updates() = update;
    p4::v1::Error p4_error;
    p4_error.set_canonical_code(static_cast<int32_t>(status));
    statuses.push_back(p4_error);
  }
  absl::optional<std::vector<std::string>> oracle =
      WriteRequestOracle(sai::GetIrP4Info(sai::Instantiation::kMiddleblock),
                         request, statuses, state);
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
  return {update, status};
}

UpdateStatus MakeDelete(const TableEntry& table_entry, StatusCode status) {
  p4::v1::Update update;
  update.set_type(p4::v1::Update::DELETE);
  *update.mutable_entity()->mutable_table_entry() = table_entry;
  return {update, status};
}

// Add a table entry to a state.
void AddTableEntry(const TableEntry& table_entry, SwitchState* state) {
  auto status =
      state->ApplyUpdate(MakeInsert(table_entry, absl::StatusCode::kOk).update);
  CHECK(status.ok());
}

}  // namespace
}  // namespace p4_fuzzer
