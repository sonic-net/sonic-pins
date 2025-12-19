#include "tests/lib/common_ir_table_entries.h"

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"  // IWYU pragma: keep
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"

namespace pins {
namespace {

using CommonIrTableEntriesTest = testing::TestWithParam<pdpi::IrTableEntry>;

TEST_P(CommonIrTableEntriesTest, IsValidIrEntryForAllSaiInstantiations) {
  for (const auto &instantation : sai::AllSaiInstantiations()) {
    EXPECT_OK(
        pdpi::IrTableEntryToPi(sai::GetIrP4Info(instantation), GetParam()))
        << "Invalid entry on " << sai::InstantiationToString(instantation);
  }
}

INSTANTIATE_TEST_SUITE_P(
    CommonIrTableEntriesSuite, CommonIrTableEntriesTest,
    testing::Values(PuntAllPacketsToControllerIrTableEntry("0x1"),
                    SetVrfIdForAllPacketsIrTableEntry("vrf-1")));

} // namespace
} // namespace pins
