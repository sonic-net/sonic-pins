#include "sai_p4/instantiations/google/sai_pd_util.h"

#include <functional>

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/testing.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"

namespace sai_pd {
namespace {

using ::testing::Eq;
using ::testing::Optional;

TEST(TableEntryNameTest, ReturnsNulloptForUninitializedEntry) {
  EXPECT_THAT(TableEntryName(sai::TableEntry()), Eq(absl::nullopt));
}

TEST(TableEntryNameTest, ReturnsTableEntryNameForSelectedEntries) {
  struct TestCase {
    std::string table_entry_name;
    std::function<void(sai::TableEntry*)> setter;
  };
  auto test_cases = std::vector<TestCase>{
      {"neighbor_table_entry", &sai::TableEntry::mutable_neighbor_table_entry},
      {"router_interface_table_entry",
       &sai::TableEntry::mutable_router_interface_table_entry},
      {"nexthop_table_entry", &sai::TableEntry::mutable_nexthop_table_entry},
      {"wcmp_group_table_entry",
       &sai::TableEntry::mutable_wcmp_group_table_entry},
  };

  for (auto& test_case : test_cases) {
    sai::TableEntry entry;
    test_case.setter(&entry);
    EXPECT_THAT(TableEntryName(entry), Optional(Eq(test_case.table_entry_name)))
        << entry.DebugString();
  }
}

TEST(UpdateStatusToStringTest, WorksForInitializedStatus) {
  auto status = gutil::ParseProtoOrDie<sai::UpdateStatus>(R"pb(
    code: INTERNAL
    message: "foo bar"
  )pb");
  EXPECT_THAT(UpdateStatusToString(status), Eq("INTERNAL: foo bar"))
      << status.DebugString();
}

}  // namespace

}  // namespace sai_pd
