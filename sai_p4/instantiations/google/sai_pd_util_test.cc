#include "sai_p4/instantiations/google/sai_pd_util.h"

#include <functional>

#include "absl/strings/str_replace.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/testing.h"
#include "re2/re2.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"

namespace sai_pd {
namespace {

using ::testing::EndsWith;
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

TEST(TableNameTest, TableEntryNameEndsWithEntrySuffix) {
  sai::TableEntry entry;
  auto* oneof_descriptor = entry.GetDescriptor()->FindOneofByName("entry");
  ASSERT_GE(oneof_descriptor->field_count(), 0);
  for (int i = 0; i < oneof_descriptor->field_count(); ++i) {
    const google::protobuf::FieldDescriptor* field = oneof_descriptor->field(i);
    entry.GetReflection()->MutableMessage(&entry, field);
    EXPECT_THAT(TableEntryName(entry), Optional(EndsWith("_entry")));
  }
}

TEST(TableNameTest, TableNameAndTableEntryNameIsNullIfOneOfFieldNotSet) {
  sai::TableEntry entry;
  EXPECT_FALSE(TableName(entry).has_value());
  EXPECT_FALSE(TableEntryName(entry).has_value());
}

// Verify that TableName(entry) is TableEntryName(entry) for each and every
// oneof field.
TEST(TableNameTest, TableNameIsTableEntryNameWithoutEntrySuffix) {
  sai::TableEntry entry;
  auto* oneof_descriptor = entry.GetDescriptor()->FindOneofByName("entry");
  ASSERT_GE(oneof_descriptor->field_count(), 0);
  for (int i = 0; i < oneof_descriptor->field_count(); ++i) {
    const google::protobuf::FieldDescriptor* field = oneof_descriptor->field(i);
    SCOPED_TRACE(entry.DebugString());
    entry.GetReflection()->MutableMessage(&entry, field);
    auto table_name = TableName(entry);
    auto entry_name = TableEntryName(entry);
    ASSERT_TRUE(table_name.has_value());
    ASSERT_TRUE(entry_name.has_value());
    EXPECT_EQ(*table_name, absl::StrReplaceAll(*entry_name, {{"_entry", ""}}));
    LOG(INFO) << "Table name: " << *table_name
              << ", Entry name: " << *entry_name;
  }
}

}  // namespace

}  // namespace sai_pd
