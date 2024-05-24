#include "p4_pdpi/sequencing_util.h"

#include <string>

#include "absl/hash/hash_testing.h"
#include "gtest/gtest.h"
namespace pdpi {
namespace {

// Tests to verify different ReferredFields are not equal and have different
// hash values.
// The hash value check is provided by VerifyTypeImplementsAbslHashCorrectly
// that checks ReferredFields that are equal have the same hash values and
// ReferredFields that are not equal have different hash values.
TEST(ReferredFieldTest, EqualityAndHashingTest) {
  std::string match_field_1 = "match_field_1";
  std::string match_field_2 = "match_field_2";
  std::string value_1 = "value_1";
  std::string value_2 = "0x002";
  std::string value_3 = "0x003";
  // ReferredFields with different match field names and match field values
  // are not equal.
  ReferredField field_1{.match_field_name = match_field_1, .value = value_1};
  ReferredField field_2{.match_field_name = match_field_2, .value = value_2};
  EXPECT_NE(field_1, field_2);

  // ReferredFields with the same match field name but different values are not
  // equal.
  ReferredField field_3 = {.match_field_name = match_field_1, .value = value_1};
  ReferredField field_4 = {.match_field_name = match_field_1, .value = value_2};
  EXPECT_NE(field_3, field_4);
  // ReferredField with different match field names but the same match field
  // value are not equal.
  ReferredField field_5 = {.match_field_name = match_field_1, .value = value_1};
  ReferredField field_6 = {.match_field_name = match_field_2, .value = value_1};
  EXPECT_NE(field_5, field_6);
  // Identical ReferredFields are equal.
  ReferredField field_7 = {.match_field_name = match_field_1, .value = value_1};
  EXPECT_EQ(field_5, field_7);
  // ReferredFields with different match field names in byte string are not
  // equal.
  ReferredField field_8 = {.match_field_name = match_field_1, .value = value_2};
  ReferredField field_9 = {.match_field_name = match_field_1, .value = value_3};
  EXPECT_NE(field_8, field_9);

  EXPECT_TRUE(absl::VerifyTypeImplementsAbslHashCorrectly({
      field_1,
      field_2,
      field_3,
      field_4,
      field_5,
      field_6,
      field_7,
      field_8,
      field_9,
  }));
}

TEST(ReferredFieldEntryTest, EqualityAndHashingTest) {
  ReferredField field_1{.match_field_name = "match_field_1",
                        .value = "value_1"};
  ReferredField field_2{.match_field_name = "match_field_2",
                        .value = "value_2"};
  ReferredField field_3{.match_field_name = "match_field_3", .value = "0x003"};
  ReferredField field_4{.match_field_name = "match_field_4", .value = "0x004"};

  // Identical ReferredTableEntries are equal.
  ReferredTableEntry entry_1 = {.table = "table_1",
                                .referred_fields = {field_1, field_2}};
  ReferredTableEntry entry_2 = {.table = "table_1",
                                .referred_fields = {field_1, field_2}};
  EXPECT_EQ(entry_1, entry_2);

  // Hex values can be differentiated.
  ReferredTableEntry entry_3 = {.table = "table_1",
                                .referred_fields = {field_2, field_4}};
  ReferredTableEntry entry_4 = {.table = "table_1",
                                .referred_fields = {field_2, field_3}};
  EXPECT_NE(entry_3, entry_4);
  ReferredTableEntry entry_5 = {.table = "table_1",
                                .referred_fields = {field_3}};
  ReferredTableEntry entry_6 = {.table = "table_1",
                                .referred_fields = {field_4}};
  EXPECT_NE(entry_5, entry_6);
  ReferredTableEntry entry_7 = {.table = "table_1",
                                .referred_fields = {field_1}};
  ReferredTableEntry entry_8 = {.table = "table_1",
                                .referred_fields = {field_3}};
  EXPECT_NE(entry_7, entry_8);

  // ReferredTableEntry whose referred_fields is a subset of another
  // ReferredTableEntry is not equal to that ReferredTableEntry.
  ReferredTableEntry entry_9 = {.table = "table_1",
                                .referred_fields = {field_1, field_2, field_3}};
  ReferredTableEntry entry_10 = {
      .table = "table_1",
      .referred_fields = {field_1, field_2, field_3, field_4}};
  EXPECT_NE(entry_9, entry_10);
  // ReferredTableEntrys with the same set of referred_fields and the same table
  // names are equal.
  ReferredTableEntry entry_11 = {.table = "table_1",
                                 .referred_fields = {field_1, field_2}};
  ReferredTableEntry entry_12 = {.table = "table_1",
                                 .referred_fields = {field_2, field_1}};
  EXPECT_EQ(entry_11, entry_12);

  // ReferredTableEntries with the same set of referred_fields but different
  // table name are not equal.
  ReferredTableEntry entry_13 = {.table = "table_2",
                                 .referred_fields = {field_1, field_2}};
  ReferredTableEntry entry_14 = {.table = "table_1",
                                 .referred_fields = {field_2, field_1}};
  EXPECT_NE(entry_13, entry_14);

  EXPECT_TRUE(absl::VerifyTypeImplementsAbslHashCorrectly({
      entry_1,
      entry_2,
      entry_3,
      entry_4,
      entry_5,
      entry_6,
      entry_7,
      entry_8,
      entry_9,
      entry_10,
      entry_11,
      entry_12,
      entry_13,
      entry_14,
  }));
}

}  // namespace
}  // namespace pdpi
