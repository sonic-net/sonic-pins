#include "p4_fuzzer/table_entry_key.h"

#include "absl/hash/hash_testing.h"
#include "gtest/gtest.h"

namespace p4_fuzzer {
namespace {

using ::p4::v1::FieldMatch;
using ::p4::v1::TableEntry;

TEST(TableEntryKeyTest, TrivialEquality) {
  TableEntry entry;
  TableEntryKey key_a(entry);
  TableEntryKey key_b(entry);

  EXPECT_EQ(key_a, key_b);
}

TEST(TableEntryKeyTest, DiscardOtherValues) {
  TableEntry entry;
  entry.set_table_id(42);
  entry.set_idle_timeout_ns(7);

  TableEntry entry2;
  entry2.set_table_id(42);
  entry2.set_idle_timeout_ns(8);

  TableEntryKey key_a(entry);
  TableEntryKey key_b(entry2);

  EXPECT_EQ(key_a, key_b);

  TableEntry entry3;
  entry3.set_table_id(42);

  TableEntryKey key_c(entry3);

  EXPECT_EQ(key_a, key_c);
}

TEST(TableEntryKeyTest, Hashing) {
  TableEntry entry;
  entry.set_table_id(42);
  entry.set_idle_timeout_ns(7);

  TableEntryKey key_a(entry);

  entry.set_idle_timeout_ns(8);
  TableEntryKey key_b(entry);

  entry.set_priority(100);

  TableEntryKey key_c(entry);

  FieldMatch* field = entry.add_match();
  field->set_field_id(43);

  TableEntryKey key_d(entry);

  EXPECT_TRUE(absl::VerifyTypeImplementsAbslHashCorrectly(
      /*values = */ {key_a, key_b, key_c}));

  EXPECT_TRUE(absl::VerifyTypeImplementsAbslHashCorrectly(
      /*values = */ {key_a, key_b, key_c}));
}

}  // namespace
}  // namespace p4_fuzzer
