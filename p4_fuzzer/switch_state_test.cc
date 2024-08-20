#include "p4_fuzzer/switch_state.h"

#include "glog/logging.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "p4_pdpi/ir.h"

namespace p4_fuzzer {
namespace {

using ::p4::config::v1::P4Info;
using ::p4::config::v1::Preamble;
using ::p4::config::v1::Table;
using ::p4::v1::TableEntry;
using ::p4::v1::Update;
using ::pdpi::CreateIrP4Info;
using ::pdpi::IrP4Info;

TEST(SwitchStateTest, TableEmptyTrivial) {
  IrP4Info info;
  SwitchState state(info);

  EXPECT_TRUE(state.AllTablesEmpty());
}

TEST(SwitchStateTest, TableEmptyFromP4Info) {
  P4Info info;
  Table* ptable = info.add_tables();
  ptable->mutable_preamble()->set_id(42);

  IrP4Info ir_info = CreateIrP4Info(info).value();

  SwitchState state(ir_info);
  EXPECT_TRUE(state.AllTablesEmpty());
}

TEST(SwitchStateTest, RuleInsert) {
  P4Info info;
  Table* ptable = info.add_tables();
  Preamble* preamble = ptable->mutable_preamble();
  preamble->set_id(42);
  preamble->set_alias("Spam");

  ptable = info.add_tables();
  preamble = ptable->mutable_preamble();
  preamble->set_id(43);
  preamble->set_alias("Eggs");

  IrP4Info ir_info = CreateIrP4Info(info).value();

  SwitchState state(ir_info);

  Update update;
  update.set_type(Update::INSERT);

  TableEntry* entry = update.mutable_entity()->mutable_table_entry();
  entry->set_table_id(42);

  ASSERT_OK(state.ApplyUpdate(update));

  EXPECT_FALSE(state.AllTablesEmpty());
  EXPECT_FALSE(state.IsTableEmpty(42));
  EXPECT_TRUE(state.IsTableEmpty(43));

  EXPECT_EQ(state.GetNumTableEntries(42), 1);
  EXPECT_EQ(state.GetNumTableEntries(43), 0);

  EXPECT_EQ(state.GetTableEntries(42).size(), 1);
  EXPECT_EQ(state.GetTableEntries(43).size(), 0);
}

TEST(SwitchStateTest, RuleDelete) {
  P4Info info;
  Table* ptable = info.add_tables();
  Preamble* preamble = ptable->mutable_preamble();
  preamble->set_id(42);
  preamble->set_alias("Spam");

  ptable = info.add_tables();
  preamble = ptable->mutable_preamble();
  preamble->set_id(43);
  preamble->set_alias("Eggs");

  IrP4Info ir_info = CreateIrP4Info(info).value();

  SwitchState state(ir_info);

  Update update;
  update.set_type(Update::INSERT);

  TableEntry* entry = update.mutable_entity()->mutable_table_entry();
  entry->set_table_id(42);

  ASSERT_OK(state.ApplyUpdate(update));

  update.set_type(Update::DELETE);
  ASSERT_OK(state.ApplyUpdate(update));

  EXPECT_TRUE(state.AllTablesEmpty());

  EXPECT_EQ(state.GetNumTableEntries(42), 0);
  EXPECT_EQ(state.GetTableEntries(42).size(), 0);
}

}  // namespace
}  // namespace p4_fuzzer
