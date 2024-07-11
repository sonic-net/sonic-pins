#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/proto.h"
#include "gutil/status_matchers.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_constraints/backend/constraint_info.h"
#include "p4_constraints/backend/interpreter.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"

namespace pins {
namespace {

TEST(AclIngressConstraints, TernaryEqualityMustBeExact) {
  auto sai_instantiation = sai::Instantiation::kFabricBorderRouter;
  p4::config::v1::P4Info p4_info = sai::GetP4Info(sai_instantiation);
  pdpi::IrP4Info ir_info = sai::GetIrP4Info(sai_instantiation);
  ASSERT_OK_AND_ASSIGN(p4_constraints::ConstraintInfo constraint_info,
                       p4_constraints::P4ToConstraintInfo(p4_info));

  // Set up entry as IR.
  ASSERT_OK_AND_ASSIGN(pdpi::IrTableEntry ir_entry,
                       gutil::ParseTextProto<pdpi::IrTableEntry>(
                           R"pb(
                             table_name: "acl_ingress_table"
                             matches {
                               name: "is_ip"
                               optional { value { hex_str: "0x1" } }
                             }
                             matches {
                               name: "ip_protocol"
                               ternary {
                                 value { hex_str: "0x11" }
                                 mask { hex_str: "0x11" }
                               }
                             }
                             matches {
                               name: "l4_src_port"
                               ternary {
                                 value { hex_str: "0xfea7" }
                                 mask { hex_str: "0xffff" }
                               }
                             }
                             priority: 1
                             action { name: "acl_drop" }
                           )pb"));

  // Since the ip_protocol ternary is not exact, given its mask, this should
  // fail.
  {
    ASSERT_OK_AND_ASSIGN(p4::v1::TableEntry pi_entry,
                         pdpi::IrTableEntryToPi(ir_info, ir_entry));
    EXPECT_THAT(p4_constraints::EntryMeetsConstraint(pi_entry, constraint_info),
                gutil::IsOkAndHolds(false));
    ASSERT_OK_AND_ASSIGN(std::string failure_reason,
                         p4_constraints::ReasonEntryViolatesConstraint(
                             pi_entry, constraint_info));
    EXPECT_NE(failure_reason, "") << "for entry:\n" << ir_entry.DebugString();
  }

  // Update match to be exact.
  for (auto& match : *ir_entry.mutable_matches()) {
    if (match.name() == "ip_protocol") {
      match.mutable_ternary()->mutable_mask()->set_hex_str("0xff");
    }
  }

  // Since the ip_protocol ternary is exact, this should succeed.
  {
    ASSERT_OK_AND_ASSIGN(p4::v1::TableEntry pi_entry,
                         pdpi::IrTableEntryToPi(ir_info, ir_entry));
    EXPECT_THAT(p4_constraints::EntryMeetsConstraint(pi_entry, constraint_info),
                gutil::IsOkAndHolds(true));
    ASSERT_OK_AND_ASSIGN(std::string failure_reason,
                         p4_constraints::ReasonEntryViolatesConstraint(
                             pi_entry, constraint_info));
    EXPECT_EQ(failure_reason, "") << "for entry:\n" << ir_entry.DebugString();
  }
}

}  // namespace
}  // namespace pins
