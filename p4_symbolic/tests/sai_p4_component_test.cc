#include <memory>

#include "absl/strings/string_view.h"
#include "absl/time/clock.h"
#include "absl/types/optional.h"
#include "absl/types/span.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/pd.h"
#include "p4_symbolic/parser.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "sai_p4/instantiations/google/sai_nonstandard_platforms.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "thinkit/bazel_test_environment.h"

namespace p4_symbolic {
namespace {

using ::gutil::ParseProtoOrDie;
using ::p4::config::v1::P4Info;
using ::testing::Eq;
using ::testing::Not;

constexpr absl::string_view kTableEntries = R"PB(
  entries {
    acl_pre_ingress_table_entry  {
      match {}
      action { set_vrf { vrf_id: "vrf-80" } }
      priority: 1
    }
  }
  entries {
    ipv6_table_entry {
      match { vrf_id: "vrf-80" }
      action { drop {} }
    }
  }
  entries {
    ipv4_table_entry {
      match { vrf_id: "vrf-80" }
      action { set_nexthop_id { nexthop_id: "nexthop-1" } }
    }
  }
  entries {
    nexthop_table_entry {
      match { nexthop_id: "nexthop-1" }
      action {
        set_ip_nexthop {
          router_interface_id: "router-interface-1"
          neighbor_id: "fe80::cebb:aaff:fe99:8877"
        }
      }
    }
  }
  entries {
    router_interface_table_entry {
      match { router_interface_id: "router-interface-1" }
      action {
        set_port_and_src_mac { port: "0x002" src_mac: "66:55:44:33:22:11" }
      }
    }
  }
  entries {
    neighbor_table_entry {
      match {
        router_interface_id: "router-interface-1"
        neighbor_id: "fe80::cebb:aaff:fe99:8877"
      }
      action { set_dst_mac { dst_mac: "cc:bb:aa:99:88:77" } }
    }
  }
)PB";

class P4SymbolicComponentTest : public testing::Test {
 public:
  thinkit::TestEnvironment& Environment() { return *environment_; }

 private:
  std::unique_ptr<thinkit::TestEnvironment> environment_ =
      absl::make_unique<thinkit::BazelTestEnvironment>(
          /*mask_known_failures=*/true);
};

TEST(P4SymbolicComponentTest, CanGenerateTestPacketsForSimpleSaiP4Entries) {
  // Some constants.
  auto env = thinkit::BazelTestEnvironment(/*mask_known_failures=*/false);
  const auto config = sai::GetNonstandardForwardingPipelineConfig(
      sai::Instantiation::kMiddleblock, sai::NonstandardPlatform::kP4Symbolic);
  ASSERT_OK_AND_ASSIGN(const pdpi::IrP4Info ir_p4info,
                       pdpi::CreateIrP4Info(config.p4info()));
  EXPECT_OK(env.StoreTestArtifact("ir_p4info.textproto", ir_p4info));
  EXPECT_OK(env.StoreTestArtifact("p4_config.json", config.p4_device_config()));

  // Prepare hard-coded table entries.
  auto pd_entries = ParseProtoOrDie<sai::TableEntries>(kTableEntries);
  EXPECT_OK(env.StoreTestArtifact("pd_entries.textproto", pd_entries));
  std::vector<p4::v1::TableEntry> pi_entries;
  for (auto& pd_entry : pd_entries.entries()) {
    ASSERT_OK_AND_ASSIGN(pi_entries.emplace_back(),
                         pdpi::PartialPdTableEntryToPiTableEntry(ir_p4info, pd_entry));
  }

  // Prepare p4-symbolic.
  ASSERT_OK_AND_ASSIGN(
      symbolic::Dataplane dataplane,
      ParseToIr(config.p4_device_config(), ir_p4info, pi_entries));
  std::vector<int> ports = {1, 2, 3, 4, 5};
  LOG(INFO) << "building model (this may take a while) ...";
  absl::Time start_time = absl::Now();
  LOG(INFO) << "-> done in " << (absl::Now() - start_time);

  // TODO: Generate test packets.
  // symbolic::Solve
  // symbolic::DebugSMT
}

}  // namespace
}  // namespace p4_symbolic
