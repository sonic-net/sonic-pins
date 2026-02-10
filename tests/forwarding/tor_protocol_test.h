#ifndef PINS_TESTS_FORWARDING_TOR_PROTOCOL_TEST_H_
#define PINS_TESTS_FORWARDING_TOR_PROTOCOL_TEST_H_

#include <memory>
#include <optional>
#include <string>

#include "dvaas/dataplane_validation.h"
#include "gtest/gtest.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "thinkit/mirror_testbed.h"
#include "thinkit/mirror_testbed_fixture.h"

namespace pins_test {
struct TorProtocolTestParams {
  struct SwitchConfig {
    p4::config::v1::P4Info p4info;
    std::optional<std::string> gnmi_config;
  };
  SwitchConfig sut;
  SwitchConfig control_switch;
  std::shared_ptr<thinkit::MirrorTestbedInterface> testbed;
  std::shared_ptr<dvaas::DataplaneValidator> dvaas;
  dvaas::DataplaneValidationParams dvaas_params;
  bool rewrite_vlan;
};

class TorProtocolTest : public testing::TestWithParam<TorProtocolTestParams> {
 protected:
  void SetUp() override;
  void TearDown() override { GetParam().testbed->TearDown(); }

  static thinkit::MirrorTestbed& testbed() {
    return GetParam().testbed->GetMirrorTestbed();
  }
  pdpi::P4RuntimeSession& sut_p4rt_session() { return *sut_p4rt_session_; }
  const pdpi::IrP4Info& ir_p4info() { return ir_p4info_; }

 private:
  std::unique_ptr<pdpi::P4RuntimeSession> sut_p4rt_session_;
  pdpi::IrP4Info ir_p4info_;
};

}  // namespace pins_test
#endif  // PINS_TESTS_FORWARDING_TOR_PROTOCOL_TEST_H_
