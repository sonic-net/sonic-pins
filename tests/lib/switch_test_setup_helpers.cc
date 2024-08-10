#include "tests/lib/switch_test_setup_helpers.h"

#include <memory>
#include <string>
#include <utility>

#include "absl/status/status.h"
#include "absl/time/time.h"
#include "absl/types/optional.h"
#include "gutil/status.h"
#include "lib/gnmi/gnmi_helper.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/p4_runtime_session.h"

namespace pins_test {
namespace {

constexpr absl::Duration kGnmiTimeoutDefault = absl::Minutes(3);

absl::StatusOr<std::unique_ptr<pdpi::P4RuntimeSession>>
CreateP4RuntimeSessionAndClearExistingState(
    thinkit::Switch& thinkit_switch,
    const pdpi::P4RuntimeSessionOptionalArgs& metadata) {
  ASSIGN_OR_RETURN(std::unique_ptr<pdpi::P4RuntimeSession> session,
                   pdpi::P4RuntimeSession::Create(thinkit_switch, metadata));
  RETURN_IF_ERROR(pdpi::ClearTableEntries(session.get()));
  RETURN_IF_ERROR(pdpi::CheckNoTableEntries(session.get())).SetPrepend()
      << "cleared all table entries: ";
  return session;
}

absl::Status PushGnmiAndWaitForConvergence(thinkit::Switch& thinkit_switch,
                                           const std::string& gnmi_config,
                                           absl::Duration gnmi_timeout) {
  RETURN_IF_ERROR(PushGnmiConfig(thinkit_switch, gnmi_config));
  return WaitForGnmiPortIdConvergence(thinkit_switch, gnmi_config,
                                      gnmi_timeout);
}

absl::Status SetForwardingPipelineConfigAndAssureClearedTables(
    pdpi::P4RuntimeSession* session, const p4::config::v1::P4Info& p4info) {
  RETURN_IF_ERROR(pdpi::SetMetadataAndSetForwardingPipelineConfig(
      session, p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
      p4info));
  RETURN_IF_ERROR(pdpi::CheckNoTableEntries(session)).SetPrepend()
      << "set a new forwarding pipeline config: ";
  return absl::OkStatus();
}

}  // namespace

absl::StatusOr<std::unique_ptr<pdpi::P4RuntimeSession>>
ConfigureSwitchAndReturnP4RuntimeSession(
    thinkit::Switch& thinkit_switch, std::optional<std::string> gnmi_config,
    std::optional<p4::config::v1::P4Info> p4info,
    const pdpi::P4RuntimeSessionOptionalArgs& metadata) {
  // Since the gNMI Config push relies on tables being cleared, we construct a
  // P4RuntimeSession and clear the tables first.
  ASSIGN_OR_RETURN(
      std::unique_ptr<pdpi::P4RuntimeSession> session,
      CreateP4RuntimeSessionAndClearExistingState(thinkit_switch, metadata));

  if (gnmi_config.has_value()) {
    RETURN_IF_ERROR(
        PushGnmiAndWaitForConvergence(thinkit_switch, *gnmi_config,
                                      /*gnmi_timeout=*/kGnmiTimeoutDefault));
  }

  if (p4info.has_value()) {
    RETURN_IF_ERROR(SetForwardingPipelineConfigAndAssureClearedTables(
        session.get(), *p4info));
  }

  return session;
}

absl::StatusOr<std::pair<std::unique_ptr<pdpi::P4RuntimeSession>,
                         std::unique_ptr<pdpi::P4RuntimeSession>>>
ConfigureSwitchPairAndReturnP4RuntimeSessionPair(
    thinkit::Switch& thinkit_switch1, thinkit::Switch& thinkit_switch2,
    std::optional<std::string> gnmi_config,
    std::optional<p4::config::v1::P4Info> p4info,
    const pdpi::P4RuntimeSessionOptionalArgs& metadata) {
  // Since the gNMI Config push relies on tables being cleared, we construct the
  // P4RuntimeSessions and clear the tables first.
  ASSIGN_OR_RETURN(
      std::unique_ptr<pdpi::P4RuntimeSession> session1,
      CreateP4RuntimeSessionAndClearExistingState(thinkit_switch1, metadata));
  ASSIGN_OR_RETURN(
      std::unique_ptr<pdpi::P4RuntimeSession> session2,
      CreateP4RuntimeSessionAndClearExistingState(thinkit_switch2, metadata));

  if (gnmi_config.has_value()) {
    // Push the gNMI configs to both switches before waiting for convergence.
    RETURN_IF_ERROR(PushGnmiConfig(thinkit_switch1, *gnmi_config));
    RETURN_IF_ERROR(PushGnmiConfig(thinkit_switch2, *gnmi_config));
    RETURN_IF_ERROR(WaitForGnmiPortIdConvergence(thinkit_switch1, *gnmi_config,
                                                 kGnmiTimeoutDefault));
    RETURN_IF_ERROR(WaitForGnmiPortIdConvergence(thinkit_switch2, *gnmi_config,
                                                 kGnmiTimeoutDefault));
  }

  if (p4info.has_value()) {
    RETURN_IF_ERROR(SetForwardingPipelineConfigAndAssureClearedTables(
        session1.get(), *p4info));
    RETURN_IF_ERROR(SetForwardingPipelineConfigAndAssureClearedTables(
        session2.get(), *p4info));
  }

  return std::make_pair(std::move(session1), std::move(session2));
}

}  // namespace pins_test
