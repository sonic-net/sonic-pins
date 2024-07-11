#include "p4_fuzzer/fuzzer_config.h"

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "gutil/status.h"  // IWYU pragma: keep
#include "gutil/status.h"
#include "p4_pdpi/ir.h"

namespace p4_fuzzer {

absl::Status FuzzerConfig::SetP4Info(const p4::config::v1::P4Info& info) {
  ASSIGN_OR_RETURN(this->ir_info_, pdpi::CreateIrP4Info(info));
  this->info_ = info;
  return absl::OkStatus();
}

absl::StatusOr<FuzzerConfig> FuzzerConfig::Create(
    const p4::config::v1::P4Info& info) {
  FuzzerConfig config;
  RETURN_IF_ERROR(config.SetP4Info(info));
  return config;
}

}  // namespace p4_fuzzer
