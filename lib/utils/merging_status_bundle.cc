#include "lib/utils/merging_status_bundle.h"

#include <string>
#include <thread>  // NOLINT (Upstream)
#include <utility>
#include <vector>

#include "absl/functional/any_invocable.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "absl/synchronization/mutex.h"

namespace pins_test {
namespace {

// Merges a vector of statuses into a single status.
absl::Status MergeStatuses(std::vector<absl::Status> statuses) {
  statuses.erase(
      std::remove_if(statuses.begin(), statuses.end(),
                     [](const absl::Status& status) { return status.ok(); }),
      statuses.end());
  if (statuses.empty()) {
    return absl::OkStatus();
  }
  if (statuses.size() == 1) {
    return statuses[0];
  }

  // If all statuses have the same error code, return that code. Otherwise,
  // return kInternal.
  absl::StatusCode code = statuses[0].code();
  std::vector<std::string> error_messages;
  for (const auto& status : statuses) {
    error_messages.push_back(status.ToString());
    if (status.code() != code) {
      code = absl::StatusCode::kInternal;
    }
  }
  return absl::Status(code, absl::StrCat("Multiple Errors:\n",
                                         absl::StrJoin(error_messages, "\n")));
}

}  // namespace

void MergingStatusBundle::Add(absl::AnyInvocable<absl::Status()> function) {
  threads_.push_back(std::thread([&, function = std::move(function)]() mutable {
    absl::Status status = function();
    absl::MutexLock lock(&mutex_);
    statuses_.push_back(status);
  }));
}

absl::Status MergingStatusBundle::Join() {
  for (auto& thread : threads_) {
    thread.join();
  }
  return MergeStatuses(std::move(statuses_));
}

}  // namespace pins_test

