#ifndef PINS_LIB_UTILS_MERGING_STATUS_BUNDLE_H_
#define PINS_LIB_UTILS_MERGING_STATUS_BUNDLE_H_

#include <thread>  // NOLINT (Upstream)
#include <vector>

#include "absl/base/thread_annotations.h"
#include "absl/functional/any_invocable.h"
#include "absl/status/status.h"
#include "absl/synchronization/mutex.h"

namespace pins_test {

class MergingStatusBundle {
 public:
  // Adds a function returning a status to the bundle.
  void Add(absl::AnyInvocable<absl::Status()> function);

  // Joins all of the threads and returns the merged status.
  absl::Status Join();

 private:
  absl::Mutex mutex_;
  std::vector<absl::Status> statuses_ ABSL_GUARDED_BY(mutex_);
  std::vector<std::thread> threads_;
};

}  // namespace pins_test

#endif  // PINS_LIB_UTILS_MERGING_STATUS_BUNDLE_H_
