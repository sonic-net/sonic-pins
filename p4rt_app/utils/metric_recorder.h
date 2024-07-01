// Copyright 2024 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
#ifndef PINS_P4RT_APP_UTILS_METRIC_RECORDER_H_
#define PINS_P4RT_APP_UTILS_METRIC_RECORDER_H_

#include <functional>
#include <memory>
#include <string>
#include <thread>  // NOLINT

#include "absl/container/flat_hash_set.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/synchronization/mutex.h"
#include "absl/synchronization/notification.h"
#include "absl/time/time.h"
#include "p4rt_app/sonic/adapters/table_adapter.h"
#include "p4rt_app/utils/lru_cache.h"

namespace p4rt_app {

struct Metric {
  // The total count of the same records.
  uint64_t count = 0;

  // The last timestamp in ns of the record.
  int64_t timestamp_ns = 0;
};

// The MetricRecorder class is used for gRPC auditing.
// It provides helper methods to record authn & authz events.
// The event info will be written into the Redis DB to show up in gNMI.
// It uses an LRU cache to prevent unbounded memory growth.
class MetricRecorder {
 public:
  MetricRecorder(absl::string_view server, uint32_t size, absl::Duration period,
                 std::unique_ptr<sonic::TableAdapter> authn_table,
                 std::unique_ptr<sonic::TableAdapter> authz_table);
  ~MetricRecorder();

  void WriteToDb();
  void RecordAuthnSuccess(absl::string_view user);
  void RecordAuthnFailure(absl::string_view deny_reason);
  void RecordAuthz(bool permitted, absl::string_view service,
                   absl::string_view rpc);

 private:
  void RecordAuthnEntry(absl::string_view record) ABSL_LOCKS_EXCLUDED(mutex_);
  void RecordAuthzEntry(absl::string_view record) ABSL_LOCKS_EXCLUDED(mutex_);

  absl::Mutex mutex_;

  // The server name shown in the authn record in the DB.
  std::string server_;

  // LRU cache to store all the records.
  // If the cache overflows, counters might be reset in the DB for the entries
  // that are evicted.
  LruCache<std::string, Metric> authn_cache_ ABSL_GUARDED_BY(mutex_);
  LruCache<std::string, Metric> authz_cache_ ABSL_GUARDED_BY(mutex_);

  // A cache to store the newly updated records before DB write.
  // Only the records in this cache will be written into the DB in the DB write.
  // This cache will be clear after DB write.
  absl::flat_hash_set<std::string> authn_pending_records_
      ABSL_GUARDED_BY(mutex_);
  absl::flat_hash_set<std::string> authz_pending_records_
      ABSL_GUARDED_BY(mutex_);

  // DB write period.
  absl::Duration period_;

  // Redis table for authn records.
  std::unique_ptr<sonic::TableAdapter> authn_table_;

  // Redis table for authz records.
  std::unique_ptr<sonic::TableAdapter> authz_table_;

  absl::Notification done_;

  // Thread to periodically write to DB.
  std::thread write_to_db_thread_;
};

}  // namespace p4rt_app

#endif  // PINS_P4RT_APP_UTILS_METRIC_RECORDER_H_
