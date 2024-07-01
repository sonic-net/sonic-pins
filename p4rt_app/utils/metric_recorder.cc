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
#include "p4rt_app/utils/metric_recorder.h"

#include <memory>
#include <string>
#include <thread>  // NOLINT
#include <utility>
#include <vector>

#include "absl/functional/bind_front.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"

namespace p4rt_app {

MetricRecorder::MetricRecorder(absl::string_view server, uint32_t size,
                               absl::Duration period,
                               std::unique_ptr<sonic::TableAdapter> authn_table,
                               std::unique_ptr<sonic::TableAdapter> authz_table)
    : server_(server),
      authn_cache_(size),
      authz_cache_(size),
      period_(period),
      authn_table_(std::move(authn_table)),
      authz_table_(std::move(authz_table)),
      write_to_db_thread_(absl::bind_front(&MetricRecorder::WriteToDb, this)) {}

MetricRecorder::~MetricRecorder() {
  done_.Notify();
  if (write_to_db_thread_.joinable()) {
    write_to_db_thread_.join();
  }
}

void MetricRecorder::WriteToDb() {
  while (!done_.HasBeenNotified()) {
    absl::SleepFor(period_);
    absl::MutexLock lock(&mutex_);
    for (const auto& record : authz_pending_records_) {
      if (!authz_cache_.contains(record)) {
        // If entry is evicted in the cache, we do not write it into the DB.
        continue;
      }
      auto metric = authz_cache_.at(record);
      authz_table_->set(record,
                        std::vector<std::pair<std::string, std::string>>{
                            {"count", absl::StrCat(metric.count)},
                            {"timestamp", absl::StrCat(metric.timestamp_ns)}});
    }
    authz_pending_records_.clear();
    for (const auto& record : authn_pending_records_) {
      if (!authn_cache_.contains(record)) {
        // If entry is evicted in the cache, we do not write it into the DB.
        continue;
      }
      auto metric = authn_cache_.at(record);
      authn_table_->set(record,
                        std::vector<std::pair<std::string, std::string>>{
                            {"count", absl::StrCat(metric.count)},
                            {"timestamp", absl::StrCat(metric.timestamp_ns)}});
    }
    authn_pending_records_.clear();
  }
}

void MetricRecorder::RecordAuthnSuccess(absl::string_view user) {
  RecordAuthnEntry(absl::StrCat(server_, "|success|", user));
}

void MetricRecorder::RecordAuthnFailure(absl::string_view deny_reason) {
  RecordAuthnEntry(absl::StrCat(server_, "|failure|", deny_reason));
}

void MetricRecorder::RecordAuthz(bool permitted, absl::string_view service,
                                 absl::string_view rpc) {
  RecordAuthzEntry(absl::StrCat(server_, "|", service, "|", rpc,
                                permitted ? "|permitted" : "|denied"));
}

void MetricRecorder::RecordAuthnEntry(absl::string_view record) {
  absl::MutexLock lock(&mutex_);

  int64_t timestamp = absl::GetCurrentTimeNanos();
  // If the entry is evicted in the cache, the counter will be reset in the DB.
  Metric& metric = authn_cache_[std::string(record)];
  ++metric.count;
  metric.timestamp_ns = timestamp;
  authn_pending_records_.insert(std::string(record));
}

void MetricRecorder::RecordAuthzEntry(absl::string_view record) {
  absl::MutexLock lock(&mutex_);

  int64_t timestamp = absl::GetCurrentTimeNanos();
  // If the entry is evicted in the cache, the counter will be reset in the DB.
  Metric& metric = authz_cache_[std::string(record)];
  ++metric.count;
  metric.timestamp_ns = timestamp;
  authz_pending_records_.insert(std::string(record));
}

}  // namespace p4rt_app
