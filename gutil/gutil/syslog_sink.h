// Exposes functions to write test artifacts understood by Bazel.

// Copyright 2025 Google LLC
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

#ifndef PINS_GUTIL_GUTIL_SYSLOG_SINK_H_
#define PINS_GUTIL_GUTIL_SYSLOG_SINK_H_

#include "absl/log/log_entry.h"
#include "absl/log/log_sink.h"

namespace gutil {

// When constructed SyslogSink will automatically register an Abseil LogSink and
// begin forwarding all LOG() messages to syslog. In the dtor we unregister the
// LogSink so the SyslogSink should outlive the program. These messages are
// treated as user-level (i.e. a LOG_USER facility), and serverities are mapped
// as follows:
//   LOG(INFO)    -> LOG_INFO
//   LOG(WARNING) -> LOG_WARNING
//   LOG(ERROR)   -> LOG_ERR
//   LOG(FATAL)   -> LOG_EMERG
//
// The syslog message will be formatted similar to the default Abseil Log
// message except with a microsecond timestamp.
class SyslogSink final : public absl::LogSink {
 public:
  SyslogSink(const char* process_name);
  ~SyslogSink();

  void Send(const absl::LogEntry& entry) override;
};

}  // namespace gutil

#endif  // PINS_GUTIL_GUTIL_SYSLOG_SINK_H_
