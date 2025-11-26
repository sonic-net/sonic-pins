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

#include <cstddef>

#include "glog/logging.h"

namespace gutil {

// When constructed SyslogSink will automatically register with GLOG and begin
// forwarding all LOG() messages to syslog. In the dtor we unregister with GLOG
// so the SyslogSink should outlive the program. These messages are treated as
// user-level (i.e. a LOG_USER facility), and serverities are mapped as follows:
//   LOG(INFO)    -> LOG_INFO
//   LOG(WARNING) -> LOG_WARNING
//   LOG(ERROR)   -> LOG_ERR
//   LOG(FATAL)   -> LOG_EMERG
//
// The syslog message will be formatted similar to a GLOG message with a
// microsecond timestamp.
class SyslogSink : google::LogSink {
 public:
  SyslogSink(const char* process_name);
  ~SyslogSink();

  void send(google::LogSeverity severity, const char* full_filename,
            const char* base_filename, int line,
            const google::LogMessageTime& logmsgtime, const char* message,
            size_t message_len) override;
};

}  // namespace gutil

#endif  // PINS_GUTIL_GUTIL_SYSLOG_SINK_H_
