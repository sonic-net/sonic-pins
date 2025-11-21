#ifndef PINS_GUTIL_SYSLOG_SINK_H_
#define PINS_GUTIL_SYSLOG_SINK_H_

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

#endif  // PINS_GUTIL_SYSLOG_SINK_H_
