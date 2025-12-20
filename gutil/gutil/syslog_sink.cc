#include "gutil/gutil/syslog_sink.h"

#include <sys/syscall.h>
#include <sys/syslog.h>
#include <sys/time.h>
#include <unistd.h>

#include <array>
#include <ctime>
#include <string>

#include "absl/log/log_entry.h"
#include "absl/log/log_sink_registry.h"

namespace gutil {
namespace {

// Abseil log severity uses integers in the range [0-3]:
//   https://github.com/abseil/abseil-cpp/blob/master/absl/base/log_severity.h
constexpr std::array<int, 4> kLogSeverityToSyslog = {
    LOG_INFO,
    LOG_WARNING,
    LOG_ERR,
    LOG_EMERG,
};
constexpr std::array<char, 4> kLogSeverityLetter = {
    'I',
    'W',
    'E',
    'F',
};

}  // namespace

SyslogSink::SyslogSink(const char* process_name) {
  openlog(process_name, LOG_NDELAY, LOG_USER);
  absl::AddLogSink(this);
}

SyslogSink::~SyslogSink() {
  absl::RemoveLogSink(this);
  closelog();
}

void SyslogSink::Send(const absl::LogEntry& entry) {
  // Create a timestamp with microsecond resolution.
  struct timeval tv;
  struct timezone tz;
  struct tm time;
  gettimeofday(&tv, &tz);
  localtime_r(&tv.tv_sec, &time);

  // Output format:
  //   I0104 23:00:59.123456    71 filename.cc:100] Your Message Here!
  int severity = static_cast<int>(entry.log_severity());
  syslog(kLogSeverityToSyslog[severity],
         "%c%02d%02d %02d:%02d:%02d.%06ld %5ld %s:%d] %.*s",
         kLogSeverityLetter[severity], 1 + time.tm_mon, time.tm_mday,
         time.tm_hour, time.tm_min, time.tm_sec, static_cast<long>(tv.tv_usec),
         syscall(SYS_gettid), std::string(entry.source_basename()).c_str(),
         entry.source_line(), static_cast<int>(entry.text_message().size()),
         entry.text_message().data());
}

}  // namespace gutil
