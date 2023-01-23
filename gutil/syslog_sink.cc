#include "gutil/syslog_sink.h"

#include <sys/syscall.h>
#include <sys/syslog.h>
#include <sys/time.h>

#include <array>

#include "glog/logging.h"

namespace gutil {
namespace {

// GLOG severity uses integers in the range [0-3]:
//   https://github.com/google/glog/blob/master/src/glog/log_severity.h
constexpr std::array<int, 4> kGlogSeverityToSyslog = {
    LOG_INFO,
    LOG_WARNING,
    LOG_ERR,
    LOG_EMERG,
};
constexpr std::array<char, 4> kGlogSeverityLetter = {
    'I',
    'W',
    'E',
    'F',
};

}  // namespace

SyslogSink::SyslogSink(const char* process_name) {
  openlog(process_name, LOG_NDELAY, LOG_USER);
  google::AddLogSink(this);
}

SyslogSink::~SyslogSink() {
  google::RemoveLogSink(this);
  closelog();
}

void SyslogSink::send(google::LogSeverity severity, const char* full_filename,
                      const char* base_filename, int line,
                      const google::LogMessageTime& logmsgtime,
                      const char* message, size_t message_len) {
  // Create a timestamp with micosecond resolution.
  struct timeval tv;
  struct timezone tz;
  struct tm time;
  gettimeofday(&tv, &tz);
  localtime_r(&tv.tv_sec, &time);

  // Output format:
  //   I0104 23:00:59.123456    71 filename.cc:100] Your Message Here!
  syslog(kGlogSeverityToSyslog[severity],
         "%c%02d%02d %02d:%02d:%02d.%06ld %5ld %s:%d] %.*s",
         kGlogSeverityLetter[severity], 1 + time.tm_mon, time.tm_mday,
         time.tm_hour, time.tm_min, time.tm_sec, static_cast<long>(tv.tv_usec),
         syscall(SYS_gettid), base_filename, line,
         static_cast<int>(message_len), message);
}

}  // namespace gutil
