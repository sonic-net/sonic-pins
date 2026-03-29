#include "fourward/fourward_server.h"

#include <fcntl.h>
#include <signal.h>
#include <sys/wait.h>
#include <unistd.h>

#include <cerrno>
#include <cstdint>
#include <cstring>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/string_view.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "gutil/status.h"
#include "tools/cpp/runfiles/runfiles.h"

namespace dvaas {
namespace {

absl::StatusOr<std::string> ResolveFourwardServerBinary() {
  using ::bazel::tools::cpp::runfiles::Runfiles;
  std::string error;
  std::unique_ptr<Runfiles> runfiles(Runfiles::Create("", &error));
  if (runfiles == nullptr) {
    return absl::InternalError(
        absl::StrCat("Failed to create Runfiles: ", error));
  }
  return runfiles->Rlocation("fourward/p4runtime/p4runtime_server");
}

constexpr absl::string_view kReadyBanner = "listening on port ";

absl::StatusOr<int> ParsePortFromBanner(absl::string_view line) {
  size_t pos = line.find(kReadyBanner);
  if (pos == absl::string_view::npos) {
    return absl::NotFoundError(
        absl::StrCat("Ready banner not found in: ", line));
  }
  absl::string_view port_str = line.substr(pos + kReadyBanner.size());
  int port;
  if (!absl::SimpleAtoi(port_str, &port)) {
    return absl::InvalidArgumentError(
        absl::StrCat("Failed to parse port from: ", port_str));
  }
  return port;
}

absl::StatusOr<int> WaitForReadyBanner(int fd, absl::Duration timeout) {
  absl::Time deadline = absl::Now() + timeout;
  std::string buffer;

  int flags = fcntl(fd, F_GETFL, 0);
  fcntl(fd, F_SETFL, flags | O_NONBLOCK);

  while (absl::Now() < deadline) {
    char chunk[1024];
    ssize_t n = read(fd, chunk, sizeof(chunk) - 1);
    if (n > 0) {
      chunk[n] = '\0';
      buffer.append(chunk, n);
      size_t pos;
      while ((pos = buffer.find('\n')) != std::string::npos) {
        std::string line = buffer.substr(0, pos);
        buffer.erase(0, pos + 1);
        absl::StatusOr<int> port = ParsePortFromBanner(line);
        if (port.ok()) return *port;
      }
      absl::StatusOr<int> port = ParsePortFromBanner(buffer);
      if (port.ok()) return *port;
    } else if (n == 0) {
      return absl::InternalError("Server process closed stdout unexpectedly");
    } else if (errno != EAGAIN && errno != EWOULDBLOCK) {
      return absl::InternalError(
          absl::StrCat("Read error: ", std::strerror(errno)));
    }
    absl::SleepFor(absl::Milliseconds(50));
  }
  return absl::DeadlineExceededError(absl::StrFormat(
      "4ward server did not produce ready banner within %s", timeout));
}

void ClearBazelEnvironment() {
  unsetenv("BUILD_WORKSPACE_DIRECTORY");
  unsetenv("BUILD_WORKING_DIRECTORY");
}

}  // namespace

FourwardServer::FourwardServer(pid_t pid, int port, uint64_t device_id)
    : process_id_(pid),
      port_(port),
      device_id_(device_id),
      address_(absl::StrCat("localhost:", port)) {}

FourwardServer::FourwardServer(FourwardServer&& other)
    : process_id_(other.process_id_),
      port_(other.port_),
      device_id_(other.device_id_),
      address_(std::move(other.address_)) {
  other.process_id_ = -1;
}

FourwardServer& FourwardServer::operator=(FourwardServer&& other) {
  if (this != &other) {
    Kill();
    process_id_ = other.process_id_;
    port_ = other.port_;
    device_id_ = other.device_id_;
    address_ = std::move(other.address_);
    other.process_id_ = -1;
  }
  return *this;
}

FourwardServer::~FourwardServer() { Kill(); }

void FourwardServer::Kill() {
  if (process_id_ <= 0) return;

  kill(process_id_, SIGTERM);

  absl::Time deadline = absl::Now() + absl::Seconds(5);
  while (absl::Now() < deadline) {
    int status;
    pid_t result = waitpid(process_id_, &status, WNOHANG);
    if (result == process_id_) {
      process_id_ = -1;
      return;
    }
    absl::SleepFor(absl::Milliseconds(100));
  }

  kill(process_id_, SIGKILL);
  waitpid(process_id_, nullptr, 0);
  process_id_ = -1;
}

absl::StatusOr<FourwardServer> FourwardServer::Start(
    uint64_t device_id, absl::Duration startup_timeout) {
  ASSIGN_OR_RETURN(std::string binary_path, ResolveFourwardServerBinary());

  int stdout_pipe[2];
  if (pipe(stdout_pipe) != 0) {
    return absl::InternalError(
        absl::StrCat("pipe() failed: ", std::strerror(errno)));
  }

  pid_t pid = fork();
  if (pid < 0) {
    close(stdout_pipe[0]);
    close(stdout_pipe[1]);
    return absl::InternalError(
        absl::StrCat("fork() failed: ", std::strerror(errno)));
  }

  if (pid == 0) {
    // Child process.
    close(stdout_pipe[0]);  // Close read end.
    dup2(stdout_pipe[1], STDOUT_FILENO);
    dup2(stdout_pipe[1], STDERR_FILENO);
    close(stdout_pipe[1]);

    ClearBazelEnvironment();

    std::string port_flag = "--port=0";
    std::string device_id_flag =
        absl::StrCat("--device-id=", device_id);

    std::vector<const char*> argv = {
        binary_path.c_str(),
        port_flag.c_str(),
        device_id_flag.c_str(),
        nullptr,
    };

    execv(binary_path.c_str(), const_cast<char* const*>(argv.data()));
    _exit(127);
  }

  // Parent process.
  close(stdout_pipe[1]);  // Close write end.

  absl::StatusOr<int> port = WaitForReadyBanner(stdout_pipe[0], startup_timeout);
  close(stdout_pipe[0]);

  if (!port.ok()) {
    kill(pid, SIGKILL);
    waitpid(pid, nullptr, 0);
    return port.status();
  }

  return FourwardServer(pid, *port, device_id);
}

}  // namespace dvaas
