// RAII wrapper for a 4ward P4Runtime server subprocess.
//
// Starts a 4ward P4RuntimeServer as a child process, waits for it to become
// ready, and terminates it on destruction. The server listens on an
// OS-assigned port; the actual port is parsed from the server's startup banner.
//
// Usage:
//   ASSERT_OK_AND_ASSIGN(FourwardServer server, FourwardServer::Start());
//   // server.Address() == "localhost:<port>"
//   // ... use gRPC to talk to the server ...
//   // Server is killed when `server` goes out of scope.
//
// The cc_library/cc_test that uses this class must list
// `@fourward//p4runtime:p4runtime_server` in its `data` attribute.

#ifndef PINS_FOURWARD_FOURWARD_SERVER_H_
#define PINS_FOURWARD_FOURWARD_SERVER_H_

#include <cstdint>
#include <string>

#include "absl/status/statusor.h"
#include "absl/time/time.h"

namespace dvaas {

class FourwardServer {
 public:
  // Starts a 4ward P4RuntimeServer subprocess. The server binary is resolved
  // from Bazel runfiles (`@fourward//p4runtime:p4runtime_server`).
  //
  // `device_id` is passed to the server via `--device-id`.
  // `startup_timeout` controls how long to wait for the ready banner.
  static absl::StatusOr<FourwardServer> Start(
      uint64_t device_id = 1,
      absl::Duration startup_timeout = absl::Seconds(15));

  FourwardServer(FourwardServer&& other);
  FourwardServer& operator=(FourwardServer&& other);
  FourwardServer(const FourwardServer&) = delete;
  FourwardServer& operator=(const FourwardServer&) = delete;

  ~FourwardServer();

  const std::string& Address() const { return address_; }
  int Port() const { return port_; }
  uint64_t DeviceId() const { return device_id_; }

 private:
  FourwardServer(pid_t pid, int port, uint64_t device_id);
  void Kill();

  pid_t process_id_ = -1;
  int port_ = 0;
  uint64_t device_id_ = 0;
  std::string address_;
};

}  // namespace dvaas

#endif  // PINS_FOURWARD_FOURWARD_SERVER_H_
