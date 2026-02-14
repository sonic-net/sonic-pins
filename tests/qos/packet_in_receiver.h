#ifndef PINS_TESTS_QOS_PACKET_IN_RECEIVER_H_
#define PINS_TESTS_QOS_PACKET_IN_RECEIVER_H_

#include <thread>  // NOLINT

#include "absl/synchronization/notification.h"
#include "absl/time/time.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
namespace pins_test {

// Packet receiver thread to receive punted packets from switch over a P4
// session. The callback is invoked serially for every packet received.
// Example:
// PacketInReceiver receiver(
//      p4_session,
//      [&num_packets_punted]() -> absl::Status {
//          num_packets_punted++;
//      });
//      .. do stuff
//      receiver.Destroy();
class PacketInReceiver final {
 public:
  PacketInReceiver(pdpi::P4RuntimeSession &session,
                   std::function<void(p4::v1::StreamMessageResponse)> callback)
      : session_(session), receiver_([this, callback = std::move(callback)]() {
          absl::StatusOr<p4::v1::StreamMessageResponse> pi_response;
          // To break out of this loop invoke Destroy().
          while (!stop_receiving_.HasBeenNotified()) {
            pi_response = session_.GetNextStreamMessage(absl::Seconds(1));
            if (pi_response.ok() && pi_response->has_packet()) {
              callback(*std::move(pi_response));
            }
          }
        }) {}

  PacketInReceiver() = delete;

  // It's ok to call this function multiple times.
  void Destroy() {
    if (receiver_.joinable()) {
      stop_receiving_.Notify();
      receiver_.join();
    }
  }

  ~PacketInReceiver() { Destroy(); }

 private:
  pdpi::P4RuntimeSession &session_;
  std::thread receiver_;
  absl::Notification stop_receiving_;
};

}  // namespace pins_test
#endif  // PINS_TESTS_QOS_PACKET_IN_RECEIVER_H_
