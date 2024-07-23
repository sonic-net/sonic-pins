#include "lib/p4rt/packet_listener.h"

namespace pins_test {
PacketListener::PacketListener(
    pdpi::P4RuntimeSession* session, const pdpi::IrP4Info* ir_p4info,
    const absl::flat_hash_map<std::string, std::string>*
        interface_port_id_to_name,
    thinkit::PacketCallback callback)
    : session_(std::move(session)),
      receive_packet_thread_([this, ir_p4info, interface_port_id_to_name,
                              callback = std::move(callback)]() {
        p4::v1::StreamMessageResponse pi_response;
        while (session_->StreamChannelRead(pi_response)) {
          sai::StreamMessageResponse pd_response;
          if (!pdpi::PiStreamMessageResponseToPd(*ir_p4info, pi_response,
                                                 &pd_response)
                   .ok()) {
            LOG(ERROR) << "Failed to convert PI stream message response to PD.";
            return;
          }
          if (!pd_response.has_packet()) {
            LOG(ERROR) << "PD response has no packet.";
            return;
          }
          std::string port_id = pd_response.packet().metadata().ingress_port();
          auto port_name = interface_port_id_to_name->find(port_id);
          if (port_name == interface_port_id_to_name->end()) {
            LOG(WARNING) << port_id << " not found.";
            return;
          }
          callback(port_name->second,
                   absl::BytesToHexString(pd_response.packet().payload()));
        }
      }) {}

}  // namespace pins_test
