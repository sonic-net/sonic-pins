// Copyright 2021 Google LLC
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
#include "p4rt_app/sonic/receive_genetlink.h"

#include <linux/netlink.h>
#include <net/if.h>
#include <netlink/genl/ctrl.h>
#include <netlink/genl/family.h>
#include <netlink/genl/genl.h>

#include "absl/log/log.h"
#include "gutil/status.h"

namespace packet_metadata {

// The family name, multicast group name and attributes should match what is
// used by the kernel module.
static constexpr char kGenericNetlinkFamilyName[] = "genl_packet";
static constexpr char kGenericNetlinkGroupName[] = "packets";

enum genl_packet_attrs {
  GENL_ATTR_SOURCE_IFINDEX,
  GENL_ATTR_DEST_IFINDEX,
  GENL_ATTR_CONTEXT,
  GENL_ATTR_PAYLOAD,
  GENL_ATTR_MAX
};

// A structure to hold parameters necessary for the Netlink callback function.
struct NetlinkCallbackArgs {
  NetlinkCallbackArgs(struct nla_policy* const genl_attr_policy,
                      ReceiveCallbackFunction callback_function)
      : genl_attr_policy_(genl_attr_policy),
        callback_function_(callback_function) {}
  ~NetlinkCallbackArgs() {
    if (genl_attr_policy_) {
      delete genl_attr_policy_;
    }
  }
  struct nla_policy* const genl_attr_policy_;
  const ReceiveCallbackFunction callback_function_;
};

namespace {

// Open a netlink socket and join the required family and group name.
absl::Status PrepareNetlinkSocket(struct nl_sock** nlsock) {
  *nlsock = nl_socket_alloc();
  if (*nlsock == nullptr) {
    return gutil::InternalErrorBuilder() << "Unable to alloc netlink socket.";
  }

  // Disable automatic request of ACK for every message.
  nl_socket_disable_auto_ack(*nlsock);

  // Connect to generic netlink.
  int error = genl_connect(*nlsock);
  if (error < 0) {
    nl_socket_free(*nlsock);
    return gutil::InternalErrorBuilder()
           << "Unable to connect to generic netlink, error: " << error;
  }

  // Increase Netlink receive buffer allocation from 32K(default) to 1.2MiB,
  // to handle receive packet bursts of upto 16000 pps.
  error = nl_socket_set_buffer_size(*nlsock, 1214400, 0);
  if (error < 0) {
    LOG(WARNING) << "Unable to increase Netlink socket receive buffer size "
                    "from 32K to 1.2MiB, failed with error: "
                 << error;
  }

  // Resolve the generic netlink family id.
  int family_id = genl_ctrl_resolve(*nlsock, kGenericNetlinkFamilyName);
  if (family_id < 0) {
    nl_socket_free(*nlsock);
    return gutil::InternalErrorBuilder()
           << "Unable to resolve generic netlink family name: "
           << kGenericNetlinkFamilyName;
  }

  int group_id = genl_ctrl_resolve_grp(*nlsock, kGenericNetlinkFamilyName,
                                       kGenericNetlinkGroupName);
  if (group_id < 0) {
    nl_socket_free(*nlsock);
    return gutil::InternalErrorBuilder()
           << "Unable to resolve group name for " << kGenericNetlinkGroupName;
  }

  // Join the group.
  error = nl_socket_add_membership(*nlsock, group_id);
  if (error < 0) {
    nl_socket_free(*nlsock);
    return gutil::InternalErrorBuilder()
           << "Unable to join group: " << kGenericNetlinkGroupName
           << " error: " << error;
  }

  return absl::OkStatus();
}

// Convert ifindex to the corresponding interface name.
absl::StatusOr<std::string> GetIfname(int16_t ifindex) {
  RET_CHECK(ifindex >= 0) << "Got an invalid ifindex: " << ifindex;
  // Return empty string for CPU port.
  if (ifindex == 0) return std::string("");
  char ifname[IF_NAMESIZE] = {0};
  RET_CHECK(if_indextoname(ifindex, ifname) != nullptr)
      << "Failed to convert ifindex: " << ifindex
      << " to ifname, errno: " << errno;
  return std::string(ifname);
}

// Process a receive message to retrieve the netlink attribute values.
absl::Status ProcessReceiveMessage(struct nl_msg* msg, void* arg) {
  auto* const nl_cb_args = reinterpret_cast<NetlinkCallbackArgs*>(arg);
  if (nl_cb_args == nullptr) {
    return gutil::UnknownErrorBuilder() << "Failed to get context value";
  }

  struct nlattr* attr[GENL_ATTR_MAX] = {0};
  // Parse the incoming message per the defined netlink attributes.
  int error = genlmsg_parse(nlmsg_hdr(msg), /*hdrlen=*/0, attr, GENL_ATTR_MAX,
                            nl_cb_args->genl_attr_policy_);
  if (error < 0) {
    return gutil::UnknownErrorBuilder() << "Failed to parse, error: " << error;
  }

  std::string source_port_name, target_port_name;
  std::string packet;
  for (int i = 0; i < GENL_ATTR_MAX; i++) {
    if (attr[i]) {
      switch (i) {
        case GENL_ATTR_SOURCE_IFINDEX: {
          /*G3_WA*/
          auto port = nla_get_u16(attr[i]);
          const auto name_or = GetIfname(port);
          if (name_or.ok()) {
            source_port_name = *name_or;
          } else {
            LOG(WARNING) << "Unable to get source port from the packet "
                            "metadata, error: "
                         << name_or.status();
          }
          break;
        }
        case GENL_ATTR_DEST_IFINDEX: {
          auto port = nla_get_u16(attr[i]);
          const auto name_or = GetIfname(port);
          if (name_or.ok()) {
            target_port_name = *name_or;
          } else {
            // This message is only logged once every minute to avoid spamming
            LOG_EVERY_N_SEC(WARNING, 60) << "Unable to get target egress port "
                                            "from the packet metadata, error: "
                                         << name_or.status();
          }
          break;
        }
        case GENL_ATTR_CONTEXT: {
          break;
        }
        case GENL_ATTR_PAYLOAD: {
          packet = std::string(static_cast<const char*>(nla_data(attr[i])),
                               static_cast<size_t>(nla_len(attr[i])));
          break;
        }
        default: {
          LOG(WARNING) << "Unexpected Netlink attribute " << i
                       << "in the packet metadata";
          break;
        }
      }
    }
  }

  if (packet.empty()) {
    return gutil::UnknownErrorBuilder() << "Empty payload, skipping.";
  }

  if (source_port_name.empty()) {
    return gutil::UnknownErrorBuilder()
           << "No source port, skipping this packet.";
  }

  RETURN_IF_ERROR((nl_cb_args->callback_function_)(source_port_name,
                                                   target_port_name, packet))
          .SetPrepend()
      << "Callback function failed for the receive packet with error: ";

  return absl::OkStatus();
}

int ProcessReceiveMessageCallback(struct nl_msg* msg, void* arg) {
  auto status = ProcessReceiveMessage(msg, arg);
  if (!status.ok()) {
    LOG_EVERY_N_SEC(WARNING, 5)
        << "Failed to process receive packet: " << status.ToString();
  }
  // Always return OK to move on to the next packet.
  return NL_OK;
}

static void ReceiveThread(struct nl_sock* nlsock, struct nl_cb* cb) {
  LOG(INFO) << "Successfully created Netlink Receive thread";
  // Blocking call to receive packets on the Netlink socket.
  while (true) {
    int error = nl_recvmsgs(nlsock, cb);
    // Packet processing happens in the ProcessReceiveMessageCallback()
    // function.
    if (error < 0) {
      LOG(WARNING)
          << "Failed in receive message callback from netlink socket, error: "
          << error;
    }
  }
  // Never expect to be here.
}

}  // namespace

absl::StatusOr<std::thread> StartReceive(
    ReceiveCallbackFunction callback_function) {
  struct nl_sock* nlsock = nullptr;
  struct nl_cb* cb = nullptr;

  RETURN_IF_ERROR(PrepareNetlinkSocket(&nlsock));

  // Set the receive policies for all netlink packet attribures.
  auto* genl_attr_policy = new struct nla_policy[GENL_ATTR_MAX];
  memset(genl_attr_policy, 0, sizeof(struct nla_policy) * GENL_ATTR_MAX);
  // TODO: google3 supports only unsigned.
  genl_attr_policy[GENL_ATTR_SOURCE_IFINDEX].type = NLA_U16;  // G3_WA
  genl_attr_policy[GENL_ATTR_DEST_IFINDEX].type = NLA_U16;    // G3_WA
  genl_attr_policy[GENL_ATTR_CONTEXT].type = NLA_U32;
  genl_attr_policy[GENL_ATTR_PAYLOAD].type = NLA_UNSPEC;

  // Register the callback function for receive packet processing.
  cb = nl_cb_alloc(NL_CB_DEFAULT);
  auto* nl_cb_args =
      new NetlinkCallbackArgs(genl_attr_policy, callback_function);
  nl_cb_set(cb, NL_CB_VALID, NL_CB_CUSTOM, ProcessReceiveMessageCallback,
            reinterpret_cast<void*>(nl_cb_args));

  // Create Receive thread to receive packets from the socket.
  std::thread receive_thread(ReceiveThread, nlsock, cb);

  return receive_thread;
}

}  // namespace packet_metadata
