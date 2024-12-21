/*
 * Copyright 2020 Google LLC
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
#ifndef PINS_P4RT_APP_SONIC_ADAPTERS_SYSTEM_CALL_ADAPTER_H_
#define PINS_P4RT_APP_SONIC_ADAPTERS_SYSTEM_CALL_ADAPTER_H_

#include <ifaddrs.h>
#include <net/if.h>
#include <stddef.h>
#include <sys/socket.h>
#include <sys/types.h>

namespace p4rt_app {
namespace sonic {

// SystemCallAdapter is a base class that acts as a proxy interface to the Libc
// system calls. The base class virtual methods are just a pass through to the
// Libc system calls.
class SystemCallAdapter {
public:
  SystemCallAdapter() {}
  virtual ~SystemCallAdapter() = default;

  virtual ssize_t read(int fd, void *buf, size_t count) const;
  virtual ssize_t write(int fd, const void *buf, size_t count) const;
  virtual int socket(int domain, int type, int protocol) const;
  virtual int connect(int sockfd, const struct sockaddr *serv_addr,
                      socklen_t addrlen) const;
  virtual int bind(int sockfd, const struct sockaddr *my_addr,
                   socklen_t addrlen) const;
  virtual int ioctl(int fd, int flags, struct ifreq *) const;
  virtual int setsockopt(int sockfd, int level, int optname, const void *optval,
                         socklen_t optlen) const;
  virtual unsigned int if_nametoindex(const char *ifname) const;
  virtual int close(int fd) const;
  virtual int getifaddrs(struct ifaddrs **ifap) const;
  virtual void freeifaddrs(struct ifaddrs *ifa) const;
  // Make option_val int* to support mocking.
  virtual int getsockopt(int socket, int level, int option_name,
                         int *option_value, socklen_t *option_len) const;
};

} // namespace sonic
} // namespace p4rt_app

#endif // PINS_P4RT_APP_SONIC_ADAPTERS_SYSTEM_CALL_ADAPTER_H_
