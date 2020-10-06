// Copyright 2020 Google LLC
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

#include "p4rt_app/sonic/adapters/system_call_adapter.h"

#include <sys/ioctl.h>
#include <unistd.h>

namespace p4rt_app {
namespace sonic {

// Direct passthrough of the methods to call the corresponding system calls.
ssize_t SystemCallAdapter::read(int fd, void *buf, size_t count) const {
  return ::read(fd, buf, count);
}

ssize_t SystemCallAdapter::write(int fd, const void *buf, size_t count) const {
  return ::write(fd, buf, count);
}

int SystemCallAdapter::socket(int domain, int type, int protocol) const {
  return ::socket(domain, type, protocol);
}

int SystemCallAdapter::connect(int sockfd, const struct sockaddr *serv_addr,
                               socklen_t addrlen) const {
  return ::connect(sockfd, serv_addr, addrlen);
}

int SystemCallAdapter::bind(int sockfd, const struct sockaddr *my_addr,
                            socklen_t addrlen) const {
  return ::bind(sockfd, my_addr, addrlen);
}

int SystemCallAdapter::ioctl(int fd, int flags, struct ifreq *ifreq) const {
  return ::ioctl(fd, flags, ifreq);
}

int SystemCallAdapter::setsockopt(int sockfd, int level, int optname,
                                  const void *optval, socklen_t optlen) const {
  return ::setsockopt(sockfd, level, optname, optval, optlen);
}

unsigned int SystemCallAdapter::if_nametoindex(const char *ifname) const {
  return ::if_nametoindex(ifname);
}

int SystemCallAdapter::close(int fd) const { return ::close(fd); }

int SystemCallAdapter::getifaddrs(struct ifaddrs **ifap) const {
  return ::getifaddrs(ifap);
}

void SystemCallAdapter::freeifaddrs(struct ifaddrs *ifa) const {
  ::freeifaddrs(ifa);
}

}  // namespace sonic
}  // namespace p4rt_app
