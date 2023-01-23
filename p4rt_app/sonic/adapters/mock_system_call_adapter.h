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
#ifndef PINS_INFRA_P4RT_APP_SONIC_ADAPTERS_MOCK_SYSTEM_CALL_ADAPTER_H
#define PINS_INFRA_P4RT_APP_SONIC_ADAPTERS_MOCK_SYSTEM_CALL_ADAPTER_H

#include <stddef.h>
#include <unistd.h>

#include "gmock/gmock.h"
#include "p4rt_app/sonic/adapters/system_call_adapter.h"

namespace p4rt_app {
namespace sonic {

class MockSystemCallAdapter final : public SystemCallAdapter {
 public:
  MOCK_METHOD(ssize_t, read, (int, void*, size_t), (const, override));
  MOCK_METHOD(ssize_t, write, (int, const void*, size_t), (const, override));
  MOCK_METHOD(int, socket, (int, int, int), (const, override));
  MOCK_METHOD(int, connect, (int, const struct sockaddr*, socklen_t),
              (const, override));
  MOCK_METHOD(int, bind, (int, const struct sockaddr*, socklen_t),
              (const, override));
  MOCK_METHOD(int, ioctl, (int, int, struct ifreq*), (const, override));
  MOCK_METHOD(int, setsockopt, (int, int, int, const void*, socklen_t),
              (const, override));
  MOCK_METHOD(unsigned int, if_nametoindex, (const char*), (const, override));
  MOCK_METHOD(int, close, (int), (const, override));
  MOCK_METHOD(int, getifaddrs, (struct ifaddrs**), (const, override));
  MOCK_METHOD(void, freeifaddrs, (struct ifaddrs*), (const, override));
};

}  // namespace sonic
}  // namespace p4rt_app

#endif  // PINS_INFRA_P4RT_APP_SONIC_ADAPTERS_MOCK_SYSTEM_CALL_ADAPTER_H
