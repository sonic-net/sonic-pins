// Copyright 2022 Google LLC
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
#ifndef PINS_INFRA_P4RT_APP_SONIC_ADAPTERS_FAKE_INTF_TRANSLATOR_H_
#define PINS_INFRA_P4RT_APP_SONIC_ADAPTERS_FAKE_INTF_TRANSLATOR_H_

#include "swss/intf_translator.h"

namespace p4rt_app {
namespace sonic {

class FakeIntfTranslator final : public swss::IntfTranslator {
 public:
  FakeIntfTranslator(bool enabled)
      : swss::IntfTranslator(nullptr), enabled_(enabled) {}

  std::string translateToLinux(const std::string& intf) const override;
  std::string translateFromLinux(const std::string& intf) const override;

 private:
  bool enabled_;
};

}  // namespace sonic
}  // namespace p4rt_app

#endif  // PINS_INFRA_P4RT_APP_SONIC_ADAPTERS_FAKE_INTF_TRANSLATOR_H_
