// Copyright 2024 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "tests/sflow/sflow_util.h"

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "lib/utils/json_utils.h"

namespace pins {
namespace {
using ::gutil::StatusIs;
using ::testing::HasSubstr;

TEST(SflowconfigTest, AppendSflowConfigSuccess) {
  const std::string kOpenConfig = R"({
    "openconfig-interfaces:interfaces":{
      "interface":[
        {
          "name":"bond0",
          "state":{"oper-status":"UP","openconfig-p4rt:id":1}
        }
      ]
    }
  })";
  const std::string kSflowConfig = R"({
    "openconfig-interfaces:interfaces":{
      "interface":[
        {
          "name":"bond0",
          "state":{"oper-status":"UP","openconfig-p4rt:id":1}
        }
      ]
    },
     "openconfig-sampling:sampling" : {
        "openconfig-sampling-sflow:sflow" : {
           "collectors" : {
              "collector" : [
                 {
                    "address" : "2001:4860:f802::be",
                    "config" : {
                       "address" : "2001:4860:f802::be",
                       "port" : 6343
                    },
                    "port" : 6343
                 }
              ]
           },
           "config" : {
              "agent-id-ipv6" : "8002:12::aab0",
              "enabled" : true,
              "polling-interval" : 0,
              "sample-size" : 128
           },
           "interfaces" : {
              "interface" : [
                 {
                    "config" : {
                       "enabled" : true,
                       "name" : "Ethernet1",
                       "ingress-sampling-rate" : 1000
                    },
                    "name" : "Ethernet1"
                 },
                 {
                    "config" : {
                       "enabled" : true,
                       "name" : "Ethernet2",
                       "ingress-sampling-rate" : 1000
                    },
                    "name" : "Ethernet2"
                 }
             ]
           }
        }
     }
  })";
  ASSERT_OK_AND_ASSIGN(
      auto json_str,
      AppendSflowConfigIfNotPresent(
          kOpenConfig,
          /*agent_addr_ipv6=*/"8002:12::aab0",
          /*collector_address_to_port=*/{{"2001:4860:f802::be", 6343}},
          /*sflow_enabled_interfaces=*/{"Ethernet1", "Ethernet2"},
          /*sampling_rate=*/1000,
          /*sampling_header_size=*/128));
  ASSERT_EQ(::nlohmann::json::parse(json_str),
            ::nlohmann::json::parse(kSflowConfig));
}

TEST(SflowconfigTest, AppendSflowConfigNoopIfPresent) {
  const std::string kGnmiConfig = R"({
    "openconfig-interfaces:interfaces":{
      "interface":[
        {
          "name":"bond0",
          "state":{"oper-status":"UP","openconfig-p4rt:id":1}
        }
      ]
    },
     "openconfig-sampling:sampling" : {
        "openconfig-sampling-sflow:sflow" : {
           "collectors" : {
              "collector" : [
                 {
                    "address" : "2001:4860:f802::be",
                    "config" : {
                       "address" : "2001:4860:f802::be",
                       "port" : 6343
                    },
                    "port" : 6343
                 }
              ]
           },
           "config" : {
              "agent-id-ipv6" : "8002:12::aab0",
              "enabled" : true,
              "polling-interval" : 0,
              "sample-size" : 128
           },
           "interfaces" : {
              "interface" : [
                 {
                    "config" : {
                       "enabled" : true,
                       "name" : "Ethernet1",
                       "ingress-sampling-rate" : 1000
                    },
                    "name" : "Ethernet1"
                 },
                 {
                    "config" : {
                       "enabled" : true,
                       "name" : "Ethernet2",
                       "ingress-sampling-rate" : 1000
                    },
                    "name" : "Ethernet2"
                 }
             ]
           }
        }
     }
  })";
  ASSERT_OK_AND_ASSIGN(
      auto json_str,
      AppendSflowConfigIfNotPresent(
          kGnmiConfig,
          /*agent_addr_ipv6=*/"8002:12::aab0",
          /*collector_address_to_port=*/{{"12:34:56::78", 6343}},
          /*sflow_enabled_interfaces=*/{"Ethernet3", "Ethernet4"},
          /*sampling_rate=*/100,
          /*sampling_header_size=*/12));
  ASSERT_EQ(::nlohmann::json::parse(json_str),
            ::nlohmann::json::parse(kGnmiConfig));
}

TEST(SflowconfigTest, AppendSflowConfigWrongParameterFail) {
  EXPECT_THAT(
      AppendSflowConfigIfNotPresent(
          /*gnmi_config=*/"",
          /*agent_addr_ipv6=*/"",
          /*collector_address_to_port=*/{{"2001:4860:f802::be", 6343}},
          /*sflow_enabled_interfaces=*/{"Ethernet1", "Ethernet2"},
          /*sampling_rate=*/1000,
          /*sampling_header_size=*/128),
      StatusIs(absl::StatusCode::kInvalidArgument,
               HasSubstr("loopback_address parameter cannot be empty.")));
  EXPECT_THAT(
      AppendSflowConfigIfNotPresent(
          /*gnmi_config=*/"",
          /*agent_addr_ipv6=*/"8002:12::aab0",
          /*collector_address_to_port=*/{{"2001:4860:f802::be", 6343}},
          /*sflow_enabled_interfaces=*/{},
          /*sampling_rate=*/1000,
          /*sampling_header_size=*/128),
      StatusIs(
          absl::StatusCode::kInvalidArgument,
          HasSubstr("sflow_enabled_interfaces parameter cannot be empty.")));
}

}  // namespace
}  // namespace pins
