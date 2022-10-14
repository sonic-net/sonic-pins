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

#include "absl/container/flat_hash_set.h"
#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "proto/gnmi/gnmi_mock.grpc.pb.h"

namespace pins {
namespace {
using ::gutil::IsOkAndHolds;
using ::gutil::StatusIs;
using ::testing::DoAll;
using ::testing::Eq;
using ::testing::HasSubstr;
using ::testing::Return;
using ::testing::SetArgPointee;
using ::testing::UnorderedPointwise;

constexpr absl::string_view kGnmiConfig = R"json({

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
  })json";

constexpr absl::string_view kResultJson = R"json({
  "openconfig-interfaces:interfaces": {
    "interface": [
      {
        "name": "bond0",
        "state": {
          "openconfig-p4rt:id": 1,
          "oper-status": "UP"
        }
      }
    ]
  },
  "openconfig-sampling:sampling": {
    "openconfig-sampling-sflow:sflow": {
      "collectors": {
        "collector": [
          {
            "address": "2001:4860:f802::be",
            "config": {
              "address": "2001:4860:f802::be",
              "port": 6343
            },
            "port": 6343
          },
          {
            "address": "12:34:56::78",
            "config": {
              "address": "12:34:56::78",
              "port": 6343
            },
            "port": 6343
          }
        ]
      },
      "config": {
        "agent-id-ipv6": "8002:12::aab0",
        "enabled": true,
        "polling-interval": 0,
        "sample-size": 12
      },
      "interfaces": {
        "interface": [
          {
            "config": {
              "enabled": true,
              "ingress-sampling-rate": 1000,
              "name": "Ethernet1"
            },
            "name": "Ethernet1"
          },
          {
            "config": {
              "enabled": true,
              "ingress-sampling-rate": 1000,
              "name": "Ethernet2"
            },
            "name": "Ethernet2"
          },
          {
            "config": {
              "enabled": true,
              "ingress-sampling-rate": 1000,
              "name": "Ethernet3"
            },
            "name": "Ethernet3"
          },
          {
            "config": {
              "enabled": true,
              "ingress-sampling-rate": 1000,
              "name": "Ethernet4"
            },
            "name": "Ethernet4"
          }
        ]
      }
    }
  }
})json";

TEST(SflowconfigTest, SflowEnabledTrue) {
  const std::string sflow_config = R"json({
  "openconfig-sampling:sampling": {
    "openconfig-sampling-sflow:sflow": {
      "config": {
        "agent-id-ipv6": "8002:12::aab0",
        "enabled": true,
        "polling-interval": 0,
        "sample-size": 12
      }
    }
  }
})json";
  EXPECT_THAT(IsSflowConfigEnabled(sflow_config), IsOkAndHolds(true));
}

TEST(SflowconfigTest, SflowEnabledFalse) {
  const std::string sflow_config = R"json({
  "openconfig-sampling:sampling": {
    "openconfig-sampling-sflow:sflow": {
      "config": {
        "agent-id-ipv6": "8002:12::aab0",
        "enabled": false,
        "polling-interval": 0,
        "sample-size": 12
      }
    }
  }
})json";
  EXPECT_THAT(IsSflowConfigEnabled(sflow_config), IsOkAndHolds(false));
}

TEST(SflowconfigTest, NoSflowConfigEnabledFalse) {
  const std::string interface_config = R"json({
  "openconfig-interfaces:interfaces": {
    "interface": [
      {
        "name": "bond0",
        "state": {
          "openconfig-p4rt:id": 1,
          "oper-status": "UP"
        }
      }
    ]
  }
})json";
  EXPECT_THAT(IsSflowConfigEnabled(interface_config), IsOkAndHolds(false));
}

TEST(SflowconfigTest, AppendSflowConfigSuccess) {
  EXPECT_THAT(
      UpdateSflowConfig(kGnmiConfig,
                        /*agent_addr_ipv6=*/"8002:12::aab0",
                        /*collector_address_to_port=*/{{"12:34:56::78", 6343}},
                        /*sflow_enabled_interfaces=*/{"Ethernet3", "Ethernet4"},
                        /*sampling_rate=*/1000,
                        /*sampling_header_size=*/12),
      IsOkAndHolds(kResultJson));
}

TEST(SflowconfigTest, ModifyCollectorIpSuccess) {
  EXPECT_THAT(
      UpdateSflowConfig(kGnmiConfig,
                        /*agent_addr_ipv6=*/"8002:12::aab0",
                        /*collector_address_to_port=*/
                        {{"12:34:56::78", 6343}, {"2001:4860:f802::be", 6343}},
                        /*sflow_enabled_interfaces=*/{"Ethernet3", "Ethernet4"},
                        /*sampling_rate=*/1000,
                        /*sampling_header_size=*/12),
      IsOkAndHolds(kResultJson));
}

TEST(SflowconfigTest, ModifyInterfaceNamesSuccess) {
  EXPECT_THAT(
      UpdateSflowConfig(kGnmiConfig,
                        /*agent_addr_ipv6=*/"8002:12::aab0",
                        /*collector_address_to_port=*/
                        {{"12:34:56::78", 6343}},
                        /*sflow_enabled_interfaces=*/
                        {"Ethernet1", "Ethernet2", "Ethernet3", "Ethernet4"},
                        /*sampling_rate=*/1000,
                        /*sampling_header_size=*/12),
      IsOkAndHolds(kResultJson));
}

TEST(SflowconfigTest, ModifySamplingRateSuccess) {
  EXPECT_THAT(UpdateSflowConfig(kGnmiConfig,
                                /*agent_addr_ipv6=*/"8002:12::aab0",
                                /*collector_address_to_port=*/
                                {},
                                /*sflow_enabled_interfaces=*/
                                {"Ethernet2", "Ethernet3"},
                                /*sampling_rate=*/512,
                                /*sampling_header_size=*/12),
              IsOkAndHolds(
                  R"json({
  "openconfig-interfaces:interfaces": {
    "interface": [
      {
        "name": "bond0",
        "state": {
          "openconfig-p4rt:id": 1,
          "oper-status": "UP"
        }
      }
    ]
  },
  "openconfig-sampling:sampling": {
    "openconfig-sampling-sflow:sflow": {
      "collectors": {
        "collector": [
          {
            "address": "2001:4860:f802::be",
            "config": {
              "address": "2001:4860:f802::be",
              "port": 6343
            },
            "port": 6343
          }
        ]
      },
      "config": {
        "agent-id-ipv6": "8002:12::aab0",
        "enabled": true,
        "polling-interval": 0,
        "sample-size": 12
      },
      "interfaces": {
        "interface": [
          {
            "config": {
              "enabled": true,
              "ingress-sampling-rate": 1000,
              "name": "Ethernet1"
            },
            "name": "Ethernet1"
          },
          {
            "config": {
              "enabled": true,
              "ingress-sampling-rate": 512,
              "name": "Ethernet2"
            },
            "name": "Ethernet2"
          },
          {
            "config": {
              "enabled": true,
              "ingress-sampling-rate": 512,
              "name": "Ethernet3"
            },
            "name": "Ethernet3"
          }
        ]
      }
    }
  }
})json"));

}

TEST(SflowconfigTest, AppendSflowConfigWrongParameterFail) {
  EXPECT_THAT(
      UpdateSflowConfig(
          /*gnmi_config=*/"",
          /*agent_addr_ipv6=*/"",
          /*collector_address_to_port=*/{{"2001:4860:f802::be", 6343}},
          /*sflow_enabled_interfaces=*/{"Ethernet1", "Ethernet2"},
          /*sampling_rate=*/1000,
          /*sampling_header_size=*/128),
      StatusIs(absl::StatusCode::kInvalidArgument,
               HasSubstr("agent_addr_ipv6 parameter cannot be empty.")));
  EXPECT_THAT(
      UpdateSflowConfig(
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

// Changes pir-pkts for BE1 from 120 to 1000.
TEST(SflowconfigTest, UpdateSflowQueueLimitSuccess) {
  constexpr absl::string_view sflow_config = R"json({
    "openconfig-interfaces:interfaces":{
      "interface":[
        {
          "name":"bond0",
          "state":{"oper-status":"UP","openconfig-p4rt:id":1}
        }
      ]
    },
    "openconfig-qos:qos": {
      "interfaces": {
        "interface": [
          {
               "config" : {
                  "interface-id" : "CPU"
               },
               "interface-id" : "CPU",
               "output" : {
                  "scheduler-policy" : {
                     "config" : {
                        "name" : "cpu_scheduler"
                     }
                  }
               }
            }
        ]
      },
      "scheduler-policies": {
        "scheduler-policy": [
          {
               "config" : {
                  "name" : "cpu_scheduler"
               },
               "name" : "cpu_scheduler",
               "schedulers" : {
                  "scheduler" : [
                     {
                        "config" : {
                           "priority" : "STRICT",
                           "sequence" : 0,
                           "type" : "openconfig-qos-types:TWO_RATE_THREE_COLOR"
                        },
                        "inputs" : {
                           "input" : [
                              {
                                 "config" : {
                                    "id" : "NC1",
                                    "input-type" : "QUEUE",
                                    "queue" : "NC1"
                                 },
                                 "id" : "NC1"
                              }
                           ]
                        },
                        "sequence" : 0,
                        "two-rate-three-color" : {
                           "config" : {
                              "google-pins-qos:bc-pkts" : 0,
                              "google-pins-qos:be-pkts" : 256,
                              "google-pins-qos:cir-pkts" : "0",
                              "google-pins-qos:pir-pkts" : "16000"
                           }
                        }
                     },
                     {
                        "config" : {
                           "priority" : "STRICT",
                           "sequence" : 5,
                           "type" : "openconfig-qos-types:TWO_RATE_THREE_COLOR"
                        },
                        "inputs" : {
                           "input" : [
                              {
                                 "config" : {
                                    "id" : "BE1",
                                    "input-type" : "QUEUE",
                                    "queue" : "BE1"
                                 },
                                 "id" : "BE1"
                              }
                           ]
                        },
                        "sequence" : 5,
                        "two-rate-three-color" : {
                           "config" : {
                              "google-pins-qos:bc-pkts" : 0,
                              "google-pins-qos:be-pkts" : 4,
                              "google-pins-qos:cir-pkts" : "0",
                              "google-pins-qos:pir-pkts" : "120"
                           }
                        }
                     }
                  ]
               }
            }
        ]
      }
    }
  })json";
  EXPECT_THAT(UpdateQueueLimit(sflow_config, /*queue_name=*/"BE1",
                               /*queue_limit=*/1000),
              IsOkAndHolds(R"json({
  "openconfig-interfaces:interfaces": {
    "interface": [
      {
        "name": "bond0",
        "state": {
          "openconfig-p4rt:id": 1,
          "oper-status": "UP"
        }
      }
    ]
  },
  "openconfig-qos:qos": {
    "interfaces": {
      "interface": [
        {
          "config": {
            "interface-id": "CPU"
          },
          "interface-id": "CPU",
          "output": {
            "scheduler-policy": {
              "config": {
                "name": "cpu_scheduler"
              }
            }
          }
        }
      ]
    },
    "scheduler-policies": {
      "scheduler-policy": [
        {
          "config": {
            "name": "cpu_scheduler"
          },
          "name": "cpu_scheduler",
          "schedulers": {
            "scheduler": [
              {
                "config": {
                  "priority": "STRICT",
                  "sequence": 0,
                  "type": "openconfig-qos-types:TWO_RATE_THREE_COLOR"
                },
                "inputs": {
                  "input": [
                    {
                      "config": {
                        "id": "NC1",
                        "input-type": "QUEUE",
                        "queue": "NC1"
                      },
                      "id": "NC1"
                    }
                  ]
                },
                "sequence": 0,
                "two-rate-three-color": {
                  "config": {
                    "google-pins-qos:bc-pkts": 0,
                    "google-pins-qos:be-pkts": 256,
                    "google-pins-qos:cir-pkts": "0",
                    "google-pins-qos:pir-pkts": "16000"
                  }
                }
              },
              {
                "config": {
                  "priority": "STRICT",
                  "sequence": 5,
                  "type": "openconfig-qos-types:TWO_RATE_THREE_COLOR"
                },
                "inputs": {
                  "input": [
                    {
                      "config": {
                        "id": "BE1",
                        "input-type": "QUEUE",
                        "queue": "BE1"
                      },
                      "id": "BE1"
                    }
                  ]
                },
                "sequence": 5,
                "two-rate-three-color": {
                  "config": {
                    "google-pins-qos:bc-pkts": 0,
                    "google-pins-qos:be-pkts": 4,
                    "google-pins-qos:cir-pkts": "0",
                    "google-pins-qos:pir-pkts": "1000"
                  }
                }
              }
            ]
          }
        }
      ]
    }
  }
})json"));
}

TEST(SflowconfigTest, UpdateSflowQueueFailedMissingCpuSchedulerPolicy) {
  EXPECT_THAT(
      UpdateQueueLimit(kGnmiConfig, /*queue_name=*/"BE1", /*queue_limit=*/1000),
      StatusIs(
          absl::StatusCode::kInvalidArgument,
          HasSubstr("Gnmi config does not have any cpu scheduler policy.")));
}

TEST(SflowUtilTest, GetSampleRateSuccessForAllInterfaces) {
  gnmi::MockgNMIStub stub;
  ON_CALL(stub, Get).WillByDefault(DoAll(
      SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
          R"pb(
            notification {
              timestamp: 1664239058571609826
              prefix { origin: "openconfig" }
              update {
                val {
                  json_ietf_val: "{\"openconfig-sampling-sflow:ingress-sampling-rate\":256}"
                }
              }
            })pb")),
      Return(grpc::Status::OK)));
  absl::flat_hash_set<std::string> interfaces{"Ethernet1/1/1",
                                              "Ethernet1/31/5"};
  const absl::flat_hash_map<std::string, int> expected_map = {
      {"Ethernet1/1/1", 256}, {"Ethernet1/31/5", 256}};
  EXPECT_THAT(GetSflowSamplingRateForInterfaces(&stub, interfaces),
              IsOkAndHolds(UnorderedPointwise(Eq(), expected_map)));
}

TEST(SflowUtilTest, UpdateQueueLimitSucceed) {
  const int kQueueNumberForBE1 = 5;
  gnmi::MockgNMIStub stub;
  ON_CALL(stub, Get).WillByDefault(DoAll(
      SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
          R"pb(notification {
                 timestamp: 1664316653291898311
                 prefix { origin: "openconfig" }
                 update {
                   path {
                     elem { name: "openconfig-qos:qos" }
                     elem { name: "scheduler-policies" }
                     elem {
                       name: "scheduler-policy"
                       key { key: "name" value: "cpu_scheduler" }
                     }
                     elem { name: "schedulers" }
                     elem {
                       name: "scheduler"
                       key { key: "sequence" value: "5" }
                     }
                     elem { name: "two-rate-three-colo" }
                     elem { name: "state" }
                   }
                   val {
                     json_ietf_val: "{\"openconfig-qos:state\":{\"google-pins-qos:bc-pkts\":0,\"google-pins-qos:be-pkts\":4,\"google-pins-qos:cir-pkts\":\"0\",\"google-pins-qos:pir-pkts\":\"120\"}}"
                   }
                 }
               })pb")),
      Return(grpc::Status::OK)));
  ASSERT_OK(VerifySflowQueueLimitState(&stub, kQueueNumberForBE1,
                                       /*expected_queue_limit=*/120));
}

TEST(SflowDscpTest, ParseTcpdumpResultA1Success) {
  const std::string tcpdump_result =
      R"(tcpdump: listening on lo, link-type EN10MB (Ethernet), capture size "
      "262144 bytes 18:10:50.401908 00:00:00:00:00:00 (oui Ethernet) > "
      "00:00:00:00:00:00 (oui Ethernet), ethertype IPv6 (0x86dd), length 230: "
      "(class 0xa1, flowlabel 0x20016, hlim 127, next-header UDP (17) payload "
      "length: 176) localhost.56223 > localhost.6343: [bad udp cksum 0x00c3 -> "
      "0x6a10!] sFlowv5, IPv6 agent 38.7.248.176, agent-id 2157511939, seqnum "
      "0, uptime 0, samples 100000, length 168 flow sample (1), length "
      "50018,[|SFLOW] 0x0000:  6802 0016 00b0 117f 0000 0000 0000 0000  "
      "h...............)";
  ASSERT_THAT(ExtractTosFromTcpdumpResult(tcpdump_result), IsOkAndHolds(161));
}

TEST(SflowDscpTest, ParseTcpdumpResultFFSuccess) {
  const std::string tcpdump_result =
      R"(tcpdump: listening on lo, link-type EN10MB (Ethernet), capture size "
      "262144 bytes 18:10:50.401908 00:00:00:00:00:00 (oui Ethernet) > "
      "00:00:00:00:00:00 (oui Ethernet), ethertype IPv6 (0x86dd), length 230: "
      "(class 0xff, flowlabel 0x20016, hlim 127, next-header UDP (17) payload "
      "length: 176) localhost.56223 > localhost.6343: [bad udp cksum 0x00c3 -> "
      "0x6a10!] sFlowv5, IPv6 agent 38.7.248.176, agent-id 2157511939, seqnum "
      "0, uptime 0, samples 100000, length 168 flow sample (1), length "
      "50018,[|SFLOW] 0x0000:  6802 0016 00b0 117f 0000 0000 0000 0000  "
      "h...............)";
  ASSERT_THAT(ExtractTosFromTcpdumpResult(tcpdump_result), IsOkAndHolds(255));
}

TEST(SflowDscpTest, ParseTcpdumpResultFailure) {
  const std::string tcpdump_result =
      R"(tcpdump: listening on lo, link-type EN10MB (Ethernet), capture size "
      "262144 bytes 18:10:50.401908 00:00:00:00:00:00 (oui Ethernet) > "
      "00:00:00:00:00:00 (oui Ethernet), ethertype IPv6 (0x86dd), length 230: "
      "(flowlabel 0x20016, hlim 127, next-header UDP (17) payload length: 176) "
      "localhost.56223 > localhost.6343: [bad udp cksum 0x00c3 -> 0x6a10!] "
      "sFlowv5, IPv6 agent 38.7.248.176, agent-id 2157511939, seqnum 0, uptime "
      "0, samples 100000, length 168 flow sample (1), length 50018,[|SFLOW] "
      "0x0000:  6802 0016 00b0 117f 0000 0000 0000 0000  h...............)";
  ASSERT_THAT(
      ExtractTosFromTcpdumpResult(tcpdump_result),
      StatusIs(absl::StatusCode::kInvalidArgument,
               HasSubstr("Failed to find ToS value in tcpdump result.")));
}

}  // namespace
}  // namespace pins
