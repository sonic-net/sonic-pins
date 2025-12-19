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

#include <string>
#include <vector>

#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/strings/str_format.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/time/time.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
#include "net/google::protobuf/contrib/fixtures/proto-fixture-repository.h"
#include "proto/gnmi/gnmi_mock.grpc.pb.h"
#include "thinkit/mock_ssh_client.h"

namespace pins {
namespace {
using ::google::protobuf::contrib::fixtures::ProtoFixtureRepository;
using ::gutil::IsOkAndHolds;
using ::gutil::StatusIs;
using ::testing::AllOf;
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

constexpr absl::string_view kResult2Json = R"json({
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
            "address": "12:34:56::78",
            "config": {
              "address": "12:34:56::78",
              "port": 6343
            },
            "port": 6343
          },
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

constexpr absl::string_view kResultNoCollectorJson = R"json({
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

constexpr absl::string_view kGnmiConfigWithGnpsi = R"json({
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
        "sample-size": 128
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
          }
        ]
      }
    }
  },
  "openconfig-system:system": {
    "openconfig-system-grpc:grpc-servers": {
      "grpc-server": [
        {
          "config": {
            "enable": %v,
            "name": "gnpsi"
          },
          "name": "gnpsi"
        }
      ]
    }
  }
})json";

gnmi::GetResponse BuildGnpsiConfig(bool enable) {
  std::string gnpsi_enable = absl::Substitute(R"json({
    "openconfig-system-grpc:enable": $0
  })json",
                                              enable);
  ProtoFixtureRepository repo;
  repo.RegisterValue("@gnpsi_enable", gnpsi_enable);
  gnmi::GetResponse response = repo.ParseTextProtoOrDie(R"pb(
    notification {
      timestamp: 1664239058571609826
      prefix { origin: "openconfig" }
      update { val { json_ietf_val: @gnpsi_enable } }
    })pb");
  return response;
}

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

TEST(SflowconfigTest, AppendDisabledInterfaceSuccess) {
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
  EXPECT_THAT(
      UpdateSflowConfig(
          sflow_config,
          /*agent_addr_ipv6=*/"8002:12::aab0",
          /*collector_address_to_port=*/{{"12:34:56::78", 6343}},
          /*sflow_interfaces=*/{{"Ethernet1", false}, {"Ethernet2", true}},
          /*sampling_rate=*/1000,
          /*sampling_header_size=*/12),
      IsOkAndHolds(R"json({
  "openconfig-sampling:sampling": {
    "openconfig-sampling-sflow:sflow": {
      "collectors": {
        "collector": [
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
              "enabled": false,
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
          }
        ]
      }
    }
  }
})json"));
}

TEST(SflowconfigTest, AppendSflowConfigSuccess) {
  EXPECT_THAT(
      UpdateSflowConfig(
          kGnmiConfig,
          /*agent_addr_ipv6=*/"8002:12::aab0",
          /*collector_address_to_port=*/{{"12:34:56::78", 6343}},
          /*sflow_interfaces=*/{{"Ethernet3", true}, {"Ethernet4", true}},
          /*sampling_rate=*/1000,
          /*sampling_header_size=*/12),
      IsOkAndHolds(kResultJson));
}

TEST(SflowconfigTest, AppendTwoCollectorSuccess) {
  EXPECT_THAT(
      UpdateSflowConfig(
          kGnmiConfig,
          /*agent_addr_ipv6=*/"8002:12::aab0",
          /*collector_address_to_port=*/
          {{"12:34:56::78", 6343}, {"2001:4860:f802::be", 6343}},
          /*sflow_interfaces=*/{{"Ethernet3", true}, {"Ethernet4", true}},
          /*sampling_rate=*/1000,
          /*sampling_header_size=*/12),
      IsOkAndHolds(kResult2Json));
}

TEST(SflowconfigTest, UpdateNoCollectorConfigSuccess) {
  EXPECT_THAT(
      UpdateSflowConfig(
          kGnmiConfig,
          /*agent_addr_ipv6=*/"8002:12::aab0",
          /*collector_address_to_port=*/{},
          /*sflow_interfaces=*/{{"Ethernet3", true}, {"Ethernet4", true}},
          /*sampling_rate=*/1000,
          /*sampling_header_size=*/12),
      IsOkAndHolds(kResultNoCollectorJson));
}

TEST(SflowconfigTest, MoreThanTwoCollectorsFailure) {
  EXPECT_THAT(
      UpdateSflowConfig(
          kGnmiConfig,
          /*agent_addr_ipv6=*/"8002:12::aab0",
          /*collector_address_to_port=*/
          {{"12:34:56::78", 6343},
           {"34:56:78::9a", 6343},
           {"34:56:78::9b", 6343}},
          /*sflow_interfaces=*/{{"Ethernet3", true}, {"Ethernet4", true}},
          /*sampling_rate=*/1000,
          /*sampling_header_size=*/12),
      StatusIs(
          absl::StatusCode::kInvalidArgument,
          HasSubstr("Number of collectors exceeds max allowed value of 2")));
}

TEST(SflowconfigTest, ModifyInterfaceNamesSuccess) {
  EXPECT_THAT(UpdateSflowConfig(kGnmiConfig,
                                /*agent_addr_ipv6=*/"8002:12::aab0",
                                /*collector_address_to_port=*/
                                {{"12:34:56::78", 6343}},
                                /*sflow_interfaces=*/
                                {{"Ethernet1", true},
                                 {"Ethernet2", true},
                                 {"Ethernet3", true},
                                 {"Ethernet4", true}},
                                /*sampling_rate=*/1000,
                                /*sampling_header_size=*/12),
              IsOkAndHolds(kResultJson));
}

TEST(SflowconfigTest, ModifySamplingRateSuccess) {
  EXPECT_THAT(UpdateSflowConfig(kGnmiConfig,
                                /*agent_addr_ipv6=*/"8002:12::aab0",
                                /*collector_address_to_port=*/
                                {},
                                /*sflow_interfaces=*/
                                {{"Ethernet2", true}, {"Ethernet3", true}},
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
          /*sflow_interfaces=*/{{"Ethernet1", true}, {"Ethernet2", true}},
          /*sampling_rate=*/1000,
          /*sampling_header_size=*/128),
      StatusIs(absl::StatusCode::kInvalidArgument,
               HasSubstr("agent_addr_ipv6 parameter cannot be empty.")));
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

TEST(SflowconfigTest, UpdateGnpsiConfigEnabledSuccess) {
  EXPECT_THAT(UpdateGnpsiConfig(kGnmiConfig, /*enable=*/true),
              IsOkAndHolds(absl::StrFormat(kGnmiConfigWithGnpsi, true)));
}

TEST(SflowconfigTest, UpdateGnpsiConfigDisabledSuccess) {
  EXPECT_THAT(UpdateGnpsiConfig(kGnmiConfig, /*enable=*/false),
              IsOkAndHolds(absl::StrFormat(kGnmiConfigWithGnpsi, false)));
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

TEST(SflowUtilTest, GetSampleRateInvalidSampleRateFail) {
  gnmi::MockgNMIStub stub;
  ON_CALL(stub, Get).WillByDefault(DoAll(
      SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
          R"pb(
            notification {
              timestamp: 1664239058571609826
              prefix { origin: "openconfig" }
              update {
                val {
                  json_ietf_val: "{\"openconfig-sampling-sflow:ingress-sampling-rate\":\"abc\"}"
                }
              }
            })pb")),
      Return(grpc::Status::OK)));
  absl::flat_hash_set<std::string> interfaces{"Ethernet1/1/1",
                                              "Ethernet1/31/5"};
  EXPECT_THAT(GetSflowSamplingRateForInterfaces(&stub, interfaces),
              StatusIs(absl::StatusCode::kInternal, HasSubstr("invalid")));
}

TEST(SflowUtilTest, GetActualSampleRateSuccessForAllInterfaces) {
  gnmi::MockgNMIStub stub;
  ON_CALL(stub, Get).WillByDefault(DoAll(
      SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
          R"pb(
            notification {
              timestamp: 1664239058571609826
              prefix { origin: "openconfig" }
              update {
                val {
                  json_ietf_val: "{\"pins-sampling-sflow:actual-ingress-sampling-rate\":256}"
                }
              }
            })pb")),
      Return(grpc::Status::OK)));
  absl::flat_hash_set<std::string> interfaces{"Ethernet1/1/1",
                                              "Ethernet1/31/5"};
  const absl::flat_hash_map<std::string, int> expected_map = {
      {"Ethernet1/1/1", 256}, {"Ethernet1/31/5", 256}};
  EXPECT_THAT(GetSflowActualSamplingRateForInterfaces(&stub, interfaces),
              IsOkAndHolds(UnorderedPointwise(Eq(), expected_map)));
}

TEST(SflowUtilTest, GetActualSampleRateInvalidSampleRateFail) {
  gnmi::MockgNMIStub stub;
  ON_CALL(stub, Get).WillByDefault(DoAll(
      SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
          R"pb(
            notification {
              timestamp: 1664239058571609826
              prefix { origin: "openconfig" }
              update {
                val {
                  json_ietf_val: "{\"pins-sampling-sflow:actual-ingress-sampling-rate\":\"abc\"}"
                }
              }
            })pb")),
      Return(grpc::Status::OK)));
  absl::flat_hash_set<std::string> interfaces{"Ethernet1/1/1",
                                              "Ethernet1/31/5"};
  EXPECT_THAT(GetSflowActualSamplingRateForInterfaces(&stub, interfaces),
              StatusIs(absl::StatusCode::kInternal, HasSubstr("invalid")));
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

TEST(SflowUtilTest, UpdateSflowInterfaceConfigSuccess) {
  gnmi::MockgNMIStub stub;
  ON_CALL(stub, Set).WillByDefault(Return(grpc::Status::OK));
  EXPECT_CALL(stub, Get)
      .Times(2)
      .WillOnce((DoAll(
          SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
              R"pb(
                notification {
                  timestamp: 1664239058571609826
                  prefix { origin: "openconfig" }
                  update {
                    val {
                      json_ietf_val: "{\"openconfig-sampling-sflow:enabled\":true}"
                    }
                  }
                })pb")),
          Return(grpc::Status::OK))))
      .WillOnce(DoAll(
          SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
              R"pb(
                notification {
                  timestamp: 1664239058571609826
                  prefix { origin: "openconfig" }
                  update {
                    val {
                      json_ietf_val: "{\"openconfig-sampling-sflow:ingress-sampling-rate\":4000}"
                    }
                  }
                })pb")),
          Return(grpc::Status::OK)));
  EXPECT_OK(SetSflowInterfaceConfig(&stub, "Ethernet1/1/1", /*enabled=*/true,
                                    /*samping_rate=*/4000, absl::Seconds(1)));
}

TEST(SflowUtilTest, UpdateSflowInterfaceConfigNotConvergeFail) {
  gnmi::MockgNMIStub stub;
  ON_CALL(stub, Set).WillByDefault(Return(grpc::Status::OK));
  ON_CALL(stub, Get).WillByDefault((DoAll(
      SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
          R"pb(
            notification {
              timestamp: 1664239058571609826
              prefix { origin: "openconfig" }
              update {
                val {
                  json_ietf_val: "{\"openconfig-sampling-sflow:enabled\":false}"
                }
              }
            })pb")),
      Return(grpc::Status::OK))));
  EXPECT_THAT(SetSflowInterfaceConfig(&stub, "Ethernet1/1/1", /*enabled=*/true,
                                      /*samping_rate=*/4000, absl::Seconds(1)),
              StatusIs(absl::StatusCode::kDeadlineExceeded));
}

TEST(SflowUtilTest, UpdateSflowInterfaceEnableSuccess) {
  gnmi::MockgNMIStub stub;
  ON_CALL(stub, Set).WillByDefault(Return(grpc::Status::OK));
  ON_CALL(stub, Get).WillByDefault(DoAll(
      SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
          R"pb(
            notification {
              timestamp: 1664239058571609826
              prefix { origin: "openconfig" }
              update {
                val {
                  json_ietf_val: "{\"openconfig-sampling-sflow:enabled\":true}"
                }
              }
            })pb")),
      Return(grpc::Status::OK)));
  EXPECT_OK(
      SetSflowInterfaceConfigEnable(&stub, "Ethernet1/1/1", /*enabled=*/true));
}

TEST(SflowUtilTest, UpdateSflowInterfaceEnableNotConvergeFail) {
  gnmi::MockgNMIStub stub;
  ON_CALL(stub, Set).WillByDefault(Return(grpc::Status::OK));
  ON_CALL(stub, Get).WillByDefault(DoAll(
      SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
          R"pb(
            notification {
              timestamp: 1664239058571609826
              prefix { origin: "openconfig" }
              update {
                val {
                  json_ietf_val: "{\"openconfig-sampling-sflow:enabled\":false}"
                }
              }
            })pb")),
      Return(grpc::Status::OK)));
  EXPECT_THAT(
      SetSflowInterfaceConfigEnable(&stub, "Ethernet1/1/1", /*enabled=*/true),
      StatusIs(absl::StatusCode::kDeadlineExceeded));
}

TEST(SflowUtilTest, VerifyGnpsiStateConvergedWithGnpsiEnabledSucceeds) {
  gnmi::MockgNMIStub stub;
  ON_CALL(stub, Get).WillByDefault(
      DoAll(SetArgPointee<2>(BuildGnpsiConfig(/*enable=*/true)),
            Return(grpc::Status::OK)));
  EXPECT_OK(VerifyGnpsiStateConverged(&stub, /*enable=*/true));
}

TEST(SflowUtilTest, VerifyGnpsiStateConvergedWithGnpsiDisabledSucceeds) {
  gnmi::MockgNMIStub stub;
  ON_CALL(stub, Get).WillByDefault(
      DoAll(SetArgPointee<2>(BuildGnpsiConfig(/*enable=*/false)),
            Return(grpc::Status::OK)));
  EXPECT_OK(VerifyGnpsiStateConverged(&stub, /*enable=*/false));
}

TEST(SflowUtilTest, VerifySetGnpsiStateEnabledSucceeds) {
  gnmi::MockgNMIStub stub;
  ON_CALL(stub, Get).WillByDefault(
      DoAll(SetArgPointee<2>(BuildGnpsiConfig(/*enable=*/true)),
            Return(grpc::Status::OK)));
  EXPECT_OK(SetGnpsiConfigEnabled(&stub, /*enable=*/true));
}

TEST(SflowUtilTest, VerifySetGnpsiStateDisabledSucceeds) {
  gnmi::MockgNMIStub stub;
  ON_CALL(stub, Get).WillByDefault(
      DoAll(SetArgPointee<2>(BuildGnpsiConfig(/*enable=*/false)),
            Return(grpc::Status::OK)));
  EXPECT_OK(SetGnpsiConfigEnabled(&stub, /*enable=*/false));
}

constexpr absl::string_view kTorSflowGnmiConfig = R"json({
     "openconfig-sampling:sampling" : {
        "openconfig-sampling-sflow:sflow" : {
           "collectors" : {
              "collector" : [
                 {
                    "address" : "2001:4860:f802::be",
                    "config" : {
                       "address" : "2001:4860:f802::be",
                       "port" : 6344
                    },
                    "port" : 6344
                 }
              ]
           }
        }
     }
  })json";

TEST(SflowUtilTest, GetSflowCollectorPortTest) {
  EXPECT_EQ(GetSflowCollectorPort(), kSflowStandaloneCollectorPort);
}

constexpr absl::string_view kTorSflowGnmiConfigMissingPort = R"json({
     "openconfig-sampling:sampling" : {
        "openconfig-sampling-sflow:sflow" : {
           "collectors" : {
              "collector" : [
                 {
                    "address" : "2001:4860:f802::be",
                    "config" : {
                    },
                    "port" : 6344
                 }
              ]
           }
        }
     }
  })json";

constexpr absl::string_view kNoCollectorGnmiConfig = R"json({
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
          }
        ]
      }
    }
  }
})json";

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

TEST(SflowDscpTest, ParseTcpdumpResultMultipleTosSameSuccess) {
  const std::string tcpdump_result =
      R"(tcpdump: listening on lo, link-type EN10MB (Ethernet), capture size "
      "262144 bytes 18:10:50.401908 00:00:00:00:00:00 (oui Ethernet) > "
      "00:00:00:00:00:00 (oui Ethernet), ethertype IPv6 (0x86dd), length 230: "
      "(class 0xa1, flowlabel 0x20016, hlim 127, next-header UDP (17) payload "
      "length: 176) localhost.56223 > localhost.6343: [bad udp cksum 0x00c3 -> "
      "0x6a10!] sFlowv5, IPv6 agent 38.7.248.176, agent-id 2157511939, seqnum "
      "0, uptime 0, samples 100000, length 168 flow sample (1), length "
      "50018,[|SFLOW] 0x0000:  6802 0016 00b0 117f 0000 0000 0000 0000  "
      "h..............."
      "00:00:00:00:00:00 (oui Ethernet), ethertype IPv6 (0x86dd), length 230: "
      "(class 0xa1, flowlabel 0x20016, hlim 127, next-header UDP (17) payload "
      "length: 176) localhost.56223 > localhost.6343: [bad udp cksum 0x00c3 -> "
      "0x6a10!] sFlowv5, IPv6 agent 38.7.248.176, agent-id 2157511939, seqnum "
      "0, uptime 0, samples 100000, length 168 flow sample (1), length "
      "50018,[|SFLOW] 0x0000:  6802 0016 00b0 117f 0000 0000 0000 0000  "
      "h...............)";
  ASSERT_THAT(ExtractTosFromTcpdumpResult(tcpdump_result), IsOkAndHolds(161));
}

TEST(SflowDscpTest, ParseTcpdumpResultMultipleTosNotSameFailure) {
  const std::string tcpdump_result =
      R"(tcpdump: listening on lo, link-type EN10MB (Ethernet), capture size "
      "262144 bytes 18:10:50.401908 00:00:00:00:00:00 (oui Ethernet) > "
      "00:00:00:00:00:00 (oui Ethernet), ethertype IPv6 (0x86dd), length 230: "
      "(class 0xa1, flowlabel 0x20016, hlim 127, next-header UDP (17) payload "
      "length: 176) localhost.56223 > localhost.6343: [bad udp cksum 0x00c3 -> "
      "0x6a10!] sFlowv5, IPv6 agent 38.7.248.176, agent-id 2157511939, seqnum "
      "0, uptime 0, samples 100000, length 168 flow sample (1), length "
      "50018,[|SFLOW] 0x0000:  6802 0016 00b0 117f 0000 0000 0000 0000  "
      "h..............."
      "00:00:00:00:00:00 (oui Ethernet), ethertype IPv6 (0x86dd), length 230: "
      "(class 0xff, flowlabel 0x20016, hlim 127, next-header UDP (17) payload "
      "length: 176) localhost.56223 > localhost.6343: [bad udp cksum 0x00c3 -> "
      "0x6a10!] sFlowv5, IPv6 agent 38.7.248.176, agent-id 2157511939, seqnum "
      "0, uptime 0, samples 100000, length 168 flow sample (1), length "
      "50018,[|SFLOW] 0x0000:  6802 0016 00b0 117f 0000 0000 0000 0000  "
      "h...............)";
  ASSERT_THAT(ExtractTosFromTcpdumpResult(tcpdump_result),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       HasSubstr("Tos values are not identical.")));
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

TEST(IpAddressTest, ParseError) {
  EXPECT_THAT(IsSameIpAddressStr("", "127.0.0.1"),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(IpAddressTest, SameIpv4Address) {
  EXPECT_THAT(IsSameIpAddressStr("127.0.0.1", "127.0.0.1"), IsOkAndHolds(true));
}

TEST(IpAddressTest, DifferentIpv4Address) {
  EXPECT_THAT(IsSameIpAddressStr("127.0.0.1", "127.0.0.2"),
              IsOkAndHolds(false));
}

TEST(IpAddressTest, SameIpv6Address) {
  EXPECT_THAT(IsSameIpAddressStr("2001:db8:0:12::1", "2001:db8:0:12::1"),
              IsOkAndHolds(true));
}

TEST(IpAddressTest, DifferentIpv6Address) {
  EXPECT_THAT(IsSameIpAddressStr("2001:db8:0:12::1", "2001:db8:0:12::2"),
              IsOkAndHolds(false));
}

TEST(IpAddressTest, SameIpv6AddressDifferentFormat) {
  EXPECT_THAT(IsSameIpAddressStr("2607:f001:0acd::",
                                 "2607:f001:0acd:0000:0000:0000:0000:0000"),
              IsOkAndHolds(true));
}

TEST(IpAddressTest, SameIpv6AddressDifferentFormat2) {
  EXPECT_THAT(IsSameIpAddressStr("2001:db8:0:12::1",
                                 "2001:0db8:0000:0012:0000:0000:0000:0001"),
              IsOkAndHolds(true));
}

TEST(IpAddressTest, SameIpv6AddressDifferentFormat3) {
  EXPECT_THAT(IsSameIpAddressStr("2607:f001:0acf:0000:0000:0000:0000:0000",
                                 "2607:f001:acf::"),
              IsOkAndHolds(true));
}

TEST(IpAddressTest, SameIpv6AddressDifferentFormat4) {
  EXPECT_THAT(IsSameIpAddressStr("2607:f001:acf::",
                                 "2607:f001:0acf:0000:0000:0000:0000:0000"),
              IsOkAndHolds(true));
}

TEST(PortIndexTest, SshCommandFailCheckFail) {
  thinkit::MockSSHClient mock_ssh_client;
  ON_CALL(mock_ssh_client, RunCommand)
      .WillByDefault(Return(absl::InternalError("No ssh client")));
  const std::vector<std::string> port_names = {"Ethernet1/1/1",
                                               "Ethernet1/1/2"};
  EXPECT_THAT(CheckStateDbPortIndexTableExists(mock_ssh_client, "switch_x",
                                               "/usr/tools/bin/", port_names),
              StatusIs(absl::StatusCode::kInternal));
}

TEST(PortIndexTest, SshCommandNoNilCheckSuccess) {
  thinkit::MockSSHClient mock_ssh_client;
  ON_CALL(mock_ssh_client, RunCommand)
      .WillByDefault(Return(R"(PORT_INDEX_TABLE|Ethernet1/10/1
PORT_INDEX_TABLE|Ethernet1/9/1
PORT_INDEX_TABLE|Ethernet1/31/1
PORT_INDEX_TABLE|Ethernet1/2/5
PORT_INDEX_TABLE|Ethernet1/13/1)"));
  const std::vector<std::string> port_names = {
      "Ethernet1/10/1", "Ethernet1/31/1", "Ethernet1/13/1"};
  EXPECT_OK(CheckStateDbPortIndexTableExists(mock_ssh_client, "switch_x",
                                             "/usr/tools/bin/", port_names));
}

TEST(PortIndexTest, SshCommandNilCheckFail) {
  thinkit::MockSSHClient mock_ssh_client;
  ON_CALL(mock_ssh_client, RunCommand).WillByDefault(Return("nil"));
  const std::vector<std::string> port_names = {"Ethernet1/1/1",
                                               "Ethernet1/1/2"};
  EXPECT_THAT(CheckStateDbPortIndexTableExists(mock_ssh_client, "switch_x",
                                               "/usr/tools/bin/", port_names),
              StatusIs(absl::StatusCode::kFailedPrecondition));
}

TEST(PortIndexTest, SshCommandEmptyCheckFail) {
  thinkit::MockSSHClient mock_ssh_client;
  ON_CALL(mock_ssh_client, RunCommand).WillByDefault(Return(""));
  const std::vector<std::string> port_names = {"Ethernet1/1/1",
                                               "Ethernet1/1/2"};
  EXPECT_THAT(
      CheckStateDbPortIndexTableExists(mock_ssh_client, "switch_x",
                                       "/usr/tools/bin/", port_names),
      StatusIs(absl::StatusCode::kFailedPrecondition,
               AllOf(HasSubstr("Ethernet1/1/1"), HasSubstr("Ethernet1/1/2"))));
}

}  // namespace
}  // namespace pins
