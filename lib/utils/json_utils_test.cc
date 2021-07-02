// Copyright 2024 Google LLC
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
#include "lib/utils/json_utils.h"

#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "include/json/reader.h"

namespace pins_test {

namespace {

using ::Json::Reader;
using ::Json::Value;

}  // namespace

constexpr absl::string_view kJsonConfig1 = R"JSON(
{
   "a" : "value1",
   "b" : {
      "c" : [ "value2", "value3" ],
      "d" : [ "value4" ]
   },
   "e" : "value5",
   "f" : [
      {
         "g" : "value6"
      },
      "value7"
   ]
}
)JSON";

constexpr absl::string_view kJsonConfig2 = R"JSON(
{
   "b" : {
      "d" : [ "value4" ],
      "c" : [ "value3", "value2" ]
   },
   "f" : [
      "value7",
      {
         "g" : "value6"
      }
   ],
   "e" : "value5",
   "a" : "value1"
}
)JSON";

TEST(JsonDiff, GpinsJsonDiffEmpty) {
  constexpr absl::string_view kJsonValue1 = R"JSON({
     "a" : "value1",
     "b" : {
        "c" : [ "value2", "value3" ],
     },
     "d" : [
        {
           "e" : "value7"
        }
     ],
     "f" : 9
  })JSON";
  Value source_value;
  Reader reader;
  reader.parse(std::string(kJsonValue1), source_value);
  Value expected_diff, actual_diff;
  EXPECT_FALSE(JsonDiff(source_value, source_value, actual_diff));
  EXPECT_EQ(expected_diff, actual_diff);
}

TEST(JsonDiff, GpinsJsonScalarDiff) {
  constexpr absl::string_view kJsonValue1 = R"JSON({
      "d" : true
  })JSON";

  constexpr absl::string_view kJsonValue2 = R"JSON({
      "d" : false
  })JSON";

  constexpr absl::string_view kExpectedScalarDiff = R"JSON({
     "d" : true
  })JSON";

  Value source_value;
  Reader reader;
  reader.parse(std::string(kJsonValue1), source_value);
  Value target_value;
  reader.parse(std::string(kJsonValue2), target_value);
  Value actual_diff;
  EXPECT_TRUE(JsonDiff(source_value, target_value, actual_diff));
  Value expected_diff;
  reader.parse(std::string(kExpectedScalarDiff), expected_diff);
  EXPECT_EQ(expected_diff, actual_diff);
}

TEST(JsonDiff, TestJsonDiffObject) {
  constexpr absl::string_view kJsonValue1 = R"JSON(
  {
     "a" : {
        "b" : [ "value2", "value3" ],
        "c" : [ "value4" ]
     }
  })JSON";

  constexpr absl::string_view kJsonValue2 = R"JSON(
  {
     "a" : {
        "b" : [ "value2", "value3" ]
     }
  })JSON";

  constexpr absl::string_view kExpectedObjectDiff = R"JSON({
     "a" : {
        "c" : [ "value4" ]
     }
  })JSON";

  Value source_value;
  Reader reader;
  reader.parse(std::string(kJsonValue1), source_value);
  Value target_value;
  reader.parse(std::string(kJsonValue2), target_value);
  Value actual_diff;
  EXPECT_TRUE(JsonDiff(source_value, target_value, actual_diff));
  Value expected_diff;
  reader.parse(std::string(kExpectedObjectDiff), expected_diff);
  EXPECT_EQ(expected_diff, actual_diff);
}

TEST(JsonDiff, TestJsonDiffArray) {
  constexpr absl::string_view kJsonValue1 = R"JSON({
     "a" : {
        "b" : [ "value2", "value3" ],
     }
  })JSON";

  constexpr absl::string_view kJsonValue2 = R"JSON({
     "a" : {
        "b" : [ "value2" ],
     }
  })JSON";

  constexpr absl::string_view kExpectedArrayDiff = R"JSON({
     "a" : {
        "b" : [ "value3" ],
     }
  })JSON";

  Value source_value;
  Reader reader;
  reader.parse(std::string(kJsonValue1), source_value);
  Value target_value;
  reader.parse(std::string(kJsonValue2), target_value);
  Value actual_diff;
  EXPECT_TRUE(JsonDiff(source_value, target_value, actual_diff));
  Value expected_diff;
  reader.parse(std::string(kExpectedArrayDiff), expected_diff);
  EXPECT_EQ(expected_diff, actual_diff);
}

TEST(JsonDiff, TestJsonDiffNested) {
  constexpr absl::string_view kJsonValue1 = R"JSON({
     "a" : [
        {
           "b" : "value6",
           "c" : "value7"
        }
     ]
  })JSON";

  constexpr absl::string_view kJsonValue2 = R"JSON({
     "a" : [
        {
           "b" : "value6"
        }
     ]
  })JSON";

  constexpr absl::string_view kExpectedNestedDiff = R"JSON({
     "a" : [
      {
         "c" : "value7"
      }
     ]
  })JSON";

  Value source_value;
  Reader reader;
  reader.parse(std::string(kJsonValue1), source_value);
  Value target_value;
  reader.parse(std::string(kJsonValue2), target_value);
  Value actual_diff;
  EXPECT_TRUE(JsonDiff(source_value, target_value, actual_diff));
  Value expected_diff;
  reader.parse(std::string(kExpectedNestedDiff), expected_diff);
  EXPECT_EQ(expected_diff, actual_diff);
}

TEST(JsonDiff, TestJsonDiffDifferentTypes) {
  constexpr absl::string_view kJsonValue1 = R"JSON(
  {
     "a" : "value8"
  })JSON";

  constexpr absl::string_view kJsonValue2 = R"JSON(
  {
     "a" : 9
  })JSON";

  constexpr absl::string_view kExpectedDifferentTypesDiff = R"JSON({
     "a" : "value8"
  })JSON";

  Value source_value;
  Reader reader;
  reader.parse(std::string(kJsonValue1), source_value);
  Value target_value;
  reader.parse(std::string(kJsonValue2), target_value);
  Value actual_diff;
  EXPECT_TRUE(JsonDiff(source_value, target_value, actual_diff));
  Value expected_diff;
  reader.parse(std::string(kExpectedDifferentTypesDiff), expected_diff);
  EXPECT_EQ(expected_diff, actual_diff);
}

TEST(JsonReplaceKey, TestJsonReplaceKeyWithSameKey) {
  constexpr absl::string_view kOpenConfig = R"JSON({
   "system" : {
      "config" : {
        "hostname": "ju1u1t1.mtv16.net.google.com"
      },
      "ntp" : {
        "config" : {
          "enabled" : true
        },
        "servers" : {
          "server" : [
            {
              "address" : "192.168.1.1",
              "config" : {
                "address" : "192.168.1.1",
                "port" : 1234
              }
            }
          ]
        }
      }
   }
  })JSON";

  Value source_value;
  Reader reader;
  reader.parse(std::string(kOpenConfig), source_value);
  JsonReplaceKey(source_value, "config", "config");
  Value target_value;
  reader.parse(std::string(kOpenConfig), target_value);
  EXPECT_EQ(source_value, target_value);
}

TEST(JsonReplaceKey, TestJsonReplaceKey) {
  constexpr absl::string_view kJsonValue1 = R"JSON({
   "a" : {
      "old_key" : {
        "b": "value1"
      },
      "c" : {
        "old_key" : {
          "d" : true
        },
        "e" : {
          "f" : [
            {
              "g" : "value2",
              "old_key" : {
                "h" : "value3",
                "i" : 1234
              }
            }
          ]
        }
      }
   }
  })JSON";

  constexpr absl::string_view kJsonValue2 = R"JSON({
   "a" : {
      "new_key" : {
        "b": "value1"
      },
      "c" : {
        "new_key" : {
          "d" : true
        },
        "e" : {
          "f" : [
            {
              "g" : "value2",
              "new_key" : {
                "h" : "value3",
                "i" : 1234
              }
            }
          ]
        }
      }
   }
  })JSON";

  Value source_value;
  Reader reader;
  reader.parse(std::string(kJsonValue1), source_value);
  JsonReplaceKey(source_value, "old_key", "new_key");
  Value target_value;
  reader.parse(std::string(kJsonValue2), target_value);
  EXPECT_EQ(target_value, source_value);
}

TEST(JsonIsSubset, GpinsJsonIsSubsetTrue) {
  constexpr absl::string_view kJson1 = R"JSON(
  {
     "a" : {
        "b" : [
          {
            "f" : "value4"
          }
        ],
     },
  })JSON";
  constexpr absl::string_view kJson2 = R"JSON(
  {
     "a" : {
        "b" : [
           {
             "c" : "value1",
             "d" : "value2"
           },
           {
             "e" : "value3",
             "f" : "value4",
             "g" : "value5"
           }
         ],
     },
  })JSON";
  Reader reader;
  Value source, target;
  reader.parse(std::string(kJson1), source);
  reader.parse(std::string(kJson2), target);
  EXPECT_TRUE(JsonIsSubset(source, target));
}

TEST(JsonIsSubset, GpinsJsonIsSubsetFalse) {
  constexpr absl::string_view kJson1 = R"JSON(
  {
     "a" : {
        "b" : [
          {
            "f" : "value4"
          }
        ],
     },
  })JSON";
  constexpr absl::string_view kJson2 = R"JSON(
  {
     "a" : {
        "b" : [
           {
             "c" : "value1",
             "d" : "value2"
           },
           {
             "e" : "value3",
             "f" : "value4",
             "g" : "value5"
           }
         ],
     },
  })JSON";
  Reader reader;
  Value source, target;
  reader.parse(std::string(kJson2), source);
  reader.parse(std::string(kJson1), target);
  EXPECT_FALSE(JsonIsSubset(source, target));
}

TEST(JsonIsSubset, GpinsJsonIsSubsetDifferentTypes) {
  constexpr absl::string_view kJson1 = R"JSON(
  {
     "a" : {
        "b" : [
          {
            "f" : "value4"
          }
        ]
     }
  })JSON";
  constexpr absl::string_view kJson2 = R"JSON(
  {
     "a" : {
        "b" :
          {
            "f" : "value4"
          }
     }
  })JSON";
  Reader reader;
  Value source, target;
  reader.parse(std::string(kJson1), source);
  reader.parse(std::string(kJson2), target);
  EXPECT_FALSE(JsonIsSubset(source, target));
}

TEST(JsonIsSubset, GpinsJsonIsSubsetDifferentValues) {
  constexpr absl::string_view kJson1 = R"JSON(
  {
     "a" : {
        "b" : [
          {
            "f" : "value4"
          }
        ],
     },
  })JSON";
  constexpr absl::string_view kJson2 = R"JSON(
  {
     "a" : {
        "b" : [
           {
             "c" : "value1",
             "d" : "value2"
           },
           {
             "e" : "value3",
             "f" : "value6",
             "g" : "value5"
           }
         ],
     },
  })JSON";
  Reader reader;
  Value source, target;
  reader.parse(std::string(kJson1), source);
  reader.parse(std::string(kJson2), target);
  EXPECT_FALSE(JsonIsSubset(source, target));
}

TEST(JsonIsSubset, JsonValueComparisonPassedInDifferentOrder) {
  Value jsonconfig_1;
  Value jsonconfig_2;
  Reader reader;
  EXPECT_TRUE(reader.parse(std::string(kJsonConfig1), jsonconfig_1));
  EXPECT_TRUE(reader.parse(std::string(kJsonConfig2), jsonconfig_2));
  EXPECT_TRUE(JsonValueIsEqual(jsonconfig_1, jsonconfig_2));
}

TEST(JsonIsSubset, GpinsConfigComparisonFailed) {
  Value jsonconfig_1;
  Value jsonconfig_2;
  Reader reader;
  EXPECT_TRUE(reader.parse(std::string(kJsonConfig1), jsonconfig_1));
  EXPECT_TRUE(reader.parse(std::string(kJsonConfig2), jsonconfig_2));
  // Change value2 -> value3.
  jsonconfig_1["b"]["c"][0] = "value3";
  jsonconfig_1["b"]["c"][1] = "value3";
  EXPECT_FALSE(JsonValueIsEqual(jsonconfig_1, jsonconfig_2));
}

TEST(JsonIsSubset, EmptySetComparisonPassed) {
  Value jsonconfig_1;
  Value jsonconfig_2;
  EXPECT_TRUE(JsonValueIsEqual(jsonconfig_1, jsonconfig_2));
}

constexpr char kReleaseInterfaceStateExpectedBlob[] = R"({
"openconfig-interfaces:interfaces" : {
      "interface" : [
      {"name":"Ethernet0","openconfig-if-ethernet:ethernet":{"state":{"port-speed":"openconfig-if-ethernet:SPEED_400GB"}},"state":{"admin-status":"UP","enabled":true,"name":"Ethernet0","openconfig-pins-interfaces:id":1,"oper-status":"DOWN","enabled":false,"mtu":9100}},
      {"name":"Ethernet8","openconfig-if-ethernet:ethernet":{"state":{"port-speed":"openconfig-if-ethernet:SPEED_200GB"}},"state":{"admin-status":"UP","enabled":true,"name":"Ethernet8","openconfig-pins-interfaces:id":2,"oper-status":"DOWN","enabled":false,"mtu":9100}},
      {"name":"Ethernet12","openconfig-if-ethernet:ethernet":{"state":{"port-speed":"openconfig-if-ethernet:SPEED_200GB"}},"state":{"admin-status":"UP","enabled":true,"name":"Ethernet12","openconfig-pins-interfaces:id":518,"oper-status":"DOWN","enabled":false,"mtu":9100}}
      ]
      }
})";

constexpr char kReleaseInterfaceStateBlob[] = R"({
"openconfig-interfaces:interfaces" : {
      "interface" : [
      {"name":"Ethernet0","openconfig-if-ethernet:ethernet":{"state":{"port-speed":"openconfig-if-ethernet:SPEED_400GB"}},"state":{"admin-status":"UP","enabled":true,"name":"Ethernet0","openconfig-pins-interfaces:id":1,"oper-status":"DOWN","enabled":false,"mtu":9100}},
      {"name":"Ethernet12","openconfig-if-ethernet:ethernet":{"state":{"port-speed":"openconfig-if-ethernet:SPEED_200GB"}},"state":{"admin-status":"UP","enabled":true,"name":"Ethernet12","openconfig-pins-interfaces:id":518,"oper-status":"DOWN","enabled":false,"mtu":9100}},
      {"name":"Ethernet8","openconfig-if-ethernet:ethernet":{"state":{"port-speed":"openconfig-if-ethernet:SPEED_200GB"}},"state":{"admin-status":"UP","enabled":true,"name":"Ethernet8","openconfig-pins-interfaces:id":2,"oper-status":"DOWN","enabled":false,"mtu":9100}}
      ]
      }
})";

TEST(JsonIsSubset, GpinsJsonIsSubsetInterfaceState) {
  Reader reader;
  Value source, target;
  reader.parse(kReleaseInterfaceStateBlob, target);
  reader.parse(kReleaseInterfaceStateExpectedBlob, source);
  EXPECT_TRUE(JsonIsSubset(source, target));
}

}  // namespace pins_test
