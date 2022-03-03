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

#include <string>

#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "include/json/reader.h"
#include "include/nlohmann/json.hpp"

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
  std::vector<std::string> error_messages;
  reader.parse(std::string(kJson1), source);
  reader.parse(std::string(kJson2), target);
  EXPECT_TRUE(JsonIsSubset(source, target, error_messages));
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
  std::vector<std::string> error_messages;
  reader.parse(std::string(kJson2), source);
  reader.parse(std::string(kJson1), target);
  EXPECT_FALSE(JsonIsSubset(source, target, error_messages));
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
  std::vector<std::string> error_messages;
  reader.parse(std::string(kJson1), source);
  reader.parse(std::string(kJson2), target);
  EXPECT_FALSE(JsonIsSubset(source, target, error_messages));
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
  std::vector<std::string> error_messages;
  reader.parse(std::string(kJson1), source);
  reader.parse(std::string(kJson2), target);
  EXPECT_FALSE(JsonIsSubset(source, target, error_messages));
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
  std::vector<std::string> error_messages;
  reader.parse(kReleaseInterfaceStateBlob, target);
  reader.parse(kReleaseInterfaceStateExpectedBlob, source);
  EXPECT_TRUE(JsonIsSubset(source, target, error_messages));
}

}  // namespace pins_test

namespace json_yang {

namespace {

using StringMap = absl::flat_hash_map<std::string, std::string>;

using ::gutil::StatusIs;
using ::testing::HasSubstr;

TEST(ParseJson, TestInvalidJson) {
  // Trailing comma after the last element in the container is unexpected.
  constexpr char kBadJson[] = R"({
    "outer" : {
      "inner" : "value",
    }
  })";
  EXPECT_THAT(ParseJson(kBadJson), StatusIs(absl::StatusCode::kInvalidArgument,
                                            HasSubstr("json parse error")));
}

TEST(ParseJson, TestEmptyJson) {
  ASSERT_OK_AND_ASSIGN(auto empty_json, ParseJson(""));
  EXPECT_TRUE(empty_json.is_null());
}

TEST(ParseJson, TestValidJson) {
  constexpr char kGoodJson[] = R"({
    "outer" : {
      "inner" : "value"
    }
  })";
  ASSERT_OK_AND_ASSIGN(auto good_json, ParseJson(kGoodJson));
  ASSERT_TRUE(good_json.contains("outer"));
  EXPECT_TRUE(good_json["outer"].contains("inner"));
}

TEST(DumpJson, TestInvalidJson) {
  // Invalid UTF-8 byte sequence.
  nlohmann::json invalid_json = "a\xA9z";
  EXPECT_EQ(DumpJson(invalid_json), "\"a\xEF\xBF\xBDz\"");
}

TEST(DumpJson, TestEmptyJson) {
  nlohmann::json null_json(nlohmann::json::value_t::null);
  EXPECT_EQ(DumpJson(null_json), "");
}

constexpr char kExpectedDump[] = R"({
  "a": 1,
  "b": "2",
  "c": -3,
  "d": 4.5,
  "e": [
    1,
    2,
    3,
    4,
    5
  ]
})";
TEST(DumpJson, TestValidJson) {
  nlohmann::json good_json = {
      {"a", 1}, {"b", "2"}, {"c", -3}, {"d", 4.5}, {"e", {1, 2, 3, 4, 5}},
  };
  EXPECT_EQ(DumpJson(good_json), kExpectedDump);
}

TEST(ReplaceNamesinJsonObject, TestReplacementEmptyJson) {
  ASSERT_OK_AND_ASSIGN(nlohmann::json example_json, ParseJson(""));
  EXPECT_EQ(ReplaceNamesinJsonObject(example_json, StringMap{}), example_json);
}

TEST(ReplaceJsonPathElements, TestReplacementEmptyNamesMap) {
  constexpr char kExampleJson[] = R"({
    "outer_element" : {
      "container1" : [
        {
          "leaf": "value1",
          "key_leaf": "key_value1",
          "element": {
            "container2": [
              {
                "key_leaf2": "key_value3",
                "leaf": "value2"
              }
            ],
            "element": {
              "leaf": "value3"
            }
          }
        },
        {
          "key_leaf": "key_value2",
          "middle_element": {
            "container2": [
              {
                "key_leaf2": "key_value4",
                "element": {
                  "inner_element": {
                    "leaf3": "value6",
                    "leaf": "value5"
                  }
                }
              }
            ]
          }
        }
      ]
    }
  })";

  ASSERT_OK_AND_ASSIGN(auto example_json, ParseJson(kExampleJson));
  EXPECT_EQ(ReplaceNamesinJsonObject(example_json, StringMap{}), example_json);
}

TEST(ReplaceNamesinJsonObject, TestReplacementNamesReplaced) {
  constexpr char kExampleJson[] = R"({
    "outer_element" : {
      "container1" : [
        {
          "leaf": "value1",
          "key_leaf": "key_value1",
          "element": {
            "container2": [
              {
                "key_leaf2": "key_value3",
                "leaf": "value2"
              }
            ],
            "element": {
              "leaf": "value3"
            }
          }
        },
        {
          "key_leaf": "key_value2",
          "middle_element": {
            "container2": [
              {
                "key_leaf2": "key_value4",
                "element": {
                  "inner_element": {
                    "leaf3": "value6",
                    "leaf": "value5"
                  }
                }
              }
            ]
          }
        }
      ]
    }
  })";

  constexpr char kExpectedJson[] = R"({
    "outer_element" : {
      "container1" : [
        {
          "new_leaf": "value1",
          "key_leaf": "key_value1",
          "new_element": {
            "container2": [
              {
                "key_leaf2": "key_value3",
                "new_leaf": "value2"
              }
            ],
            "new_element": {
              "new_leaf": "value3"
            }
          }
        },
        {
          "key_leaf": "key_value2",
          "middle_element": {
            "container2": [
              {
                "key_leaf2": "key_value4",
                "new_element": {
                  "inner_element": {
                    "leaf3": "value6",
                    "new_leaf": "value5"
                  }
                }
              }
            ]
          }
        }
      ]
    }
  })";

  ASSERT_OK_AND_ASSIGN(auto example_json, ParseJson(kExampleJson));
  ASSERT_OK_AND_ASSIGN(auto expected_json, ParseJson(kExpectedJson));
  EXPECT_EQ(ReplaceNamesinJsonObject(
                example_json, StringMap{{"element", "new_element"},
                                        {"leaf", "new_leaf"},
                                        {"no_such_element", "such_element"}}),
            expected_json);
}

// Map of yang list paths to names of key leaves used for testing.
static const auto* const kPathKeyNameMap = new StringMap({
    {"/outer_element/container1", "key_leaf1"},
    {"/outer_element/container1/middle_element/container2", "key_leaf2"},
    {"/outer_element/container1/middle_element/container2/inner_element/"
     "container3",
     "key_leaf3"},
});

TEST(FlattenJson, TestInvalidJsonType) {
  nlohmann::json root(nlohmann::json::value_t::discarded);
  EXPECT_THAT(FlattenJsonToMap(root, *kPathKeyNameMap),
              gutil::StatusIs(absl::StatusCode::kInvalidArgument,
                              testing::HasSubstr("Invalid json type")));
}

TEST(FlattenJson, TestUnknownKeyOuter) {
  constexpr char kExampleJson[] = R"({
    "outer_element" : {
      "unknown_container" : [
        {
          "leaf": "value"
        }
      ]
    }
  })";
  ASSERT_OK_AND_ASSIGN(nlohmann::json root, ParseJson(kExampleJson));
  EXPECT_THAT(
      FlattenJsonToMap(root, *kPathKeyNameMap),
      gutil::StatusIs(
          absl::StatusCode::kInvalidArgument,
          testing::HasSubstr("No key found for path "
                             "[/outer_element/unknown_container] while parsing "
                             "path [/outer_element/unknown_container].")));
}

TEST(FlattenJson, TestUnknownKeyInner) {
  constexpr char kExampleJson[] = R"({
    "outer_element" : {
      "container1" : [
        {
          "key_leaf1": "value1",
          "middle_element": {
            "container2": [
              {
                "key_leaf2": "value2",
                "inner_element": {
                  "unknown_container": [
                    {
                      "leaf": "value"
                    }
                  ]
                }
              }
            ]
          }
        }
      ]
    }
  })";
  ASSERT_OK_AND_ASSIGN(nlohmann::json root, ParseJson(kExampleJson));
  EXPECT_THAT(FlattenJsonToMap(root, *kPathKeyNameMap),
              gutil::StatusIs(
                  absl::StatusCode::kInvalidArgument,
                  testing::HasSubstr(
                      "No key found for path "
                      "[/outer_element/container1/middle_element/container2/"
                      "inner_element/unknown_container] while parsing path "
                      "[/outer_element/container1[key_leaf1='value1']/"
                      "middle_element/container2[key_leaf2='value2']/"
                      "inner_element/unknown_container].")));
}

TEST(FlattenJson, TestMissingKeyLeafOuter) {
  constexpr char kExampleJson[] = R"({
    "outer_element" : {
      "container1" : [
        {
          "key_leaf1": "value1"
        },
        {
          "key_leaf1": "value2"
        },
        {
          "bad_key_leaf": "value"
        }
      ]
    }
  })";
  ASSERT_OK_AND_ASSIGN(nlohmann::json root, ParseJson(kExampleJson));
  EXPECT_THAT(
      FlattenJsonToMap(root, *kPathKeyNameMap),
      gutil::StatusIs(
          absl::StatusCode::kInvalidArgument,
          testing::HasSubstr(
              "No key leaf 'key_leaf1' found for array element 2 under path: "
              "[/outer_element/container1].")));
}

TEST(FlattenJson, TestMissingKeyLeafInner) {
  constexpr char kExampleJson[] = R"({
    "outer_element" : {
      "container1" : [
        {
          "key_leaf1": "value1",
          "middle_element": {
            "container2": [
              {
                "key_leaf2": "value2",
                "inner_element": {
                  "container3": [
                    {
                      "bad_key_leaf": "value3"
                    }
                  ]
                }
              }
            ]
          }
        }
      ]
    }
  })";
  ASSERT_OK_AND_ASSIGN(nlohmann::json root, ParseJson(kExampleJson));
  EXPECT_THAT(
      FlattenJsonToMap(root, *kPathKeyNameMap),
      gutil::StatusIs(
          absl::StatusCode::kInvalidArgument,
          testing::HasSubstr(
              "No key leaf 'key_leaf3' found for array element 0 under path: "
              "[/outer_element/container1[key_leaf1='value1']/middle_element/"
              "container2[key_leaf2='value2']/inner_element/container3].")));
}

TEST(FlattenJson, TestInvalidKeyLeafTypeOuter) {
  constexpr char kExampleJson[] = R"({
    "outer_element" : {
      "container1" : [
        {
          "key_leaf1": "value1"
        },
        {
          "key_leaf1": "value2"
        },
        {
          "key_leaf1": {
            "leaf": "leaf_value"
          }
        }
      ]
    }
  })";
  ASSERT_OK_AND_ASSIGN(nlohmann::json root, ParseJson(kExampleJson));
  EXPECT_THAT(
      FlattenJsonToMap(root, *kPathKeyNameMap),
      gutil::StatusIs(
          absl::StatusCode::kInvalidArgument,
          testing::HasSubstr("Invalid type 'object' for key leaf 'key_leaf1' "
                             "for array element 2 under path "
                             "[/outer_element/container1")));
}

TEST(FlattenJson, TestInvalidKeyLeafTypeInner) {
  constexpr char kExampleJson[] = R"({
    "outer_element" : {
      "container1" : [
        {
          "key_leaf1": "value1",
          "middle_element": {
            "container2": [
              {
                "key_leaf2": "value2",
                "inner_element": {
                  "container3": [
                    {
                      "key_leaf3": "value3"
                    },
                    {
                      "key_leaf3": {
                        "leaf": "leaf_value"
                      }
                    }
                  ]
                }
              }
            ]
          }
        }
      ]
    }
  })";
  ASSERT_OK_AND_ASSIGN(nlohmann::json root, ParseJson(kExampleJson));
  EXPECT_THAT(
      FlattenJsonToMap(root, *kPathKeyNameMap),
      gutil::StatusIs(
          absl::StatusCode::kInvalidArgument,
          testing::HasSubstr(
              "Invalid type 'object' for key leaf 'key_leaf3' for array "
              "element 1 under path "
              "[/outer_element/container1[key_leaf1='value1']/middle_element/"
              "container2[key_leaf2='value2']/inner_element/container3]")));
}

TEST(FlattenJson, TestEmptySuccess) {
  ASSERT_OK_AND_ASSIGN(nlohmann::json root, ParseJson(""));
  EXPECT_THAT(FlattenJsonToMap(root, *kPathKeyNameMap),
              gutil::IsOkAndHolds(StringMap{}));
}

TEST(FlattenJson, TestSuccess) {
  constexpr char kExampleJson[] = R"({
    "outer_element_1" : {
      "outer_leaf_int": -34,
      "outer_leaf_uint": 123,
      "outer_leaf_float": 6.45,
      "outer_leaf_boolean": false,
      "outer_leaf_string": "just a string"
    },
    "outer_element" : {
      "container1" : [
        {
          "key_leaf1": "outer_value1",
          "middle_element": {
            "container2": [
              {
                "key_leaf2": "middle_value1",
                "inner_element": {
                  "container3": [
                    {
                      "key_leaf3": "inner_value1",
                      "inner_object1": {
                        "leaf1": "value1"
                      }
                    },
                    {
                      "key_leaf3": -12
                    },
                    {
                      "key_leaf3": 87
                    },
                    {
                      "key_leaf3": 3.67
                    },
                    {
                      "key_leaf3": true
                    }
                  ]
                }
              },
              {
                "key_leaf2": "middle_value2",
                "inner_element": {
                  "inner_leaf": "inner_value1"
                }
              }
            ]
          }
        },
        {
          "key_leaf1": "outer_value2",
          "middle_element": {
            "outer_leaf": "outer_value"
          }
        }
      ]
    }
  })";
  ASSERT_OK_AND_ASSIGN(nlohmann::json root, ParseJson(kExampleJson));
  const auto kExpectedMap = StringMap{
      {"/outer_element_1/outer_leaf_int", "-34"},
      {"/outer_element_1/outer_leaf_uint", "123"},
      {"/outer_element_1/outer_leaf_float", "6.45"},
      {"/outer_element_1/outer_leaf_boolean", "false"},
      {"/outer_element_1/outer_leaf_string", "just a string"},

      {"/outer_element/container1[key_leaf1='outer_value1']/key_leaf1",
       "outer_value1"},
      {"/outer_element/container1[key_leaf1='outer_value1']/middle_element/"
       "container2[key_leaf2='middle_value1']/key_leaf2",
       "middle_value1"},

      {"/outer_element/container1[key_leaf1='outer_value1']/middle_element/"
       "container2[key_leaf2='middle_value1']/inner_element/"
       "container3[key_leaf3='inner_value1']/key_leaf3",
       "inner_value1"},
      {"/outer_element/container1[key_leaf1='outer_value1']/middle_element/"
       "container2[key_leaf2='middle_value1']/inner_element/"
       "container3[key_leaf3='inner_value1']/inner_object1/leaf1",
       "value1"},

      {"/outer_element/container1[key_leaf1='outer_value1']/middle_element/"
       "container2[key_leaf2='middle_value1']/inner_element/"
       "container3[key_leaf3='-12']/key_leaf3",
       "-12"},
      {"/outer_element/container1[key_leaf1='outer_value1']/middle_element/"
       "container2[key_leaf2='middle_value1']/inner_element/"
       "container3[key_leaf3='87']/key_leaf3",
       "87"},
      {"/outer_element/container1[key_leaf1='outer_value1']/middle_element/"
       "container2[key_leaf2='middle_value1']/inner_element/"
       "container3[key_leaf3='3.67']/key_leaf3",
       "3.67"},
      {"/outer_element/container1[key_leaf1='outer_value1']/middle_element/"
       "container2[key_leaf2='middle_value1']/inner_element/"
       "container3[key_leaf3='true']/key_leaf3",
       "true"},

      {"/outer_element/container1[key_leaf1='outer_value1']/middle_element/"
       "container2[key_leaf2='middle_value2']/key_leaf2",
       "middle_value2"},
      {"/outer_element/container1[key_leaf1='outer_value1']/middle_element/"
       "container2[key_leaf2='middle_value2']/inner_element/inner_leaf",
       "inner_value1"},

      {"/outer_element/container1[key_leaf1='outer_value2']/key_leaf1",
       "outer_value2"},
      {"/outer_element/container1[key_leaf1='outer_value2']/middle_element/"
       "outer_leaf",
       "outer_value"},
  };
  EXPECT_THAT(FlattenJsonToMap(root, *kPathKeyNameMap),
              gutil::IsOkAndHolds(kExpectedMap));
}

}  // namespace

}  // namespace json_yang
