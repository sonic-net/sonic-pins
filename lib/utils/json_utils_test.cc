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
#include <vector>

#include "absl/strings/str_join.h"
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
using ::testing::HasSubstr;

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

using StringSetMap =
    absl::flat_hash_map<std::string, absl::btree_set<std::string>>;
using StringMap = absl::flat_hash_map<std::string, std::string>;

using ::gutil::IsOkAndHolds;
using ::gutil::StatusIs;
using ::testing::Eq;
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

TEST(FormatJsonBestEffort, IsIdentityFunctionOnEmptyString) {
  EXPECT_EQ(FormatJsonBestEffort(""), "");
}

TEST(FormatJsonBestEffort, IsIdentityFunctionOnNonJsonStrings) {
  constexpr absl::string_view kNonJsonString = "{ definitely not valid JSON }";
  EXPECT_EQ(FormatJsonBestEffort(kNonJsonString), kNonJsonString);
}

TEST(FormatJsonBestEffort,
     PreservesSemanticsOfJsonStringsAndCanonicalizesThem) {
  nlohmann::json json;
  json["some field"] = 42;
  // We give `FormatJsonBestEffort` some liberty in formatting JSON so this test
  // is not too brittle, but we want to make sure it  at least (i) preserves
  // the semantics, and (ii) returns a canonical JSON string that is independent
  // of the formatting details of the input string.
  EXPECT_THAT(ParseJson(FormatJsonBestEffort(json.dump())),
              IsOkAndHolds(Eq(json)));
  EXPECT_EQ(
      FormatJsonBestEffort(json.dump(/*indent =*/0, /*indent_char =*/' ')),
      FormatJsonBestEffort(json.dump(/*indent =*/2, /*indent_char =*/' ')));
  EXPECT_EQ(
      FormatJsonBestEffort(json.dump(/*indent =*/2, /*indent_char =*/' ')),
      FormatJsonBestEffort(json.dump(/*indent =*/1, /*indent_char =*/'\t')));
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

TEST(ReplaceNamesinJsonObject, TestReplacementEmptyNamesMap) {
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

TEST(ReplaceNamesinJsonObject, TestInPlaceReplacementEmptyJson) {
  ASSERT_OK_AND_ASSIGN(nlohmann::json empty_json, ParseJson(""));
  ASSERT_OK_AND_ASSIGN(nlohmann::json expected_json, ParseJson(""));
  ReplaceNamesinJsonObject(StringMap{}, empty_json);
  EXPECT_EQ(empty_json, expected_json);
}

TEST(ReplaceNamesinJsonObject, TestInPlaceReplacementEmptyNamesMap) {
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
  ASSERT_OK_AND_ASSIGN(auto expected_json, ParseJson(kExampleJson));
  ReplaceNamesinJsonObject(StringMap{}, example_json);
  EXPECT_EQ(example_json, expected_json);
}

TEST(ReplaceNamesinJsonObject, TestInPlaceReplacementNamesReplaced) {
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
  ReplaceNamesinJsonObject(StringMap{{"element", "new_element"},
                                     {"leaf", "new_leaf"},
                                     {"no_such_element", "such_element"}},
                           example_json);
  EXPECT_EQ(example_json, expected_json);
}

// Map of yang list paths to names of key leaves used for testing.
static const auto* const kPathKeyNameMap = new StringSetMap({
    {"/outer_element/container1", {"key_leaf1"}},
    {"/outer_element/container1/middle_element/container2", {"key_leaf2"}},
    {"/outer_element/container1/middle_element/container2/inner_element/"
     "container3",
     {"key_leaf3"}},
    {"/outer_element2/known_container3/known_list1", {"leaf5"}},
    {"/known_outer_element4", {"leaf7"}},
});

static const auto* const kPathKeyNameMapWithMultipleKeys = new StringSetMap({
    {"/outer_element/container1", {"key_leaf1"}},
    {"/outer_element/container1/middle_element/container2", {"key_leaf2"}},
    {"/outer_element/container1/middle_element/container2/inner_element/"
     "container3",
     {"key_leaf3", "key_leaf4"}},
});

TEST(FlattenJson, TestInvalidJsonType) {
  nlohmann::json root(nlohmann::json::value_t::discarded);
  EXPECT_THAT(FlattenJsonToMap(root, *kPathKeyNameMap,
                               /*ignore_unknown_key_paths=*/false),
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
  std::vector<std::string> missing_paths = {"/outer_element/unknown_container"};
  EXPECT_THAT(FlattenJsonToMap(root, *kPathKeyNameMap,
                               /*ignore_unknown_key_paths=*/false),
              gutil::StatusIs(absl::StatusCode::kInvalidArgument,
                              testing::HasSubstr(absl::StrCat(
                                  "No key found in the map for the paths: \n",
                                  absl::StrJoin(missing_paths, "\n")))));
}

TEST(FlattenJson, TestUnknownKeyOuterIgnoreUnknownKeyPaths) {
  constexpr char kExampleJson[] = R"({
    "outer_element" : {
      "unknown_container" : [
        {
          "leaf": "value"
        }
      ],
      "other_leaf": "other_value"
    }
  })";
  const auto kExpectedMap = StringMap{
      {"/outer_element/other_leaf", "other_value"},
  };
  ASSERT_OK_AND_ASSIGN(nlohmann::json root, ParseJson(kExampleJson));
  EXPECT_THAT(FlattenJsonToMap(root, *kPathKeyNameMap,
                               /*ignore_unknown_key_paths=*/true),
              gutil::IsOkAndHolds(kExpectedMap));
}

TEST(FlattenJson, TestUnknownKeyMultiple) {
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
                  ],
                 "unknown_container2": [
                    {
                      "leaf2": "value2"
                    }
                  ]
                }
              }
            ]
          }
        }
      ]
    },
    "outer_element2" : {
      "unknown_container3" : [
        {
          "leaf4": "value"
        }
      ],
      "known_container3" : {
      "known_list1" : [
        {
          "leaf5": "value"
        }
      ]
      } 
    },
    "unknown_outer_element3" : [
        {
          "leaf6": "value"
        }
    ],
    "known_outer_element4" : [
        {
          "leaf7": "value"
        }
    ]
  })";
  ASSERT_OK_AND_ASSIGN(nlohmann::json root, ParseJson(kExampleJson));
  std::vector<std::string> missing_paths = {
      "/outer_element/container1/middle_element/container2/inner_element/"
      "unknown_container",
      "/outer_element/container1/middle_element/container2/inner_element/"
      "unknown_container2",
      "/outer_element2/unknown_container3", "/unknown_outer_element3"};
  EXPECT_THAT(FlattenJsonToMap(root, *kPathKeyNameMap,
                               /*ignore_unknown_key_paths=*/false),
              gutil::StatusIs(absl::StatusCode::kInvalidArgument,
                              testing::StrEq(absl::StrCat(
                                  "No key found in the map for the paths: \n",
                                  absl::StrJoin(missing_paths, "\n")))));
}

TEST(FlattenJson, TestUnknownKeyInnerIgnoreUnknownKeyPaths) {
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
                  ],
                  "inner_leaf": "inner_value"
                }
              }
            ]
          }
        }
      ]
    }
  })";
  const auto kExpectedMap = StringMap{
      {"/outer_element/container1[key_leaf1='value1']/key_leaf1", "value1"},
      {"/outer_element/container1[key_leaf1='value1']/middle_element/"
       "container2[key_leaf2='value2']/key_leaf2",
       "value2"},
      {"/outer_element/container1[key_leaf1='value1']/middle_element/"
       "container2[key_leaf2='value2']/inner_element/inner_leaf",
       "inner_value"},
  };
  ASSERT_OK_AND_ASSIGN(nlohmann::json root, ParseJson(kExampleJson));
  EXPECT_THAT(FlattenJsonToMap(root, *kPathKeyNameMap,
                               /*ignore_unknown_key_paths=*/true),
              gutil::IsOkAndHolds(kExpectedMap));
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
      FlattenJsonToMap(root, *kPathKeyNameMap,
                       /*ignore_unknown_key_paths=*/false),
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
      FlattenJsonToMap(root, *kPathKeyNameMap,
                       /*ignore_unknown_key_paths=*/false),
      gutil::StatusIs(
          absl::StatusCode::kInvalidArgument,
          testing::HasSubstr(
              "No key leaf 'key_leaf3' found for array element 0 under path: "
              "[/outer_element/container1[key_leaf1='value1']/middle_element/"
              "container2[key_leaf2='value2']/inner_element/container3].")));
}

TEST(FlattenJson, TestLeafLists) {
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
                    0,
                    1,
                    2
                  ],
                  "container4": [
                    0,
                    -1,
                    -2
                  ],
                  "container5": [
                    true
                  ],
                  "container6": [
                    "a",
                    "b"
                  ],
                  "container7": [
                    9.0,
                    2.7
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
  const auto path_map = StringSetMap({
      {"/outer_element/container1", {"key_leaf1"}},
      {"/outer_element/container1/middle_element/container2", {"key_leaf2"}},
      {"/outer_element/container1/middle_element/container2/inner_element/"
       "container3",
       {}},
      {"/outer_element/container1/middle_element/container2/inner_element/"
       "container4",
       {}},
      {"/outer_element/container1/middle_element/container2/inner_element/"
       "container5",
       {}},
      {"/outer_element/container1/middle_element/container2/inner_element/"
       "container6",
       {}},
      {"/outer_element/container1/middle_element/container2/inner_element/"
       "container7",
       {}},
  });
  EXPECT_THAT(
      FlattenJsonToMap(root, path_map, /*ignore_unknown_key_paths=*/false),
      gutil::IsOkAndHolds(StringMap{
          {"/outer_element/container1[key_leaf1='value1']/middle_element/"
           "container2[key_leaf2='value2']/inner_element/container7['2.7']",
           "2.7"},
          {"/outer_element/container1[key_leaf1='value1']/middle_element/"
           "container2[key_leaf2='value2']/inner_element/container4['-2']",
           "-2"},
          {"/outer_element/container1[key_leaf1='value1']/middle_element/"
           "container2[key_leaf2='value2']/inner_element/"
           "container5['true']",
           "true"},
          {"/outer_element/container1[key_leaf1='value1']/middle_element/"
           "container2[key_leaf2='value2']/inner_element/container3['2']",
           "2"},
          {"/outer_element/container1[key_leaf1='value1']/middle_element/"
           "container2[key_leaf2='value2']/inner_element/container7['9']",
           "9"},
          {"/outer_element/container1[key_leaf1='value1']/middle_element/"
           "container2[key_leaf2='value2']/inner_element/container3['0']",
           "0"},
          {"/outer_element/container1[key_leaf1='value1']/middle_element/"
           "container2[key_leaf2='value2']/inner_element/container6['b']",
           "b"},
          {"/outer_element/container1[key_leaf1='value1']/middle_element/"
           "container2[key_leaf2='value2']/inner_element/container6['a']",
           "a"},
          {"/outer_element/container1[key_leaf1='value1']/middle_element/"
           "container2[key_leaf2='value2']/inner_element/container3['1']",
           "1"},
          {"/outer_element/container1[key_leaf1='value1']/middle_element/"
           "container2[key_leaf2='value2']/inner_element/container4['0']",
           "0"},
          {"/outer_element/container1[key_leaf1='value1']/key_leaf1", "value1"},
          {"/outer_element/container1[key_leaf1='value1']/middle_element/"
           "container2[key_leaf2='value2']/inner_element/container4['-1']",
           "-1"},
          {"/outer_element/container1[key_leaf1='value1']/middle_element/"
           "container2[key_leaf2='value2']/key_leaf2",
           "value2"}}));
}

TEST(FlattenJson, TestLeafListsNonPrimitive) {
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
  const auto path_map = StringSetMap({
      {"/outer_element/container1", {"key_leaf1"}},
      {"/outer_element/container1/middle_element/container2", {"key_leaf2"}},
      {"/outer_element/container1/middle_element/container2/inner_element/"
       "container3",
       {}},
  });
  EXPECT_THAT(
      FlattenJsonToMap(root, path_map, /*ignore_unknown_key_paths=*/false),
      gutil::StatusIs(
          absl::StatusCode::kInvalidArgument,
          testing::HasSubstr(
              "Invalid type 'object' for array element (leaf list) 0 under "
              "path "
              "[/outer_element/container1[key_leaf1='value1']/middle_element/"
              "container2[key_leaf2='value2']/inner_element/container3]. "
              "Expected: integer, unsigned, float, string, bool.")));
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
      FlattenJsonToMap(root, *kPathKeyNameMap,
                       /*ignore_unknown_key_paths=*/false),
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
                      "key_leaf3": "value3",
                      "key_leaf4" : "value4"
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
      FlattenJsonToMap(root, *kPathKeyNameMapWithMultipleKeys,
                       /*ignore_unknown_key_paths=*/false),
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
  EXPECT_THAT(FlattenJsonToMap(root, *kPathKeyNameMap,
                               /*ignore_unknown_key_paths=*/false),
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
                      },
                      "key_leaf4": "inner_value2"
                    },
                    {
                      "key_leaf3": -12,
                      "key_leaf4": -13
                    },
                    {
                      "key_leaf3": 87,
                      "key_leaf4": 88
                    },
                    {
                      "key_leaf3": 3.67,
                      "key_leaf4": 4.5
                    },
                    {
                      "key_leaf3": true,
                      "key_leaf4": false
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
       "container3[key_leaf3='inner_value1'][key_leaf4='inner_value2']/"
       "key_leaf3",
       "inner_value1"},
      {"/outer_element/container1[key_leaf1='outer_value1']/middle_element/"
       "container2[key_leaf2='middle_value1']/inner_element/"
       "container3[key_leaf3='inner_value1'][key_leaf4='inner_value2']/"
       "key_leaf4",
       "inner_value2"},
      {"/outer_element/container1[key_leaf1='outer_value1']/middle_element/"
       "container2[key_leaf2='middle_value1']/inner_element/"
       "container3[key_leaf3='inner_value1'][key_leaf4='inner_value2']/"
       "inner_object1/leaf1",
       "value1"},

      {"/outer_element/container1[key_leaf1='outer_value1']/middle_element/"
       "container2[key_leaf2='middle_value1']/inner_element/"
       "container3[key_leaf3='-12'][key_leaf4='-13']/key_leaf3",
       "-12"},
      {"/outer_element/container1[key_leaf1='outer_value1']/middle_element/"
       "container2[key_leaf2='middle_value1']/inner_element/"
       "container3[key_leaf3='-12'][key_leaf4='-13']/key_leaf4",
       "-13"},
      {"/outer_element/container1[key_leaf1='outer_value1']/middle_element/"
       "container2[key_leaf2='middle_value1']/inner_element/"
       "container3[key_leaf3='87'][key_leaf4='88']/key_leaf3",
       "87"},
      {"/outer_element/container1[key_leaf1='outer_value1']/middle_element/"
       "container2[key_leaf2='middle_value1']/inner_element/"
       "container3[key_leaf3='87'][key_leaf4='88']/key_leaf4",
       "88"},
      {"/outer_element/container1[key_leaf1='outer_value1']/middle_element/"
       "container2[key_leaf2='middle_value1']/inner_element/"
       "container3[key_leaf3='3.67'][key_leaf4='4.5']/key_leaf3",
       "3.67"},
      {"/outer_element/container1[key_leaf1='outer_value1']/middle_element/"
       "container2[key_leaf2='middle_value1']/inner_element/"
       "container3[key_leaf3='3.67'][key_leaf4='4.5']/key_leaf4",
       "4.5"},
      {"/outer_element/container1[key_leaf1='outer_value1']/middle_element/"
       "container2[key_leaf2='middle_value1']/inner_element/"
       "container3[key_leaf3='true'][key_leaf4='false']/key_leaf3",
       "true"},
      {"/outer_element/container1[key_leaf1='outer_value1']/middle_element/"
       "container2[key_leaf2='middle_value1']/inner_element/"
       "container3[key_leaf3='true'][key_leaf4='false']/key_leaf4",
       "false"},
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
  EXPECT_THAT(FlattenJsonToMap(root, *kPathKeyNameMapWithMultipleKeys,
                               /*ignore_unknown_key_paths=*/false),
              gutil::IsOkAndHolds(kExpectedMap));
}

TEST(IsJsonSubset, TestBadSource) {
  constexpr char kGoodJson[] = R"({
    "outer_element": {
      "leaf" : "value"
    }
  })";
  nlohmann::json source(nlohmann::json::value_t::discarded);
  ASSERT_OK_AND_ASSIGN(nlohmann::json target, ParseJson(kGoodJson));

  std::vector<std::string> differences;
  EXPECT_THAT(IsJsonSubset(source, target, *kPathKeyNameMap, differences),
              gutil::StatusIs(absl::StatusCode::kInvalidArgument));
  EXPECT_TRUE(differences.empty());
}

TEST(IsJsonSubset, TestBadTarget) {
  constexpr char kGoodJson[] = R"({
    "outer_element": {
      "leaf" : "value"
    }
  })";
  ASSERT_OK_AND_ASSIGN(nlohmann::json source, ParseJson(kGoodJson));
  nlohmann::json target(nlohmann::json::value_t::discarded);

  std::vector<std::string> differences;
  EXPECT_THAT(IsJsonSubset(source, target, *kPathKeyNameMap, differences),
              gutil::StatusIs(absl::StatusCode::kInvalidArgument));
  EXPECT_TRUE(differences.empty());
}

TEST(IsJsonSubset, TestBothEmpty) {
  ASSERT_OK_AND_ASSIGN(nlohmann::json source, ParseJson(""));
  ASSERT_OK_AND_ASSIGN(nlohmann::json target, ParseJson(""));

  std::vector<std::string> differences;
  EXPECT_THAT(IsJsonSubset(source, target, *kPathKeyNameMap, differences),
              gutil::IsOkAndHolds(true));
  EXPECT_TRUE(differences.empty());
}

TEST(IsJsonSubset, TestSourceEmpty) {
  constexpr char kExampleJson[] = R"({
    "outer_element": {
      "leaf" : "value"
    }
  })";
  ASSERT_OK_AND_ASSIGN(nlohmann::json source, ParseJson(""));
  ASSERT_OK_AND_ASSIGN(nlohmann::json target, ParseJson(kExampleJson));

  std::vector<std::string> differences;
  EXPECT_THAT(IsJsonSubset(source, target, *kPathKeyNameMap, differences),
              gutil::IsOkAndHolds(true));
  EXPECT_TRUE(differences.empty());
}

TEST(IsJsonSubset, TestTargetEmpty) {
  constexpr char kExampleJson[] = R"({
    "outer_element": {
      "leaf" : "value"
    }
  })";
  ASSERT_OK_AND_ASSIGN(nlohmann::json source, ParseJson(kExampleJson));
  ASSERT_OK_AND_ASSIGN(nlohmann::json target, ParseJson(""));

  std::vector<std::string> differences;
  EXPECT_THAT(IsJsonSubset(source, target, *kPathKeyNameMap, differences),
              gutil::IsOkAndHolds(false));
  EXPECT_THAT(differences,
              ElementsAre(testing::HasSubstr(
                  "Missing: [/outer_element/leaf] with value 'value'")));
}

TEST(IsJsonSubset, LeafListUnstableOrderSuccess) {
  constexpr char kSourceConfigJson[] = R"({
    "outer_element": {
      "leaf" : ["ip1", "ip2"]
    }
  })";
  ASSERT_OK_AND_ASSIGN(nlohmann::json source, ParseJson(kSourceConfigJson));

  constexpr char kTargetConfigJson[] = R"({
    "outer_element": {
      "leaf" : ["ip2", "ip1"]
    }
  })";
  ASSERT_OK_AND_ASSIGN(nlohmann::json target, ParseJson(kTargetConfigJson));

  std::vector<std::string> differences;
  const auto path_map = StringSetMap({
      {"/outer_element/leaf", {}},
  });
  EXPECT_THAT(IsJsonSubset(source, target, path_map, differences),
              gutil::IsOkAndHolds(true));
}

TEST(IsJsonSubset, LeafListSubsetFail) {
  constexpr char kSourceConfigJson[] = R"({
    "outer_element": {
      "leaf" : ["ip1", "ip2"]
    }
  })";
  ASSERT_OK_AND_ASSIGN(nlohmann::json source, ParseJson(kSourceConfigJson));

  constexpr char kTargetConfigJson[] = R"({
    "outer_element": {
      "leaf" : ["ip1"]
    }
  })";
  ASSERT_OK_AND_ASSIGN(nlohmann::json target, ParseJson(kTargetConfigJson));

  std::vector<std::string> differences;
  const auto path_map = StringSetMap({
      {"/outer_element/leaf", {}},
  });
  EXPECT_THAT(IsJsonSubset(source, target, path_map, differences),
              gutil::IsOkAndHolds(false));
  EXPECT_THAT(differences,
              ElementsAre(HasSubstr(
                  "Missing: [/outer_element/leaf['ip2']] with value 'ip2'")));
}
TEST(IsJsonSubset, LeafSubsetFail) {
  constexpr char kSourceConfigJson[] = R"({
    "outer_element": {
      "leaf" : ["ip1", "ip2"]
    }
  })";
  ASSERT_OK_AND_ASSIGN(nlohmann::json source, ParseJson(kSourceConfigJson));

  constexpr char kTargetConfigJson[] = R"({
    "outer_element": {
      "leaf" : "ip1"
    }
  })";
  ASSERT_OK_AND_ASSIGN(nlohmann::json target, ParseJson(kTargetConfigJson));

  std::vector<std::string> differences;
  const auto path_map = StringSetMap({
      {"/outer_element/leaf", {}},
  });
  EXPECT_THAT(IsJsonSubset(source, target, path_map, differences),
              gutil::IsOkAndHolds(false));
  EXPECT_THAT(
      differences,
      testing::UnorderedElementsAre(
          HasSubstr("Missing: [/outer_element/leaf['ip1']] with value 'ip1'"),
          HasSubstr("Missing: [/outer_element/leaf['ip2']] with value 'ip2'")));
}

TEST(IsJsonSubset, LeafListSupersetSuccess) {
  constexpr char kSourceConfigJson[] = R"({
    "outer_element": {
      "leaf" : ["ip1"]
    }
  })";
  ASSERT_OK_AND_ASSIGN(nlohmann::json source, ParseJson(kSourceConfigJson));

  constexpr char kTargetConfigJson[] = R"({
    "outer_element": {
      "leaf" : ["ip1",  "ip2"]
    }
  })";
  ASSERT_OK_AND_ASSIGN(nlohmann::json target, ParseJson(kTargetConfigJson));

  std::vector<std::string> differences;
  const auto path_map = StringSetMap({
      {"/outer_element/leaf", {}},
  });
  EXPECT_THAT(IsJsonSubset(source, target, path_map, differences),
              gutil::IsOkAndHolds(true));
}

TEST(IsJsonSubset, TestIsSubset) {
  constexpr char kSourceJson[] = R"({
    "outer_element": {
      "container1" : [
        {
          "key_leaf1" : "container1_value1",
          "middle_element" : {
            "container2" : [
              {
                "key_leaf2" : "container2_value1",
                "inner_element" : {
                  "leaf1" : "value1",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1",
                      "leaf2" : "value2"
                    }
                  ]
                }
              },
              {
                "key_leaf2" : "container2_value2",
                "inner_element" : {
                  "leaf1" : "value3",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1",
                      "leaf2" : "value4"
                    }
                  ]
                }
              }
            ]
          }
        },
        {
          "key_leaf1" : "container1_value2",
          "middle_element" : {
            "container2" : [
              {
                "key_leaf2" : "container2_value1",
                "inner_element" : {
                  "leaf1" : "value5",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1",
                      "leaf2" : "value6"
                    }
                  ]
                }
              },
              {
                "key_leaf2" : "container2_value2",
                "inner_element" : {
                  "leaf1" : "value7",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1",
                      "leaf2" : "value8"
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
  constexpr char kTargetJson[] = R"({
    "outer_element": {
      "container1" : [
        {
          "key_leaf1" : "container1_value2",
          "middle_element" : {
            "container2" : [
              {
                "key_leaf2" : "container2_value2",
                "inner_element" : {
                  "leaf1" : "value7",
                  "container3" : [
                    {
                      "leaf2" : "value8",
                      "key_leaf3" : "container3_value1",
                      "extra_leaf2" : "extra_valu8"
                    }
                  ]
                }
              },
              {
                "key_leaf2" : "container2_value1",
                "inner_element" : {
                  "leaf1" : "value5",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1",
                      "leaf2" : "value6",
                      "extra_leaf2" : "extra_value6"
                    }
                  ]
                }
              }
            ]
          }
        },
        {
          "key_leaf1" : "container1_value1",
          "middle_element" : {
            "container2" : [
              {
                "key_leaf2" : "container2_value1",
                "inner_element" : {
                  "leaf1" : "value1",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1",
                      "leaf2" : "value2"
                    }
                  ]
                }
              },
              {
                "key_leaf2" : "container2_value2",
                "inner_element" : {
                  "leaf1" : "value3",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1",
                      "leaf2" : "value4",
                      "extra_leaf2" : "extra_value4"
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
  ASSERT_OK_AND_ASSIGN(nlohmann::json source, ParseJson(kSourceJson));
  ASSERT_OK_AND_ASSIGN(nlohmann::json target, ParseJson(kTargetJson));

  std::vector<std::string> differences;
  EXPECT_THAT(IsJsonSubset(source, target, *kPathKeyNameMap, differences),
              gutil::IsOkAndHolds(true));
  EXPECT_TRUE(differences.empty());
}

TEST(IsJsonSubset, TestNotSubsetMismatch) {
  constexpr char kSourceJson[] = R"({
    "outer_element": {
      "container1" : [
        {
          "key_leaf1" : "container1_value1",
          "middle_element" : {
            "container2" : [
              {
                "key_leaf2" : "container2_value1",
                "inner_element" : {
                  "leaf1" : "value1",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1"
                    }
                  ]
                }
              },
              {
                "key_leaf2" : "container2_value2",
                "inner_element" : {
                  "leaf1" : "value3",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1",
                      "leaf2" : "value4"
                    }
                  ]
                }
              }
            ]
          }
        },
        {
          "key_leaf1" : "container1_value2",
          "middle_element" : {
            "container2" : [
              {
                "key_leaf2" : "container2_value1",
                "inner_element" : {
                  "leaf1" : "value5",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1",
                      "leaf2" : "value6"
                    }
                  ]
                }
              },
              {
                "key_leaf2" : "container2_value2",
                "inner_element" : {
                  "leaf1" : "value7",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1",
                      "leaf2" : "value8"
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
  constexpr char kTargetJson[] = R"({
    "outer_element": {
      "container1" : [
        {
          "key_leaf1" : "container1_value2",
          "middle_element" : {
            "container2" : [
              {
                "key_leaf2" : "container2_value2",
                "inner_element" : {
                  "leaf1" : "value7",
                  "container3" : [
                    {
                      "leaf2" : "another_value8",
                      "key_leaf3" : "container3_value1"
                    }
                  ]
                }
              },
              {
                "key_leaf2" : "container2_value1",
                "inner_element" : {
                  "leaf1" : "value5",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1",
                      "leaf2" : "another_value6"
                    }
                  ]
                }
              }
            ]
          }
        },
        {
          "key_leaf1" : "container1_value1",
          "middle_element" : {
            "container2" : [
              {
                "key_leaf2" : "container2_value1",
                "inner_element" : {
                  "leaf1" : "value1",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1"
                    }
                  ]
                }
              },
              {
                "key_leaf2" : "container2_value2",
                "inner_element" : {
                  "leaf1" : "value3",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1",
                      "leaf2" : "value4"
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
  ASSERT_OK_AND_ASSIGN(nlohmann::json source, ParseJson(kSourceJson));
  ASSERT_OK_AND_ASSIGN(nlohmann::json target, ParseJson(kTargetJson));

  std::vector<std::string> differences;
  EXPECT_THAT(IsJsonSubset(source, target, *kPathKeyNameMap, differences),
              gutil::IsOkAndHolds(false));
  EXPECT_THAT(
      differences,
      testing::UnorderedElementsAre(
          testing::HasSubstr(
              "Mismatch: "
              "[/outer_element/container1[key_leaf1='container1_value2']/"
              "middle_element/container2[key_leaf2='container2_value2']/"
              "inner_element/container3[key_leaf3='container3_value1']/leaf2]: "
              "'value8' != 'another_value8'"),
          testing::HasSubstr(
              "Mismatch: "
              "[/outer_element/container1[key_leaf1='container1_value2']/"
              "middle_element/container2[key_leaf2='container2_value1']/"
              "inner_element/container3[key_leaf3='container3_value1']/leaf2]: "
              "'value6' != 'another_value6'")));
}

TEST(IsJsonSubset, TestNotSubsetMissing) {
  constexpr char kSourceJson[] = R"({
    "outer_element": {
      "container1" : [
        {
          "key_leaf1" : "container1_value1",
          "middle_element" : {
            "container2" : [
              {
                "key_leaf2" : "container2_value1",
                "inner_element" : {
                  "leaf1" : "value1",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1",
                      "leaf2" : "value2"
                    }
                  ]
                }
              },
              {
                "key_leaf2" : "container2_value2",
                "inner_element" : {
                  "leaf1" : "value3",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1",
                      "leaf2" : "value4"
                    }
                  ]
                }
              }
            ]
          }
        },
        {
          "key_leaf1" : "container1_value2",
          "middle_element" : {
            "container2" : [
              {
                "key_leaf2" : "container2_value1",
                "inner_element" : {
                  "leaf1" : "value5",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1",
                      "leaf2" : "value6"
                    }
                  ]
                }
              },
              {
                "key_leaf2" : "container2_value2",
                "inner_element" : {
                  "leaf1" : "value7",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1",
                      "leaf2" : "value8"
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
  constexpr char kTargetJson[] = R"({
    "outer_element": {
      "container1" : [
        {
          "key_leaf1" : "container1_value2",
          "middle_element" : {
            "container2" : [
              {
                "key_leaf2" : "container2_value2",
                "inner_element" : {
                  "leaf1" : "value7",
                  "container3" : [
                    {
                      "leaf2" : "value8",
                      "key_leaf3" : "container3_value1"
                    }
                  ]
                }
              },
              {
                "key_leaf2" : "container2_value1",
                "inner_element" : {
                  "leaf1" : "value5",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1",
                      "leaf2" : "value6"
                    }
                  ]
                }
              }
            ]
          }
        },
        {
          "key_leaf1" : "container1_value1",
          "middle_element" : {
            "container2" : [
              {
                "key_leaf2" : "container2_value1",
                "inner_element" : {
                  "leaf1" : "value1",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1"
                    }
                  ]
                }
              },
              {
                "key_leaf2" : "container2_value2",
                "inner_element" : {
                  "leaf1" : "value3",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1",
                      "leaf2" : "value4"
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
  ASSERT_OK_AND_ASSIGN(nlohmann::json source, ParseJson(kSourceJson));
  ASSERT_OK_AND_ASSIGN(nlohmann::json target, ParseJson(kTargetJson));

  std::vector<std::string> differences;
  EXPECT_THAT(IsJsonSubset(source, target, *kPathKeyNameMap, differences),
              gutil::IsOkAndHolds(false));
  EXPECT_THAT(differences,
              testing::UnorderedElementsAre(testing::HasSubstr(
                  "Missing: "
                  "[/outer_element/container1[key_leaf1='container1_value1']/"
                  "middle_element/container2[key_leaf2='container2_value1']/"
                  "inner_element/container3[key_leaf3='container3_value1']/"
                  "leaf2] with value 'value2'")));
}

TEST(AreJsonEqual, TestBadLhsArgument) {
  constexpr char kGoodJson[] = R"({
    "outer_element": {
      "leaf" : "value"
    }
  })";
  nlohmann::json lhs(nlohmann::json::value_t::discarded);
  ASSERT_OK_AND_ASSIGN(nlohmann::json rhs, ParseJson(kGoodJson));

  std::vector<std::string> differences;
  EXPECT_THAT(AreJsonEqual(lhs, rhs, *kPathKeyNameMap, differences),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(AreJsonEqual, TestBadRhsArgument) {
  constexpr char kGoodJson[] = R"({
    "outer_element": {
      "leaf" : "value"
    }
  })";
  ASSERT_OK_AND_ASSIGN(nlohmann::json lhs, ParseJson(kGoodJson));
  nlohmann::json rhs(nlohmann::json::value_t::discarded);

  std::vector<std::string> differences;
  EXPECT_THAT(AreJsonEqual(lhs, rhs, *kPathKeyNameMap, differences),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(AreJsonEqual, TestBothEmpty) {
  ASSERT_OK_AND_ASSIGN(nlohmann::json lhs, ParseJson(""));
  ASSERT_OK_AND_ASSIGN(nlohmann::json rhs, ParseJson(""));

  std::vector<std::string> differences;
  ASSERT_OK_AND_ASSIGN(bool is_equal,
                       AreJsonEqual(lhs, rhs, *kPathKeyNameMap, differences));
  EXPECT_TRUE(is_equal && differences.empty());
}

TEST(AreJsonEqual, TestLhsEmpty) {
  constexpr char kExampleJson[] = R"({
    "outer_element": {
      "leaf" : "value"
    }
  })";
  ASSERT_OK_AND_ASSIGN(nlohmann::json lhs, ParseJson(""));
  ASSERT_OK_AND_ASSIGN(nlohmann::json rhs, ParseJson(kExampleJson));

  std::vector<std::string> differences;
  ASSERT_OK_AND_ASSIGN(bool is_equal,
                       AreJsonEqual(lhs, rhs, *kPathKeyNameMap, differences));
  EXPECT_FALSE(is_equal);
  EXPECT_THAT(differences,
              ElementsAre(testing::HasSubstr(
                  "Missing lhs: [/outer_element/leaf] with value 'value'")));
}

TEST(AreJsonEqual, TestRhsEmpty) {
  constexpr char kExampleJson[] = R"({
    "outer_element": {
      "leaf" : "value"
    }
  })";
  ASSERT_OK_AND_ASSIGN(nlohmann::json lhs, ParseJson(kExampleJson));
  ASSERT_OK_AND_ASSIGN(nlohmann::json rhs, ParseJson(""));

  std::vector<std::string> differences;
  ASSERT_OK_AND_ASSIGN(bool is_equal,
                       AreJsonEqual(lhs, rhs, *kPathKeyNameMap, differences));
  EXPECT_FALSE(is_equal);
  EXPECT_THAT(differences,
              ElementsAre(testing::HasSubstr(
                  "Missing rhs: [/outer_element/leaf] with value 'value'")));
}

TEST(AreJsonEqual, TestAreEqual) {
  constexpr char kLhsJson[] = R"({
    "outer_element": {
      "container1" : [
        {
          "key_leaf1" : "container1_value1",
          "middle_element" : {
            "container2" : [
              {
                "key_leaf2" : "container2_value1",
                "inner_element" : {
                  "leaf1" : "value1",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1",
                      "leaf2" : "value2"
                    }
                  ]
                }
              },
              {
                "key_leaf2" : "container2_value2",
                "inner_element" : {
                  "leaf1" : "value3",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1",
                      "leaf2" : "value4"
                    }
                  ]
                }
              }
            ]
          }
        },
        {
          "key_leaf1" : "container1_value2",
          "middle_element" : {
            "container2" : [
              {
                "key_leaf2" : "container2_value1",
                "inner_element" : {
                  "leaf1" : "value5",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1",
                      "leaf2" : "value6"
                    }
                  ]
                }
              },
              {
                "key_leaf2" : "container2_value2",
                "inner_element" : {
                  "leaf1" : "value7",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1",
                      "leaf2" : "value8"
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
  constexpr char kRhsJson[] = R"({
    "outer_element": {
      "container1" : [
        {
          "key_leaf1" : "container1_value2",
          "middle_element" : {
            "container2" : [
              {
                "key_leaf2" : "container2_value2",
                "inner_element" : {
                  "leaf1" : "value7",
                  "container3" : [
                    {
                      "leaf2" : "value8",
                      "key_leaf3" : "container3_value1"
                    }
                  ]
                }
              },
              {
                "key_leaf2" : "container2_value1",
                "inner_element" : {
                  "leaf1" : "value5",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1",
                      "leaf2" : "value6"
                    }
                  ]
                }
              }
            ]
          }
        },
        {
          "key_leaf1" : "container1_value1",
          "middle_element" : {
            "container2" : [
              {
                "key_leaf2" : "container2_value1",
                "inner_element" : {
                  "leaf1" : "value1",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1",
                      "leaf2" : "value2"
                    }
                  ]
                }
              },
              {
                "key_leaf2" : "container2_value2",
                "inner_element" : {
                  "leaf1" : "value3",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1",
                      "leaf2" : "value4"
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
  ASSERT_OK_AND_ASSIGN(nlohmann::json lhs, ParseJson(kLhsJson));
  ASSERT_OK_AND_ASSIGN(nlohmann::json rhs, ParseJson(kRhsJson));

  std::vector<std::string> differences;
  ASSERT_OK_AND_ASSIGN(bool is_equal,
                       AreJsonEqual(lhs, rhs, *kPathKeyNameMap, differences));
  EXPECT_TRUE(is_equal && differences.empty());
}

TEST(AreJsonEqual, TestNotEqualMismatch) {
  constexpr char kLhsJson[] = R"({
    "outer_element": {
      "container1" : [
        {
          "key_leaf1" : "container1_value1",
          "middle_element" : {
            "container2" : [
              {
                "key_leaf2" : "container2_value1",
                "inner_element" : {
                  "leaf1" : "value1",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1"
                    }
                  ]
                }
              },
              {
                "key_leaf2" : "container2_value2",
                "inner_element" : {
                  "leaf1" : "value3",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1",
                      "leaf2" : "value4"
                    }
                  ]
                }
              }
            ]
          }
        },
        {
          "key_leaf1" : "container1_value2",
          "middle_element" : {
            "container2" : [
              {
                "key_leaf2" : "container2_value1",
                "inner_element" : {
                  "leaf1" : "value5",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1",
                      "leaf2" : "value6"
                    }
                  ]
                }
              },
              {
                "key_leaf2" : "container2_value2",
                "inner_element" : {
                  "leaf1" : "value7",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1",
                      "leaf2" : "value8"
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
  constexpr char kRhsJson[] = R"({
    "outer_element": {
      "container1" : [
        {
          "key_leaf1" : "container1_value2",
          "middle_element" : {
            "container2" : [
              {
                "key_leaf2" : "container2_value2",
                "inner_element" : {
                  "leaf1" : "value7",
                  "container3" : [
                    {
                      "leaf2" : "another_value8",
                      "key_leaf3" : "container3_value1"
                    }
                  ]
                }
              },
              {
                "key_leaf2" : "container2_value1",
                "inner_element" : {
                  "leaf1" : "value5",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1",
                      "leaf2" : "another_value6"
                    }
                  ]
                }
              }
            ]
          }
        },
        {
          "key_leaf1" : "container1_value1",
          "middle_element" : {
            "container2" : [
              {
                "key_leaf2" : "container2_value1",
                "inner_element" : {
                  "leaf1" : "value1",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1"
                    }
                  ]
                }
              },
              {
                "key_leaf2" : "container2_value2",
                "inner_element" : {
                  "leaf1" : "value3",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1",
                      "leaf2" : "value4"
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
  ASSERT_OK_AND_ASSIGN(nlohmann::json lhs, ParseJson(kLhsJson));
  ASSERT_OK_AND_ASSIGN(nlohmann::json rhs, ParseJson(kRhsJson));

  std::vector<std::string> differences;
  ASSERT_OK_AND_ASSIGN(bool is_equal,
                       AreJsonEqual(lhs, rhs, *kPathKeyNameMap, differences));
  EXPECT_FALSE(is_equal);
  EXPECT_THAT(
      differences,
      testing::UnorderedElementsAre(
          testing::HasSubstr(
              "Mismatch: "
              "[/outer_element/container1[key_leaf1='container1_value2']/"
              "middle_element/container2[key_leaf2='container2_value1']/"
              "inner_element/container3[key_leaf3='container3_value1']/leaf2]: "
              "'value6' != 'another_value6'"),
          testing::HasSubstr(
              "Mismatch: "
              "[/outer_element/container1[key_leaf1='container1_value2']/"
              "middle_element/container2[key_leaf2='container2_value2']/"
              "inner_element/container3[key_leaf3='container3_value1']/leaf2]: "
              "'value8' != 'another_value8'")));
}

TEST(AreJsonEqual, TestNotEqualMissingLhs) {
  constexpr char kLhsJson[] = R"({
    "outer_element": {
      "container1" : [
        {
          "key_leaf1" : "container1_value1",
          "middle_element" : {
            "container2" : [
              {
                "key_leaf2" : "container2_value1",
                "inner_element" : {
                  "leaf1" : "value1",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1"
                    }
                  ]
                }
              },
              {
                "key_leaf2" : "container2_value2",
                "inner_element" : {
                  "leaf1" : "value3",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1",
                      "leaf2" : "value4"
                    }
                  ]
                }
              }
            ]
          }
        },
        {
          "key_leaf1" : "container1_value2",
          "middle_element" : {
            "container2" : [
              {
                "key_leaf2" : "container2_value1",
                "inner_element" : {
                  "leaf1" : "value5",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1",
                      "leaf2" : "value6"
                    }
                  ]
                }
              },
              {
                "key_leaf2" : "container2_value2",
                "inner_element" : {
                  "leaf1" : "value7",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1",
                      "leaf2" : "value8"
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
  constexpr char kRhsJson[] = R"({
    "outer_element": {
      "container1" : [
        {
          "key_leaf1" : "container1_value2",
          "middle_element" : {
            "container2" : [
              {
                "key_leaf2" : "container2_value2",
                "inner_element" : {
                  "leaf1" : "value7",
                  "container3" : [
                    {
                      "leaf2" : "value8",
                      "key_leaf3" : "container3_value1"
                    }
                  ]
                }
              },
              {
                "key_leaf2" : "container2_value1",
                "inner_element" : {
                  "leaf1" : "value5",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1",
                      "leaf2" : "value6"
                    }
                  ]
                }
              }
            ]
          }
        },
        {
          "key_leaf1" : "container1_value1",
          "middle_element" : {
            "container2" : [
              {
                "key_leaf2" : "container2_value1",
                "inner_element" : {
                  "leaf1" : "value1",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1",
                      "rhs_leaf2" : "rhs_value2"
                    }
                  ]
                }
              },
              {
                "key_leaf2" : "container2_value2",
                "inner_element" : {
                  "leaf1" : "value3",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1",
                      "leaf2" : "value4"
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
  ASSERT_OK_AND_ASSIGN(nlohmann::json lhs, ParseJson(kLhsJson));
  ASSERT_OK_AND_ASSIGN(nlohmann::json rhs, ParseJson(kRhsJson));

  std::vector<std::string> differences;
  ASSERT_OK_AND_ASSIGN(bool is_equal,
                       AreJsonEqual(lhs, rhs, *kPathKeyNameMap, differences));
  EXPECT_FALSE(is_equal);
  EXPECT_THAT(differences,
              testing::UnorderedElementsAre(testing::HasSubstr(
                  "Missing lhs: "
                  "[/outer_element/container1[key_leaf1='container1_value1']/"
                  "middle_element/container2[key_leaf2='container2_value1']/"
                  "inner_element/container3[key_leaf3='container3_value1']/"
                  "rhs_leaf2] with value 'rhs_value2'")));
}

TEST(AreJsonEqual, TestNotEqualMissingRhs) {
  constexpr char kLhsJson[] = R"({
    "outer_element": {
      "container1" : [
        {
          "key_leaf1" : "container1_value1",
          "middle_element" : {
            "container2" : [
              {
                "key_leaf2" : "container2_value1",
                "inner_element" : {
                  "leaf1" : "value1",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1",
                      "lhs_leaf2" : "lhs_value2"
                    }
                  ]
                }
              },
              {
                "key_leaf2" : "container2_value2",
                "inner_element" : {
                  "leaf1" : "value3",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1",
                      "leaf2" : "value4"
                    }
                  ]
                }
              }
            ]
          }
        },
        {
          "key_leaf1" : "container1_value2",
          "middle_element" : {
            "container2" : [
              {
                "key_leaf2" : "container2_value1",
                "inner_element" : {
                  "leaf1" : "value5",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1",
                      "leaf2" : "value6"
                    }
                  ]
                }
              },
              {
                "key_leaf2" : "container2_value2",
                "inner_element" : {
                  "leaf1" : "value7",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1",
                      "leaf2" : "value8"
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
  constexpr char kRhsJson[] = R"({
    "outer_element": {
      "container1" : [
        {
          "key_leaf1" : "container1_value2",
          "middle_element" : {
            "container2" : [
              {
                "key_leaf2" : "container2_value2",
                "inner_element" : {
                  "leaf1" : "value7",
                  "container3" : [
                    {
                      "leaf2" : "value8",
                      "key_leaf3" : "container3_value1"
                    }
                  ]
                }
              },
              {
                "key_leaf2" : "container2_value1",
                "inner_element" : {
                  "leaf1" : "value5",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1",
                      "leaf2" : "value6"
                    }
                  ]
                }
              }
            ]
          }
        },
        {
          "key_leaf1" : "container1_value1",
          "middle_element" : {
            "container2" : [
              {
                "key_leaf2" : "container2_value1",
                "inner_element" : {
                  "leaf1" : "value1",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1"
                    }
                  ]
                }
              },
              {
                "key_leaf2" : "container2_value2",
                "inner_element" : {
                  "leaf1" : "value3",
                  "container3" : [
                    {
                      "key_leaf3" : "container3_value1",
                      "leaf2" : "value4"
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
  ASSERT_OK_AND_ASSIGN(nlohmann::json lhs, ParseJson(kLhsJson));
  ASSERT_OK_AND_ASSIGN(nlohmann::json rhs, ParseJson(kRhsJson));

  std::vector<std::string> differences;
  ASSERT_OK_AND_ASSIGN(bool is_equal,
                       AreJsonEqual(lhs, rhs, *kPathKeyNameMap, differences));
  EXPECT_FALSE(is_equal);
  EXPECT_THAT(differences,
              testing::UnorderedElementsAre(testing::HasSubstr(
                  "Missing rhs: "
                  "[/outer_element/container1[key_leaf1='container1_value1']/"
                  "middle_element/container2[key_leaf2='container2_value1']/"
                  "inner_element/container3[key_leaf3='container3_value1']/"
                  "lhs_leaf2] with value 'lhs_value2'.")));
}

TEST(GetSimpleJsonValue, TestGetSimpleJsonValue) {
  constexpr absl::string_view kJsonStr = R"JSON({
   "outer_element" : {
      "container1" : {
        "name": "key1"
      },
      "container2" : {
        "inner_container2" : {
          "bool" : true
        },
        "inner_containers" : {
          "inner_container" : [
            {
              "inner_array_element" : {
                "int" : 1234,
                "float" : 1234.56
              }
            }
          ]
        }
      }
   }
  })JSON";
  ASSERT_OK_AND_ASSIGN(nlohmann::json source, ParseJson(kJsonStr));

  EXPECT_THAT(
      GetSimpleJsonValueAsString(source["outer_element"]["container1"]["name"]),
      "key1");
  EXPECT_THAT(
      GetSimpleJsonValueAsString(
          source["outer_element"]["container2"]["inner_container2"]["bool"]),
      "true");
  EXPECT_THAT(GetSimpleJsonValueAsString(
                  source["outer_element"]["container2"]["inner_containers"]
                        ["inner_container"][0]["inner_array_element"]["int"]),
              "1234");
  EXPECT_THAT(GetSimpleJsonValueAsString(
                  source["outer_element"]["container2"]["inner_containers"]
                        ["inner_container"][0]["inner_array_element"]["float"]),
              "1234.56");
  EXPECT_THAT(
      GetSimpleJsonValueAsString(
          source["outer_element"]["inner_containers"]["inner_container"][0]),
      "");
}

TEST(IsJsonSubset, StringMapsMatch) {
  const auto source_map = StringMap{
      {"/outer_element/container1[key_leaf1='value1']/key_leaf1", "value1"},
      {"/outer_element/container1[key_leaf1='value1']/middle_element/"
       "container2[key_leaf2='value2']/key_leaf2",
       "value2"},
      {"/outer_element/container1[key_leaf1='value1']/middle_element/"
       "container2[key_leaf2='value2']/inner_element/inner_leaf",
       "inner_value"},
  };
  std::vector<std::string> differences;
  EXPECT_TRUE(IsJsonSubset(source_map, source_map, differences));
}

TEST(IsJsonSubset, StringMapsWithArray) {
  const auto source_map = StringMap{
      {"/outer_element/container1[key_leaf1='value1']/middle_element/"
       "container2[key_leaf2='value2']/inner_element/container7['2.7']",
       "2.7"},
      {"/outer_element/container1[key_leaf1='value1']/middle_element/"
       "container2[key_leaf2='value2']/inner_element/container4['-2']",
       "-2"},
      {"/outer_element/container1[key_leaf1='value1']/middle_element/"
       "container2[key_leaf2='value2']/inner_element/"
       "container5['true']",
       "true"},
      {"/outer_element/container1[key_leaf1='value1']/middle_element/"
       "container2[key_leaf2='value2']/inner_element/container3['2']",
       "2"},
      {"/outer_element/container1[key_leaf1='value1']/middle_element/"
       "container2[key_leaf2='value2']/inner_element/container7['9']",
       "9"},
      {"/outer_element/container1[key_leaf1='value1']/middle_element/"
       "container2[key_leaf2='value2']/inner_element/container3['0']",
       "0"},
      {"/outer_element/container1[key_leaf1='value1']/middle_element/"
       "container2[key_leaf2='value2']/inner_element/container6['b']",
       "b"},
      {"/outer_element/container1[key_leaf1='value1']/middle_element/"
       "container2[key_leaf2='value2']/inner_element/container6['a']",
       "a"},
      {"/outer_element/container1[key_leaf1='value1']/middle_element/"
       "container2[key_leaf2='value2']/inner_element/container3['1']",
       "1"},
      {"/outer_element/container1[key_leaf1='value1']/middle_element/"
       "container2[key_leaf2='value2']/inner_element/container4['0']",
       "0"},
      {"/outer_element/container1[key_leaf1='value1']/key_leaf1", "value1"},
      {"/outer_element/container1[key_leaf1='value1']/middle_element/"
       "container2[key_leaf2='value2']/inner_element/container4['-1']",
       "-1"},
      {"/outer_element/container1[key_leaf1='value1']/middle_element/"
       "container2[key_leaf2='value2']/key_leaf2",
       "value2"}};
  auto target_map = source_map;
  target_map.erase(
      "/outer_element/container1[key_leaf1='value1']/middle_element/"
      "container2[key_leaf2='value2']/inner_element/container7['2.7']");
  std::vector<std::string> differences;
  EXPECT_FALSE(IsJsonSubset(source_map, target_map, differences));
  EXPECT_TRUE(IsJsonSubset(target_map, source_map, differences));
}

}  // namespace

}  // namespace json_yang
