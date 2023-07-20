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
#include "p4rt_app/utils/lru_cache.h"

#include <string>

#include "gtest/gtest.h"

namespace p4rt_app {
namespace {

TEST(LruCacheTest, TestCapacity) {
  LruCache<std::string, std::string> cache(3);
  EXPECT_EQ(cache.capacity(), 3);
}

TEST(LruCacheTest, TestSize) {
  LruCache<std::string, std::string> cache(3);
  EXPECT_EQ(cache.size(), 0);
  cache["1"] = "one";
  EXPECT_EQ(cache.size(), 1);
  cache["2"] = "two";
  EXPECT_EQ(cache.size(), 2);
  cache["1"] = "three";
  EXPECT_EQ(cache.size(), 2);
}

TEST(LruCacheTest, TestInsert) {
  LruCache<std::string, std::string> cache(3);
  cache["1"] = "one";
  EXPECT_TRUE(cache.contains("1"));
  EXPECT_EQ(cache.at("1"), "one");
  cache["2"] = "two";
  EXPECT_TRUE(cache.contains("2"));
  EXPECT_EQ(cache.at("2"), "two");
  cache["3"] = "three";
  EXPECT_TRUE(cache.contains("3"));
  EXPECT_EQ(cache.at("3"), "three");
}

TEST(LruCacheTest, TestUpdate) {
  LruCache<std::string, std::string> cache(3);
  cache["1"] = "one";
  EXPECT_TRUE(cache.contains("1"));
  EXPECT_EQ(cache.at("1"), "one");
  cache["1"] = "two";
  EXPECT_TRUE(cache.contains("1"));
  EXPECT_EQ(cache.at("1"), "two");
  cache["1"] = "three";
  EXPECT_TRUE(cache.contains("1"));
  EXPECT_EQ(cache.at("1"), "three");
}

TEST(LruCacheTest, TestOverflow) {
  LruCache<std::string, std::string> cache(3);
  cache["1"] = "one";
  cache["2"] = "two";
  cache["3"] = "three";
  cache["4"] = "four";
  EXPECT_TRUE(cache.contains("4"));
  EXPECT_EQ(cache.at("4"), "four");
  EXPECT_EQ(cache.size(), 3);
  EXPECT_FALSE(cache.contains("1"));
  cache["2"] = "new_two";
  EXPECT_EQ(cache.at("2"), "new_two");
  cache["5"] = "five";
  EXPECT_TRUE(cache.contains("5"));
  EXPECT_EQ(cache.at("5"), "five");
  EXPECT_EQ(cache.size(), 3);
  EXPECT_FALSE(cache.contains("3"));
}

}  // namespace
}  // namespace p4rt_app
