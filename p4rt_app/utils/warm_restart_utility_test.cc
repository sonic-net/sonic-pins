// Copyright 2025 Google LLC
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
#include "p4rt_app/utils/warm_restart_utility.h"

#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "absl/time/time.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "p4rt_app/sonic/adapters/fake_table_adapter.h"
#include "p4rt_app/sonic/adapters/fake_warm_boot_state_adapter.h"
#include "swss/warm_restart.h"

namespace p4rt_app {
namespace {

using ::testing::UnorderedElementsAreArray;

class WarmRestartUtilityTest : public ::testing::Test {
 public:
  WarmRestartUtilityTest()
      : port_table_("ConfigDb:PORT"),
        cpu_port_table_("ConfigDb:CPU_PORT"),
        port_channel_table_("ConfigDb:PORTCHANNEL"),
        cpu_queue_table_("ConfigDb:QUEUE_NAME_TO_ID_MAP"),
        node_cfg_table_("ConfigDb:NODE_CFG"),
        send_to_ingress_table_("ConfigDb:SEND_TO_INGRESS") {
    auto port_table_config_db =
        std::make_shared<sonic::FakeTableAdapter>(&port_table_, "PORT");
    auto cpu_port_table_config_db =
        std::make_shared<sonic::FakeTableAdapter>(&cpu_port_table_, "CPU_PORT");
    auto port_channel_table_config_db =
        std::make_shared<sonic::FakeTableAdapter>(&port_channel_table_,
                                                  "PORTCHANNEL");
    auto cpu_queue_table_config_db = std::make_unique<sonic::FakeTableAdapter>(
        &cpu_queue_table_, "QUEUE_NAME_TO_ID_MAP");
    auto node_cfg_table_config_db =
        std::make_unique<sonic::FakeTableAdapter>(&node_cfg_table_, "NODE_CFG");
    auto send_to_ingress_table_config_db =
        std::make_unique<sonic::FakeTableAdapter>(&send_to_ingress_table_,
                                                  "SEND_TO_INGRESS_PORT");
    auto warm_boot_state_adapter =
        std::make_unique<sonic::FakeWarmBootStateAdapter>();
    warm_boot_state_adapter_ = warm_boot_state_adapter.get();
    port_table_config_db_ = port_table_config_db.get();
    cpu_port_table_config_db_ = cpu_port_table_config_db.get();
    port_channel_table_config_db_ = port_channel_table_config_db.get();
    cpu_queue_config_db_ = cpu_queue_table_config_db.get();
    node_cfg_table_config_db_ = node_cfg_table_config_db.get();
    send_to_ingress_table_config_db_ = send_to_ingress_table_config_db.get();

    warm_restart_util_ = std::make_unique<WarmRestartUtil>(
        std::move(warm_boot_state_adapter), std::move(port_table_config_db),
        std::move(cpu_port_table_config_db),
        std::move(port_channel_table_config_db),
        std::move(cpu_queue_table_config_db),
        std::move(node_cfg_table_config_db),
        std::move(send_to_ingress_table_config_db));
  }

 protected:
  sonic::FakeSonicDbTable port_table_;
  sonic::FakeSonicDbTable cpu_port_table_;
  sonic::FakeSonicDbTable port_channel_table_;
  sonic::FakeSonicDbTable cpu_queue_table_;
  sonic::FakeSonicDbTable node_cfg_table_;
  sonic::FakeSonicDbTable send_to_ingress_table_;

  sonic::FakeWarmBootStateAdapter* warm_boot_state_adapter_;
  // CONFIG DB tables to query (key, port_id) pairs.
  sonic::FakeTableAdapter* port_table_config_db_;
  sonic::FakeTableAdapter* cpu_port_table_config_db_;
  sonic::FakeTableAdapter* port_channel_table_config_db_;
  sonic::FakeTableAdapter* node_cfg_table_config_db_;
  sonic::FakeTableAdapter* send_to_ingress_table_config_db_;
  // CONFIG DB table to query CPU queues.
  sonic::FakeTableAdapter* cpu_queue_config_db_;
  std::unique_ptr<WarmRestartUtil> warm_restart_util_;
};

TEST_F(WarmRestartUtilityTest, GetPortIdsFromConfigDb) {
  EXPECT_TRUE(warm_restart_util_->GetPortIdsFromConfigDb().empty());
  port_table_config_db_->batch_set(
      {{"Ethernet0", "SET", {{"alias", "fortyGigE0/0"}, {"id", "1"}}},
       {"Ethernet4", "SET", {{"alias", "fortyGigE0/4"}, {"id", "2"}}},
       {"Ethernet8", "SET", {{"alias", "fortyGigE0/8"}, {"id", "3"}}},
       {"Ethernet12", "SET", {{"alias", "fortyGigE0/12"}, {"id", "4"}}}});
  std::vector<std::pair<std::string, std::string>> expected_port_ids = {
      {"Ethernet0", "1"},
      {"Ethernet4", "2"},
      {"Ethernet8", "3"},
      {"Ethernet12", "4"}};
  EXPECT_THAT(warm_restart_util_->GetPortIdsFromConfigDb(),
              UnorderedElementsAreArray(expected_port_ids));

  cpu_port_table_config_db_->set("CPU", {{"id", "4294967293"}});
  port_channel_table_config_db_->batch_set({
      {"PortChannel101", "SET", {{"alias", "PortChannel101"}, {"id", "2149"}}},
      {"PortChannel102", "SET", {{"alias", "PortChannel102"}, {"id", "2150"}}},
  });
  expected_port_ids.push_back({"CPU", "4294967293"});
  expected_port_ids.push_back({"PortChannel101", "2149"});
  expected_port_ids.push_back({"PortChannel102", "2150"});
  EXPECT_THAT(warm_restart_util_->GetPortIdsFromConfigDb(),
              UnorderedElementsAreArray(expected_port_ids));
}

TEST_F(WarmRestartUtilityTest, GetCpuQueueIdsFromConfigDb) {
  EXPECT_TRUE(warm_restart_util_->GetCpuQueueIdsFromConfigDb().empty());
  cpu_queue_config_db_->batch_set({{"CPU",
                                    "SET",
                                    {{"CONTROLLER_PRIORITY_1", "32"},
                                     {"CONTROLLER_PRIORITY_2", "33"},
                                     {"CONTROLLER_PRIORITY_3", "34"},
                                     {"CONTROLLER_PRIORITY_4", "35"},
                                     {"CONTROLLER_PRIORITY_5", "36"},
                                     {"CONTROLLER_PRIORITY_6", "37"},
                                     {"CONTROLLER_PRIORITY_7", "38"},
                                     {"CONTROLLER_PRIORITY_8", "39"},
                                     {"INBAND_PRIORITY_1", "0"},
                                     {"INBAND_PRIORITY_2", "3"},
                                     {"INBAND_PRIORITY_3", "4"},
                                     {"INBAND_PRIORITY_4", "5"},
                                     {"INBAND_PRIORITY_5", "6"},
                                     {"INBAND_PRIORITY_6", "7"},
                                     {"INBAND_PRIORITY_7", "40"},
                                     {"INBAND_PRIORITY_8", "41"}}},
                                   {"FRONT_PANEL",
                                    "SET",
                                    {{"AF1", "3"},
                                     {"AF2", "4"},
                                     {"AF3", "5"},
                                     {"AF4", "6"},
                                     {"BE1", "2"},
                                     {"LLQ1", "0"},
                                     {"LLQ2", "1"},
                                     {"NC1", "7"}}}});
  std::vector<std::pair<std::string, std::string>> expected_cpu_queue_ids = {
      {"CONTROLLER_PRIORITY_1", "32"}, {"CONTROLLER_PRIORITY_2", "33"},
      {"CONTROLLER_PRIORITY_3", "34"}, {"CONTROLLER_PRIORITY_4", "35"},
      {"CONTROLLER_PRIORITY_5", "36"}, {"CONTROLLER_PRIORITY_6", "37"},
      {"CONTROLLER_PRIORITY_7", "38"}, {"CONTROLLER_PRIORITY_8", "39"},
      {"INBAND_PRIORITY_1", "0"},      {"INBAND_PRIORITY_2", "3"},
      {"INBAND_PRIORITY_3", "4"},      {"INBAND_PRIORITY_4", "5"},
      {"INBAND_PRIORITY_5", "6"},      {"INBAND_PRIORITY_6", "7"},
      {"INBAND_PRIORITY_7", "40"},     {"INBAND_PRIORITY_8", "41"}};
  EXPECT_THAT(warm_restart_util_->GetCpuQueueIdsFromConfigDb(),
              UnorderedElementsAreArray(expected_cpu_queue_ids));
}

TEST_F(WarmRestartUtilityTest, GetFrontPanelQueueIdsFromConfigDb) {
  EXPECT_TRUE(warm_restart_util_->GetFrontPanelQueueIdsFromConfigDb().empty());
  cpu_queue_config_db_->batch_set({{"FRONT_PANEL",
                                    "SET",
                                    {{"CONTROLLER_PRIORITY_1", "32"},
                                     {"CONTROLLER_PRIORITY_2", "33"},
                                     {"CONTROLLER_PRIORITY_3", "34"},
                                     {"CONTROLLER_PRIORITY_4", "35"},
                                     {"CONTROLLER_PRIORITY_5", "36"},
                                     {"CONTROLLER_PRIORITY_6", "37"},
                                     {"CONTROLLER_PRIORITY_7", "38"},
                                     {"CONTROLLER_PRIORITY_8", "39"},
                                     {"INBAND_PRIORITY_1", "0"},
                                     {"INBAND_PRIORITY_2", "3"},
                                     {"INBAND_PRIORITY_3", "4"},
                                     {"INBAND_PRIORITY_4", "5"},
                                     {"INBAND_PRIORITY_5", "6"},
                                     {"INBAND_PRIORITY_6", "7"},
                                     {"INBAND_PRIORITY_7", "40"},
                                     {"INBAND_PRIORITY_8", "41"}}},
                                   {"FRONT_PANEL",
                                    "SET",
                                    {{"AF1", "3"},
                                     {"AF2", "4"},
                                     {"AF3", "5"},
                                     {"AF4", "6"},
                                     {"BE1", "2"},
                                     {"LLQ1", "0"},
                                     {"LLQ2", "1"},
                                     {"NC1", "7"}}}});
  std::vector<std::pair<std::string, std::string>>
      expected_front_panel_queue_ids = {
          {"AF1", "3"}, {"AF2", "4"},  {"AF3", "5"},  {"AF4", "6"},
          {"BE1", "2"}, {"LLQ1", "0"}, {"LLQ2", "1"}, {"NC1", "7"}};
  EXPECT_THAT(warm_restart_util_->GetFrontPanelQueueIdsFromConfigDb(),
              UnorderedElementsAreArray(expected_front_panel_queue_ids));
}

TEST_F(WarmRestartUtilityTest, GetDeviceIdFromConfigDb) {
  EXPECT_FALSE(warm_restart_util_->GetDeviceIdFromConfigDb().has_value());
  node_cfg_table_config_db_->set("integrated_circuit0", {{"node-id", "1"}});
  EXPECT_TRUE(warm_restart_util_->GetDeviceIdFromConfigDb().has_value());
  EXPECT_EQ(warm_restart_util_->GetDeviceIdFromConfigDb().value(), 1);
}

TEST_F(WarmRestartUtilityTest, GetPortsFromConfigDb) {
  EXPECT_TRUE(warm_restart_util_->GetPortsFromConfigDb().empty());
  port_table_config_db_->batch_set(
      {{"Ethernet0", "SET", {{"alias", "fortyGigE0/0"}, {"id", "1"}}},
       {"Ethernet4", "SET", {{"alias", "fortyGigE0/4"}, {"id", "2"}}},
       {"Ethernet8", "SET", {{"alias", "fortyGigE0/8"}, {"id", "3"}}},
       {"Ethernet12", "SET", {{"alias", "fortyGigE0/12"}, {"id", "4"}}}});
  std::vector<std::string> expected_ports = {
      {"Ethernet0"}, {"Ethernet4"}, {"Ethernet8"}, {"Ethernet12"}};
  EXPECT_THAT(warm_restart_util_->GetPortsFromConfigDb(),
              UnorderedElementsAreArray(expected_ports));

  send_to_ingress_table_config_db_->set("SEND_TO_INGRESS",
                                        {{"value", {"NULL", "NULL"}}});
  expected_ports.push_back({"SEND_TO_INGRESS"});
  EXPECT_THAT(warm_restart_util_->GetPortsFromConfigDb(),
              UnorderedElementsAreArray(expected_ports));
}

}  // namespace
}  // namespace p4rt_app
