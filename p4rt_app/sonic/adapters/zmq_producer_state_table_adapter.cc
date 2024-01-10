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
#include "p4rt_app/sonic/adapters/zmq_producer_state_table_adapter.h"

#include <memory>
#include <string>
#include <vector>

#include "swss/dbconnector.h"
#include "swss/rediscommand.h"
#include "swss/zmqclient.h"
#include "swss/zmqproducerstatetable.h"

namespace p4rt_app {
namespace sonic {

ZmqProducerStateTableAdapter::ZmqProducerStateTableAdapter(
    swss::DBConnector* db, const std::string& table_name,
    swss::ZmqClient& zmq_client)
    : producer_(std::make_unique<swss::ZmqProducerStateTable>(db, table_name,
                                                              zmq_client)) {}

void ZmqProducerStateTableAdapter::send(
    const std::vector<swss::KeyOpFieldsValuesTuple>& kcos) {
  producer_->send(kcos);
}

bool ZmqProducerStateTableAdapter::wait(
    std::string& db, std::string& table_name,
    std::vector<std::shared_ptr<swss::KeyOpFieldsValuesTuple>>& kcos) {
  return producer_->wait(db, table_name, kcos);
}

}  // namespace sonic
}  // namespace p4rt_app
