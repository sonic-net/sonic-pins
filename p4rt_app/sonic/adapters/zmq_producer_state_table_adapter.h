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
#ifndef PINS_P4RT_APP_SONIC_ADAPTERS_ZMQ_PRODUCER_STATE_TABLE_ADAPTER_H_
#define PINS_P4RT_APP_SONIC_ADAPTERS_ZMQ_PRODUCER_STATE_TABLE_ADAPTER_H_

#include <memory>
#include <string>
#include <vector>

#include "swss/dbconnector.h"
#include "swss/rediscommand.h"
#include "swss/zmqclient.h"
#include "swss/zmqproducerstatetable.h"

namespace p4rt_app {
namespace sonic {

class ZmqProducerStateTableAdapter {
 public:
  explicit ZmqProducerStateTableAdapter(swss::DBConnector* db,
                                        const std::string& table_name,
                                        swss::ZmqClient& zmq_client);
  virtual ~ZmqProducerStateTableAdapter() = default;

  // Sends a batch (vector of key, op, field values) of messages.
  virtual void send(const std::vector<swss::KeyOpFieldsValuesTuple>& kcos);

  // Waits to receive a batch response, with the individual keys and responses
  // in the vector of tuples.
  virtual bool wait(
      std::string& db, std::string& table_name,
      std::vector<std::shared_ptr<swss::KeyOpFieldsValuesTuple>>& kcos);

 protected:
  // Test only constructor used to construct Mock & Fake classes.
  ZmqProducerStateTableAdapter() = default;

 private:
  std::unique_ptr<swss::ZmqProducerStateTable> producer_;
};

}  // namespace sonic
}  // namespace p4rt_app

#endif  // PINS_P4RT_APP_SONIC_ADAPTERS_ZMQ_PRODUCER_STATE_TABLE_ADAPTER_H_
