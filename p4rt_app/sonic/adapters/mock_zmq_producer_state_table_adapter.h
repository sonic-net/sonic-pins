#ifndef PINS_P4RT_APP_SONIC_ADAPTERS_MOCK_ZMQ_PRODUCER_STATE_TABLE_ADAPTER_H_
#define PINS_P4RT_APP_SONIC_ADAPTERS_MOCK_ZMQ_PRODUCER_STATE_TABLE_ADAPTER_H_

#include <memory>
#include <string>
#include <vector>

#include "gmock/gmock.h"
#include "p4rt_app/sonic/adapters/zmq_producer_state_table_adapter.h"
#include "swss/table.h"

namespace p4rt_app {
namespace sonic {

class MockZmqProducerStateTableAdapter final
    : public ZmqProducerStateTableAdapter {
 public:
  MOCK_METHOD(void, send,
              (const std::vector<swss::KeyOpFieldsValuesTuple>& kcos),
              (override));

  MOCK_METHOD(
      bool, wait,
      (std::string & db, std::string& table_name,
       std::vector<std::shared_ptr<swss::KeyOpFieldsValuesTuple>>& kcos),
      (override));
};

}  // namespace sonic
}  // namespace p4rt_app

#endif  // PINS_P4RT_APP_SONIC_ADAPTERS_MOCK_ZMQ_PRODUCER_STATE_TABLE_ADAPTER_H_
