#ifndef PINS_TESTS_INTEGRATION_SYSTEM_NSF_INTERFACES_TESTBED_H_
#define PINS_TESTS_INTEGRATION_SYSTEM_NSF_INTERFACES_TESTBED_H_

#include <memory>
#include <variant>

#include "thinkit/generic_testbed.h"
#include "thinkit/generic_testbed_fixture.h"
#include "thinkit/mirror_testbed.h"
#include "thinkit/mirror_testbed_fixture.h"

namespace pins_test {

using Testbed = std::variant<std::unique_ptr<thinkit::GenericTestbed>,
                             thinkit::MirrorTestbed*>;
using TestbedInterface =
    std::variant<std::unique_ptr<thinkit::GenericTestbedInterface>,
                 std::unique_ptr<thinkit::MirrorTestbedInterface>>;

}  // namespace pins_test

#endif  // PINS_TESTS_INTEGRATION_SYSTEM_NSF_INTERFACES_TESTBED_H_
