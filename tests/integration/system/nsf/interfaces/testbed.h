#ifndef PINS_TESTS_INTEGRATION_SYSTEM_NSF_INTERFACES_TESTBED_H_
#define PINS_TESTS_INTEGRATION_SYSTEM_NSF_INTERFACES_TESTBED_H_

#include <memory>
#include <variant>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "gutil/overload.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/generic_testbed_fixture.h"
#include "thinkit/mirror_testbed.h"
#include "thinkit/mirror_testbed_fixture.h"

namespace pins_test {

using TestbedInterface =
    std::variant<std::unique_ptr<thinkit::GenericTestbedInterface>,
                 std::unique_ptr<thinkit::MirrorTestbedInterface>>;
using TestbedHolder = std::variant<std::unique_ptr<thinkit::GenericTestbed>,
                                   thinkit::MirrorTestbed *>;

// A wrapper class for both GenericTestbed and MirrorTestbed.
//
// This class is useful for providing a common interface for both GenericTestbed
// and MirrorTestbed, that becomes essential for providing common (or similar
// functionality) that supports both testbed types.
//
// library that provides this functionality.
//
// For example, the following code snippet shows how to use this class to
// provide a common interface for both testbed types.
//
//   class MyTestFixture {
//   protected:
//     ...
//
//     TestbedHolder testbed_;
//   };
//
//   ...
//
//   ASSERT_OK_AND_ASSIGN(testbed_, GetTestbed(testbed_interface_));
//
// Note: We assign the returned testbed to a TestbedHolder member variable
// because TestbedHolder takes ownership of the unique pointer of the
// GenericTestbed variant.
//
// Caution: Do NOT use Testbed as the type of testbed_ to store the returned
// testbed, as it would lead to a dangling pointer, since Testbed does not take
// ownership of the underlying GenericTestbed.
//
// However, we can directly assign the TestbedHolder to a Testbed variable.
// This is important so that the utility functions can support both the testbed
// types through Testbed (that does not takes ownership of the underlying
// GenericTestbed, if present) while still supporting implicit conversions from
// thinkit::GenericTestbed* and thinkit::MirrorTestbed* to Testbed, while the
// client code ensures that the GenericTestbed outlives the function call, if
// present.
//
//   ASSIGN_OR_RETURN(thinkit::GenericTestbed* generic_testbed,
//                    GetGenericTestbed(testbed_));
//   ASSIGN_OR_RETURN(thinkit::MirrorTestbed* mirror_testbed,
//                    GetMirrorTestbed(testbed_));
//
class Testbed
    : public std::variant<thinkit::GenericTestbed *, thinkit::MirrorTestbed *> {
public:
  using std::variant<thinkit::GenericTestbed *,
                     thinkit::MirrorTestbed *>::variant;

  Testbed(const TestbedHolder &testbed_holder)
      : std::variant<thinkit::GenericTestbed *, thinkit::MirrorTestbed *>(
            std::visit(
                gutil::Overload{
                    [](const std::unique_ptr<thinkit::GenericTestbed> &testbed)
                        -> Testbed { return testbed.get(); },
                    [](thinkit::MirrorTestbed *testbed) -> Testbed {
                      return testbed;
                    }},
                testbed_holder)) {}
};

inline absl::StatusOr<thinkit::GenericTestbed *>
GetGenericTestbed(const Testbed &testbed) {
  if (!std::holds_alternative<thinkit::GenericTestbed *>(testbed)) {
    return absl::InvalidArgumentError(
        "The given testbed is not a GenericTestbed.");
  }
  return std::get<thinkit::GenericTestbed *>(testbed);
}
inline absl::StatusOr<thinkit::MirrorTestbed *>
GetMirrorTestbed(const Testbed &testbed) {
  if (!std::holds_alternative<thinkit::MirrorTestbed *>(testbed)) {
    return absl::InvalidArgumentError(
        "The given testbed is not a MirrorTestbed.");
  }
  return std::get<thinkit::MirrorTestbed *>(testbed);
}

}  // namespace pins_test

#endif  // PINS_TESTS_INTEGRATION_SYSTEM_NSF_INTERFACES_TESTBED_H_
