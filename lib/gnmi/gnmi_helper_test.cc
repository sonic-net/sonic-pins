#include "lib/gnmi/gnmi_helper.h"

#include "absl/strings/str_split.h"
#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/proto_matchers.h"
#include "gutil/status_matchers.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "proto/gnmi/gnmi.pb.h"

namespace pins_test {

namespace {
using gutil::EqualsProto;
}  // namespace

TEST(OCStringToPath, OCStringToPathTestCase1) {
  EXPECT_THAT(
      ConvertOCStringToPath("interfaces/interface[name=ethernet0]/config/mtu"),
      EqualsProto(R"pb(
        elem { name: "interfaces" }
        elem {
          name: "interface"
          key { key: "name" value: "ethernet0" }
        }
        elem { name: "config" }
        elem { name: "mtu" }
      )pb"));
}

TEST(OCStringToPath, OCStringToPathTestCase2) {
  EXPECT_THAT(
      ConvertOCStringToPath("components/component[name=1/1]/state/name"),
      EqualsProto(R"pb(
        elem { name: "components" }
        elem {
          name: "component"
          key { key: "name" value: "1/1" }
        }
        elem { name: "state" }
        elem { name: "name" }
      )pb"));
}

TEST(OCStringToPath, OCStringToPathTestCase3) {
  EXPECT_THAT(
      ConvertOCStringToPath(
          "interfaces/interface[name=ethernet0]/config/mtu/ic[name=1/1]/value"),
      EqualsProto(R"pb(
        elem { name: "interfaces" }
        elem {
          name: "interface"
          key { key: "name" value: "ethernet0" }
        }
        elem { name: "config" }
        elem { name: "mtu" }
        elem {
          name: "ic"
          key { key: "name" value: "1/1" }
        }
        elem { name: "value" }
      )pb"));
}

}  // namespace pins_test
