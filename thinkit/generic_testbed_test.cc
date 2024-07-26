#include "thinkit/generic_testbed.h"

#include <sstream>

#include "gmock/gmock.h"
#include "gtest/gtest.h"

namespace thinkit {
namespace {

TEST(HttpResponse, StreamInsertionOperatorWorks) {
  std::stringstream ss;
  ss << HttpResponse{.response_code = 400, .response = "Bad Request"};
  EXPECT_EQ(ss.str(), "400: Bad Request");
}

}  // namespace
}  // namespace thinkit
