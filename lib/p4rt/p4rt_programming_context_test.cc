// Copyright (c) 2024, Google Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "lib/p4rt/p4rt_programming_context.h"

#include <functional>

#include "absl/status/status.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto_matchers.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"

namespace pins_test {
namespace {

using ::gutil::EqualsProto;
using ::gutil::StatusIs;
using ::testing::_;
using ::testing::MockFunction;
using ::testing::Return;
using ::testing::Sequence;

static constexpr char kInsertVrfRequest[] =
    R"pb(updates {
           type: INSERT
           entity {
             table_entry {
               table_id: 33554506
               match {
                 field_id: 1
                 exact { value: "default-vrf" }
               }
               action { action { action_id: 24742814 } }
             }
           }
         })pb";

static constexpr char kDeleteVrfRequest[] =
    R"pb(updates {
           type: DELETE
           entity {
             table_entry {
               table_id: 33554506
               match {
                 field_id: 1
                 exact { value: "default-vrf" }
               }
               action { action { action_id: 24742814 } }
             }
           }
         })pb";

static constexpr char kInsertPreingressRequest[] = R"pb(
  updates {
    type: INSERT
    entity {
      table_entry {
        table_id: 33554689
        action {
          action {
            action_id: 16777472
            params { param_id: 1 value: "default-vrf" }
          }
        }
        priority: 1132
      }
    }
  }
)pb";

static constexpr char kDeletePreingressRequest[] = R"pb(
  updates {
    type: DELETE
    entity {
      table_entry {
        table_id: 33554689
        action {
          action {
            action_id: 16777472
            params { param_id: 1 value: "default-vrf" }
          }
        }
        priority: 1132
      }
    }
  }
)pb";

TEST(P4rtProgrammingContext, RevertsOnDestruction) {
  MockFunction<absl::Status(pdpi::P4RuntimeSession*, p4::v1::WriteRequest&)>
      mock_write_request;
  Sequence sequence;
  EXPECT_CALL(mock_write_request, Call(_, EqualsProto(kInsertVrfRequest)))
      .InSequence(sequence)
      .WillOnce(Return(absl::OkStatus()));

  EXPECT_CALL(mock_write_request,
              Call(_, EqualsProto(kInsertPreingressRequest)))
      .InSequence(sequence)
      .WillOnce(Return(absl::OkStatus()));

  // Expect the deletes to be in reverse order.
  EXPECT_CALL(mock_write_request,
              Call(_, EqualsProto(kDeletePreingressRequest)))
      .InSequence(sequence)
      .WillOnce(Return(absl::OkStatus()));

  EXPECT_CALL(mock_write_request, Call(_, EqualsProto(kDeleteVrfRequest)))
      .InSequence(sequence)
      .WillOnce(Return(absl::OkStatus()));

  P4rtProgrammingContext context(nullptr, mock_write_request.AsStdFunction());
  auto vrf_request =
      gutil::ParseProtoOrDie<p4::v1::WriteRequest>(kInsertVrfRequest);
  EXPECT_OK(context.SendWriteRequest(vrf_request));
  auto preingress_request =
      gutil::ParseProtoOrDie<p4::v1::WriteRequest>(kInsertPreingressRequest);
  EXPECT_OK(context.SendWriteRequest(preingress_request));
}

TEST(P4rtProgrammingContext, MoveDoesntBreakRevertsOnDestruction) {
  MockFunction<absl::Status(pdpi::P4RuntimeSession*, p4::v1::WriteRequest&)>
      mock_write_request;
  Sequence sequence;
  EXPECT_CALL(mock_write_request, Call(_, EqualsProto(kInsertVrfRequest)))
      .InSequence(sequence)
      .WillOnce(Return(absl::OkStatus()));

  EXPECT_CALL(mock_write_request,
              Call(_, EqualsProto(kInsertPreingressRequest)))
      .InSequence(sequence)
      .WillOnce(Return(absl::OkStatus()));

  // Expect the deletes to be in reverse order.
  EXPECT_CALL(mock_write_request,
              Call(_, EqualsProto(kDeletePreingressRequest)))
      .InSequence(sequence)
      .WillOnce(Return(absl::OkStatus()));

  EXPECT_CALL(mock_write_request, Call(_, EqualsProto(kDeleteVrfRequest)))
      .InSequence(sequence)
      .WillOnce(Return(absl::OkStatus()));

  P4rtProgrammingContext context(nullptr, mock_write_request.AsStdFunction());
  auto vrf_request =
      gutil::ParseProtoOrDie<p4::v1::WriteRequest>(kInsertVrfRequest);
  EXPECT_OK(context.SendWriteRequest(vrf_request));
  auto preingress_request =
      gutil::ParseProtoOrDie<p4::v1::WriteRequest>(kInsertPreingressRequest);
  EXPECT_OK(context.SendWriteRequest(preingress_request));

  // Expect that moving the context does not cause any double reverts or
  // anything similar.
  P4rtProgrammingContext new_context(std::move(context));
  P4rtProgrammingContext newest_context = std::move(new_context);
}

TEST(P4rtProgrammingContext, WorksWithGetWriteRequestFunction) {
  MockFunction<absl::Status(pdpi::P4RuntimeSession*, p4::v1::WriteRequest&)>
      mock_write_request;

  Sequence sequence;
  EXPECT_CALL(mock_write_request, Call(_, EqualsProto(kInsertVrfRequest)))
      .InSequence(sequence)
      .WillOnce(Return(absl::OkStatus()));
  EXPECT_CALL(mock_write_request,
              Call(_, EqualsProto(kInsertPreingressRequest)))
      .InSequence(sequence)
      .WillOnce(Return(absl::OkStatus()));

  // Expect the deletes to be in reverse order.
  EXPECT_CALL(mock_write_request,
              Call(_, EqualsProto(kDeletePreingressRequest)))
      .InSequence(sequence)
      .WillOnce(Return(absl::OkStatus()));
  EXPECT_CALL(mock_write_request, Call(_, EqualsProto(kDeleteVrfRequest)))
      .InSequence(sequence)
      .WillOnce(Return(absl::OkStatus()));

  P4rtProgrammingContext context(nullptr, mock_write_request.AsStdFunction());
  auto write_request = context.GetWriteRequestFunction();
  auto vrf_request =
      gutil::ParseProtoOrDie<p4::v1::WriteRequest>(kInsertVrfRequest);
  auto preingress_request =
      gutil::ParseProtoOrDie<p4::v1::WriteRequest>(kInsertPreingressRequest);

  EXPECT_OK(write_request(vrf_request));
  EXPECT_OK(write_request(preingress_request));
}

TEST(P4rtProgrammingContext, RevertsOnRevertCall) {
  MockFunction<absl::Status(pdpi::P4RuntimeSession*, p4::v1::WriteRequest&)>
      mock_write_request;

  Sequence sequence;
  EXPECT_CALL(mock_write_request,
              Call(_, EqualsProto(kDeletePreingressRequest)))
      .InSequence(sequence)
      .WillOnce(Return(absl::OkStatus()));
  EXPECT_CALL(mock_write_request, Call(_, EqualsProto(kDeleteVrfRequest)))
      .InSequence(sequence)
      .WillOnce(Return(absl::OkStatus()));

  // Expect the inserts to be in reverse order.
  EXPECT_CALL(mock_write_request, Call(_, EqualsProto(kInsertVrfRequest)))
      .InSequence(sequence)
      .WillOnce(Return(absl::OkStatus()));
  EXPECT_CALL(mock_write_request,
              Call(_, EqualsProto(kInsertPreingressRequest)))
      .InSequence(sequence)
      .WillOnce(Return(absl::OkStatus()));

  // Reprogram a table entry to ensure that Revert actually reverted the initial
  // entries and not the destructor (if Revert is a no-op, then the order of
  // reverts would differ).
  EXPECT_CALL(mock_write_request, Call(_, EqualsProto(kDeleteVrfRequest)))
      .InSequence(sequence)
      .WillOnce(Return(absl::OkStatus()));
  EXPECT_CALL(mock_write_request, Call(_, EqualsProto(kInsertVrfRequest)))
      .InSequence(sequence)
      .WillOnce(Return(absl::OkStatus()));

  P4rtProgrammingContext context(nullptr, mock_write_request.AsStdFunction());

  auto preingress_request =
      gutil::ParseProtoOrDie<p4::v1::WriteRequest>(kDeletePreingressRequest);
  auto vrf_request =
      gutil::ParseProtoOrDie<p4::v1::WriteRequest>(kDeleteVrfRequest);

  EXPECT_OK(context.SendWriteRequest(preingress_request));
  EXPECT_OK(context.SendWriteRequest(vrf_request));
  EXPECT_OK(context.Revert());

  // This should be reverted by the destructor.
  EXPECT_OK(context.SendWriteRequest(vrf_request));
}

// This test case covers that when one of the revert requests fails, that
// retrying the revert will continue where it left off.
TEST(P4rtProgrammingContext, RevertsOnRevertCallResumesOnFailure) {
  MockFunction<absl::Status(pdpi::P4RuntimeSession*, p4::v1::WriteRequest&)>
      mock_write_request;
  Sequence sequence;
  EXPECT_CALL(mock_write_request,
              Call(_, EqualsProto(kDeletePreingressRequest)))
      .InSequence(sequence)
      .WillOnce(Return(absl::OkStatus()));
  EXPECT_CALL(mock_write_request, Call(_, EqualsProto(kDeleteVrfRequest)))
      .InSequence(sequence)
      .WillOnce(Return(absl::OkStatus()));

  // Expect the inserts to be in reverse order. The first time, the insert will
  // fail. Then when we run Revert again, we should expect it to try the same
  // insert again, but it will succeed.
  EXPECT_CALL(mock_write_request, Call(_, EqualsProto(kInsertVrfRequest)))
      .InSequence(sequence)
      .WillOnce(Return(absl::UnknownError("Error")));
  EXPECT_CALL(mock_write_request, Call(_, EqualsProto(kInsertVrfRequest)))
      .InSequence(sequence)
      .WillOnce(Return(absl::OkStatus()));
  EXPECT_CALL(mock_write_request,
              Call(_, EqualsProto(kInsertPreingressRequest)))
      .InSequence(sequence)
      .WillOnce(Return(absl::OkStatus()));

  // Reprogram a table entry to ensure that Revert actually reverted the initial
  // entries and not the destructor (if Revert is a no-op, then the order of
  // reverts would differ).
  EXPECT_CALL(mock_write_request, Call(_, EqualsProto(kDeleteVrfRequest)))
      .InSequence(sequence)
      .WillOnce(Return(absl::OkStatus()));
  EXPECT_CALL(mock_write_request, Call(_, EqualsProto(kInsertVrfRequest)))
      .InSequence(sequence)
      .WillOnce(Return(absl::OkStatus()));

  P4rtProgrammingContext context(nullptr, mock_write_request.AsStdFunction());

  auto preingress_request =
      gutil::ParseProtoOrDie<p4::v1::WriteRequest>(kDeletePreingressRequest);
  auto vrf_request =
      gutil::ParseProtoOrDie<p4::v1::WriteRequest>(kDeleteVrfRequest);

  EXPECT_OK(context.SendWriteRequest(preingress_request));
  EXPECT_OK(context.SendWriteRequest(vrf_request));
  EXPECT_THAT(context.Revert(), StatusIs(absl::StatusCode::kUnknown));
  EXPECT_OK(context.Revert());

  // This should be reverted by the destructor.
  EXPECT_OK(context.SendWriteRequest(vrf_request));
}

TEST(P4rtProgrammingContext, RejectModifyRequests) {
  MockFunction<absl::Status(pdpi::P4RuntimeSession*, p4::v1::WriteRequest&)>
      mock_write_request;
  P4rtProgrammingContext context(nullptr, mock_write_request.AsStdFunction());

  auto request1 = gutil::ParseProtoOrDie<p4::v1::WriteRequest>(
      R"pb(
        updates {
          type: MODIFY
          entity {
            table_entry {
              table_id: 33554689
              action {
                action {
                  action_id: 16777472
                  params { param_id: 1 value: "default-vrf" }
                }
              }
              priority: 1132
            }
          }
        }
      )pb");
  EXPECT_THAT(context.SendWriteRequest(request1),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

}  // namespace
}  // namespace pins_test
