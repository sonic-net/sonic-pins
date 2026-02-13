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

#include "tests/integration/system/nsf/compare_p4flows.h"

#include <cstdint>
#include <memory>
#include <string>
#include <vector>

#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "google/protobuf/message_lite.h"
#include "google/protobuf/util/message_differencer.h"
#include "gutil/status.h"
#include "p4/v1/p4runtime.pb.h"

namespace pins_test {
namespace {

using ::google::protobuf::util::MessageDifferencer;
using ::p4::v1::ReadResponse;

// Fields in P4 snapshot which needs to be ignored during comparison.
void AppendIgnoredP4SnapshotFields(MessageDifferencer *differencer) {
  if (differencer == nullptr)
    return;
  const google::protobuf::Descriptor &descriptor =
      *p4::v1::TableEntry().GetDescriptor();
  // Ignore counter_data and meter_counter_data fields in all table entries.
  differencer->IgnoreField(descriptor.FindFieldByName("counter_data"));
  differencer->IgnoreField(descriptor.FindFieldByName("meter_counter_data"));
  differencer->set_report_ignores(false);
  differencer->set_report_moves(false);
  differencer->set_repeated_field_comparison(MessageDifferencer::AS_SET);
}

} // namespace

absl::Status CompareP4FlowSnapshots(const ReadResponse &snapshot_before_nsf,
                                    const ReadResponse &snapshot_after_nsf) {
  MessageDifferencer differencer;
  std::string diff_report;
  AppendIgnoredP4SnapshotFields(&differencer);
  differencer.ReportDifferencesToString(&diff_report);

  if (!differencer.Compare(snapshot_before_nsf, snapshot_after_nsf)) {
    return gutil::InternalErrorBuilder()
           << "Differences found between the P4 flow snapshots:\n"
           << diff_report;
  }
  return absl::OkStatus();
}

} // namespace pins_test
