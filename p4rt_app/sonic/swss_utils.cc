#include "p4rt_app/sonic/swss_utils.h"

#include <string>

#include "absl/container/flat_hash_map.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "gutil/status.h"
#include "swss/rediscommand.h"
#include "swss/table.h"

namespace p4rt_app {
namespace sonic {

bool kfvEq(const swss::KeyOpFieldsValuesTuple& left,
           const swss::KeyOpFieldsValuesTuple& right) {
  if (kfvKey(left) != kfvKey(right)) return false;
  if (kfvOp(left) != kfvOp(right)) return false;
  if (kfvFieldsValues(left).size() != kfvFieldsValues(right).size()) {
    return false;
  }

  absl::flat_hash_map<std::string, std::string> left_values;
  for (const auto& [field, value] : kfvFieldsValues(left)) {
    left_values[field] = value;
  }
  for (const auto& [field, value] : kfvFieldsValues(right)) {
    auto left_lookup = left_values.find(field);
    if (left_lookup == left_values.end()) return false;
    if (left_lookup->second != value) return false;
  }
  return true;
}

absl::StatusOr<std::string> kfvFieldLookup(
    const swss::KeyOpFieldsValuesTuple& kfv, absl::string_view field) {
  for (const auto& [kfv_field, value] : kfvFieldsValues(kfv)) {
    if (kfv_field == field) return value;
  }
  return gutil::NotFoundErrorBuilder()
         << "Tuple with key " << kfvKey(kfv)
         << " does not contain the field: " << field;
}

}  // namespace sonic
}  // namespace p4rt_app
