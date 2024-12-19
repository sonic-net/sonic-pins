// Copyright 2024 Google LLC
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
#ifndef PINS_P4RT_APP_UTILS_EVENT_DATA_TRACKER_H_
#define PINS_P4RT_APP_UTILS_EVENT_DATA_TRACKER_H_

#include <mutex> // NOLINT
#include <optional>
#include <utility>

namespace p4rt_app {

// TODO: move into sonic-swss-common if others have a need.
//
//  Thread safe container for accumulating data. Note the data type must support
//  the '+' operator.
template <typename T> class EventDataTracker {
public:
  explicit EventDataTracker(T default_value)
      : default_value_(std::move(default_value)), data_(default_value_) {}

  void Increment(const T &value) {
    std::lock_guard<std::mutex> lock(l_);
    if (!min_value_seen_.has_value() || value < *min_value_seen_) {
      min_value_seen_ = value;
    }
    if (!max_value_seen_.has_value() || value > *max_value_seen_) {
      max_value_seen_ = value;
    }
    data_ += value;
  }

  EventDataTracker<T> &operator+=(const T &value) {
    this->Increment(value);
    return *this;
  }

  T ReadData() const {
    std::lock_guard<std::mutex> lock(l_);
    return data_;
  }

  std::optional<T> ReadMinValue() const {
    std::lock_guard<std::mutex> lock(l_);
    return min_value_seen_;
  }

  std::optional<T> ReadMaxValue() const {
    std::lock_guard<std::mutex> lock(l_);
    return max_value_seen_;
  }

  T ReadDataAndReset() {
    std::lock_guard<std::mutex> lock(l_);

    T tmp = data_;
    data_ = default_value_;
    min_value_seen_.reset();
    max_value_seen_.reset();
    return tmp;
  }

private:
  mutable std::mutex l_;

  T default_value_;
  T data_;
  std::optional<T> min_value_seen_;
  std::optional<T> max_value_seen_;
};

} // namespace p4rt_app

#endif // PINS_P4RT_APP_UTILS_EVENT_DATA_TRACKER_H_
