// Copyright 2021 Google LLC
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

#ifndef PINS_GUTIL_GUTIL_STATUS_H_
#define PINS_GUTIL_GUTIL_STATUS_H_

#include <iostream>
#include <sstream>
#include <string>
#include <utility>

#include "absl/base/attributes.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/cord.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/types/optional.h"
#include "grpcpp/grpcpp.h"

namespace gutil {

// Converts `status` to a readable string. The current absl `ToString` method is
// not stable, which causes issues while golden testing. This function is
// stable.
std::string StableStatusToString(const absl::Status& status);

// Protobuf and some other Google projects use Status classes that are isomorph,
// but not equal to absl::Status (outside of google3).
// This auxiliary function converts such Status classes to absl::Status.
template <typename T>
absl::Status ToAbslStatus(T status) {
  return absl::Status(
      static_cast<absl::StatusCode>(status.code()),
      absl::string_view(status.message().data(), status.message().size()));
}

// A proxy type and function for template type deduction for logging
// `absl::StatusOr`s.
//
// Can be removed once `absl::StatusOr` supports `operator<<`.
template <class T>
class StreamableStatusOrProxy {
 public:
  explicit StreamableStatusOrProxy(const absl::StatusOr<T>& status_or)
      : status_or_(status_or) {}

  StreamableStatusOrProxy(const StreamableStatusOrProxy&) = delete;
  StreamableStatusOrProxy& operator=(const StreamableStatusOrProxy&) = delete;

  friend std::ostream& operator<<(std::ostream& os,
                                  const StreamableStatusOrProxy& logger) {
    if (logger.status_or_.ok()) return os << *logger.status_or_;
    return os << logger.status_or_.status().code() << ": "
              << logger.status_or_.status().message();
  }

 private:
  const absl::StatusOr<T>& status_or_;
};

template <class T>
StreamableStatusOrProxy<T> StreamableStatusOr(
    const absl::StatusOr<T>& status_or) {
  return StreamableStatusOrProxy<T>(status_or);
}

// Convert between gRPC and Abseil statuses.
grpc::Status AbslStatusToGrpcStatus(const absl::Status& status);
absl::Status GrpcStatusToAbslStatus(const grpc::Status& status);

// StatusBuilder facilitates easier construction of Status objects with streamed
// message building.
//
// Example usage:
//   absl::Status foo(int i) {
//     if (i < 0) {
//       return StatusBuilder(absl::StatusCode::kInvalidArgument) << "i=" << i;
//     }
//   }
class ABSL_MUST_USE_RESULT StatusBuilder {
 public:
  StatusBuilder(std::string file, int line, absl::StatusCode code)
      : status_(absl::Status(code, "")),
        log_error_(false),
        join_style_(MessageJoinStyle::kAnnotate) {
    source_ = absl::StrCat("[", file, ":", line, "]: ");
  }

  explicit StatusBuilder(absl::StatusCode code)
      : status_(absl::Status(code, "")),
        log_error_(false),
        join_style_(MessageJoinStyle::kAnnotate) {}

  explicit StatusBuilder(absl::Status status)
      : status_(status),
        log_error_(false),
        join_style_(MessageJoinStyle::kAnnotate) {}

  StatusBuilder(const StatusBuilder& other)
      : source_(other.source_),
        status_(other.status_),
        log_error_(other.log_error_),
        join_style_(other.join_style_) {
    stream_ << other.stream_.str();
  }

  // Streaming to the StatusBuilder appends to the error message.
  template <typename t>
  ABSL_MUST_USE_RESULT StatusBuilder& operator<<(t val) {
    stream_ << val;
    return *this;
  }

  // Makes the StatusBuilder print the error message (with source) when
  // converting to a different type.
  ABSL_MUST_USE_RESULT StatusBuilder& LogError() {
    log_error_ = true;
    return *this;
  }

  // The additional message is prepended to the pre-existing status error
  // message. No separator is placed between the messages.
  ABSL_MUST_USE_RESULT StatusBuilder& SetPrepend() {
    join_style_ = MessageJoinStyle::kPrepend;
    return *this;
  }

  // The additional message is appended to the pre-existing status error
  // message. No separator is placed between the messages.
  ABSL_MUST_USE_RESULT StatusBuilder& SetAppend() {
    join_style_ = MessageJoinStyle::kAppend;
    return *this;
  }

  // Override the StatusCode in status_ to the given value.
  ABSL_MUST_USE_RESULT StatusBuilder& SetCode(absl::StatusCode code) {
    status_ = absl::Status(code, status_.message());
    return *this;
  }

  ABSL_MUST_USE_RESULT StatusBuilder& SetPayload(absl::string_view url,
                                                 absl::Cord payload) {
    status_.SetPayload(url, std::move(payload));
    return *this;
  }

  // Implicit type conversions.
  operator absl::Status() const { return GetStatusAndLog(); }
  template <typename T>
  operator absl::StatusOr<T>() const {
    return absl::StatusOr<T>(static_cast<absl::Status>(*this));
  }

 private:
  enum class MessageJoinStyle {
    kAnnotate,
    kAppend,
    kPrepend,
  };

  std::string source_;
  absl::Status status_;
  std::stringstream stream_;
  bool log_error_;
  MessageJoinStyle join_style_;

  absl::Status GetStatusAndLog() const;
};

// Custom allocators for default StatusCodes.
class ABSL_MUST_USE_RESULT CancelledErrorBuilder : public StatusBuilder {
 public:
  CancelledErrorBuilder() : StatusBuilder(absl::StatusCode::kCancelled) {}
};
class ABSL_MUST_USE_RESULT UnknownErrorBuilder : public StatusBuilder {
 public:
  UnknownErrorBuilder() : StatusBuilder(absl::StatusCode::kUnknown) {}
};
class ABSL_MUST_USE_RESULT InvalidArgumentErrorBuilder : public StatusBuilder {
 public:
  InvalidArgumentErrorBuilder()
      : StatusBuilder(absl::StatusCode::kInvalidArgument) {}
};
class ABSL_MUST_USE_RESULT DeadlineExceededErrorBuilder : public StatusBuilder {
 public:
  DeadlineExceededErrorBuilder()
      : StatusBuilder(absl::StatusCode::kDeadlineExceeded) {}
};
class ABSL_MUST_USE_RESULT NotFoundErrorBuilder : public StatusBuilder {
 public:
  NotFoundErrorBuilder() : StatusBuilder(absl::StatusCode::kNotFound) {}
};
class ABSL_MUST_USE_RESULT AlreadyExistsErrorBuilder : public StatusBuilder {
 public:
  AlreadyExistsErrorBuilder()
      : StatusBuilder(absl::StatusCode::kAlreadyExists) {}
};
class ABSL_MUST_USE_RESULT PermissionDeniedErrorBuilder : public StatusBuilder {
 public:
  PermissionDeniedErrorBuilder()
      : StatusBuilder(absl::StatusCode::kPermissionDenied) {}
};
class ABSL_MUST_USE_RESULT ResourceExhaustedErrorBuilder
    : public StatusBuilder {
 public:
  ResourceExhaustedErrorBuilder()
      : StatusBuilder(absl::StatusCode::kResourceExhausted) {}
};
class ABSL_MUST_USE_RESULT FailedPreconditionErrorBuilder
    : public StatusBuilder {
 public:
  FailedPreconditionErrorBuilder()
      : StatusBuilder(absl::StatusCode::kFailedPrecondition) {}
};
class ABSL_MUST_USE_RESULT AbortedErrorBuilder : public StatusBuilder {
 public:
  AbortedErrorBuilder() : StatusBuilder(absl::StatusCode::kAborted) {}
};
class ABSL_MUST_USE_RESULT OutOfRangeErrorBuilder : public StatusBuilder {
 public:
  OutOfRangeErrorBuilder() : StatusBuilder(absl::StatusCode::kOutOfRange) {}
};
class ABSL_MUST_USE_RESULT UnimplementedErrorBuilder : public StatusBuilder {
 public:
  UnimplementedErrorBuilder()
      : StatusBuilder(absl::StatusCode::kUnimplemented) {}
};
class ABSL_MUST_USE_RESULT InternalErrorBuilder : public StatusBuilder {
 public:
  InternalErrorBuilder() : StatusBuilder(absl::StatusCode::kInternal) {}
};
class ABSL_MUST_USE_RESULT UnavailableErrorBuilder : public StatusBuilder {
 public:
  UnavailableErrorBuilder() : StatusBuilder(absl::StatusCode::kUnavailable) {}
};
class ABSL_MUST_USE_RESULT DataLossErrorBuilder : public StatusBuilder {
 public:
  DataLossErrorBuilder() : StatusBuilder(absl::StatusCode::kDataLoss) {}
};
class ABSL_MUST_USE_RESULT UnauthenticatedErrorBuilder : public StatusBuilder {
 public:
  UnauthenticatedErrorBuilder()
      : StatusBuilder(absl::StatusCode::kUnauthenticated) {}
};

// status.h internal classes. Not for public use.
namespace status_internal {
// Holds a status builder in the '_' parameter.
class StatusBuilderHolder {
 public:
  StatusBuilderHolder(const absl::Status& status) : builder_(status) {}
  StatusBuilderHolder(absl::Status&& status) : builder_(std::move(status)) {}

  StatusBuilder builder_;
};
}  // namespace status_internal

}  // namespace gutil

// RETURN_IF_ERROR evaluates an expression that returns a absl::Status. If the
// result is not ok, returns a StatusBuilder for the result. Otherwise,
// continues. Because the macro ends in an unterminated StatusBuilder, all
// StatusBuilder extensions can be used.
//
// Example:
//   absl::Status Foo() {...}
//   absl::Status Bar() {
//     RETURN_IF_ERROR(Foo()).LogError() << "Additional Info";
//     return absl::OkStatus()
//   }
#define RETURN_IF_ERROR(expr)                     \
  for (absl::Status status = expr; !status.ok();) \
  return gutil::StatusBuilder(std::move(status))

// These macros help create unique variable names for ASSIGN_OR_RETURN. Not for
// public use.
#define __ASSIGN_OR_RETURN_VAL_DIRECT(arg) __ASSIGN_OR_RETURN_RESULT_##arg
#define __ASSIGN_OR_RETURN_VAL(arg) __ASSIGN_OR_RETURN_VAL_DIRECT(arg)

// An implementation of ASSIGN_OR_RETURN that does not include a StatusBuilder.
// Not for public use.
#define __ASSIGN_OR_RETURN(dest, expr)                \
  auto __ASSIGN_OR_RETURN_VAL(__LINE__) = expr;       \
  if (!__ASSIGN_OR_RETURN_VAL(__LINE__).ok()) {       \
    return __ASSIGN_OR_RETURN_VAL(__LINE__).status(); \
  }                                                   \
  dest = std::move(__ASSIGN_OR_RETURN_VAL(__LINE__)).value()

// An implementation of ASSIGN_OR_RETURN that provides a StatusBuilder for extra
// processing. Not for public use.
#define __ASSIGN_OR_RETURN_STREAM(dest, expr, stream)     \
  auto __ASSIGN_OR_RETURN_VAL(__LINE__) = expr;           \
  if (!__ASSIGN_OR_RETURN_VAL(__LINE__).ok()) {           \
    return ::gutil::status_internal::StatusBuilderHolder( \
               __ASSIGN_OR_RETURN_VAL(__LINE__).status()) \
        .builder##stream;                                 \
  }                                                       \
  dest = std::move(__ASSIGN_OR_RETURN_VAL(__LINE__)).value()

// Macro to choose the correct implementation for ASSIGN_OR_RETURN based on
// the number of inputs. Not for public use.
#define __ASSIGN_OR_RETURN_PICK(dest, expr, stream, func, ...) func

// ASSIGN_OR_RETURN evaluates an expression that returns a StatusOr. If the
// result is ok, the value is saved to dest. Otherwise, the status is returned.
//
// Example:
//   absl::StatusOr<int> Foo() {...}
//   absl::Status Bar() {
//     ASSIGN_OR_RETURN(int value, Foo());
//     std::cout << "value: " << value;
//     return absl::OkStatus();
//   }
//
// ASSIGN_OR_RETURN optionally takes in a third parameter that takes in
// absl::StatusBuilder commands. Usage should assume a StatusBuilder object is
// available and referred to as '_'.
//
// Example:
//   absl::StatusOr<int> Foo() {...}
//   absl::Status Bar() {
//     ASSIGN_OR_RETURN(int value, Foo(), _.LogError() << "Additional Info");
//     std::cout << "value: " << value;
//     return absl::OkStatus();
//   }
#define ASSIGN_OR_RETURN(...)                                     \
  __ASSIGN_OR_RETURN_PICK(__VA_ARGS__, __ASSIGN_OR_RETURN_STREAM, \
                          __ASSIGN_OR_RETURN)                     \
  (__VA_ARGS__)

// Returns an error if `cond` doesn't hold.
#define RET_CHECK(cond) \
  while (!(cond))       \
  return gutil::InternalErrorBuilder() << "(" << #cond << ") failed"

#endif  // PINS_GUTIL_GUTIL_STATUS_H_
