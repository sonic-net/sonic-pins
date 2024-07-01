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
#ifndef PINS_P4RT_APP_UTILS_AUTHZ_LOGGER_H_
#define PINS_P4RT_APP_UTILS_AUTHZ_LOGGER_H_

#include <memory>
#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "grpcpp/security/audit_logging.h"
#include "p4rt_app/utils/metric_recorder.h"

// This file defines the AuthzLogger class and the AuthzAuditLoggerFactory
// class. These two classes are required in the gRPC authz audit logging API.
// The implementation is simply a wrapper of the MetricRecorder class.
namespace p4rt_app {

class AuthzLogger : public grpc::experimental::AuditLogger {
 public:
  AuthzLogger(p4rt_app::MetricRecorder* recorder) : recorder_(recorder) {}

  absl::string_view name() const override { return "authz_logger"; }

  void Log(const grpc::experimental::AuditContext& context) override;

 private:
  // Metric recorder to log the authz auditing logs.
  // Does not take any ownership, and pointer must refer to valid object that
  // outlive the one constructed.
  p4rt_app::MetricRecorder* recorder_;
};

class AuthzAuditLoggerFactory : public grpc::experimental::AuditLoggerFactory {
 public:
  class AuthzConfig : public Config {
   public:
    absl::string_view name() const override { return "authz_logger"; }
    std::string ToString() const override { return "authz_config"; }
  };

  AuthzAuditLoggerFactory(p4rt_app::MetricRecorder* recorder)
      : recorder_(recorder) {}

  absl::string_view name() const override { return "authz_logger"; }

  std::unique_ptr<grpc::experimental::AuditLogger> CreateAuditLogger(
      std::unique_ptr<AuditLoggerFactory::Config>) override {
    return std::make_unique<AuthzLogger>(recorder_);
  }

  absl::StatusOr<std::unique_ptr<Config>> ParseAuditLoggerConfig(
      const grpc_core::experimental::Json&) override {
    return std::make_unique<AuthzConfig>();
  }

 private:
  // Metric recorder to log the authz auditing logs.
  // Does not take any ownership, and pointer must refer to valid object that
  // outlive the one constructed.
  p4rt_app::MetricRecorder* recorder_;
};

}  // namespace p4rt_app

#endif  // PINS_P4RT_APP_UTILS_AUTHZ_LOGGER_H_
