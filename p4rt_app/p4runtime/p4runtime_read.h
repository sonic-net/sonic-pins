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
#ifndef PINS_P4RT_APP_P4RUNTIME_P4RUNTIME_READ_H_
#define PINS_P4RT_APP_P4RUNTIME_P4RUNTIME_READ_H_

#include <string>

#include "absl/container/flat_hash_map.h"
#include "absl/status/statusor.h"
#include "boost/bimap.hpp"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/entity_keys.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4rt_app/p4runtime/queue_translator.h"
#include "p4rt_app/sonic/redis_connections.h"

namespace p4rt_app {

// Reads all table entries from the cache and return in batches (of batch_size).
// For each ACL entry we also fetch counter data from CounterDb.
// TODO: Encapsulate translation arguments.
absl::StatusOr<std::vector<p4::v1::ReadResponse>> ReadAllEntitiesInBatches(
    int batch_size, const p4::v1::ReadRequest &request,
    const pdpi::IrP4Info &ir_p4_info,
    const absl::flat_hash_map<pdpi::EntityKey, p4::v1::Entity> &entity_cache,
    bool translate_port_ids,
    const boost::bimap<std::string, std::string> &port_translation_map,
    QueueTranslator& cpu_queue_translator,
    QueueTranslator& front_panel_queue_translator,
    sonic::P4rtTable& p4rt_table);

} // namespace p4rt_app

#endif // PINS_P4RT_APP_P4RUNTIME_P4RUNTIME_READ_H_
