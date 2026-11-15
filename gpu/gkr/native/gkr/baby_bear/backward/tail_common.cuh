#pragma once

#include "gkr/backward/tail_common.cuh"
#include "ops/baby_bear/gkr_ops_helpers.cuh"

namespace airbender::gkr::backward {

using ::airbender::gkr::ops::run_round_update_single_thread;
using ::airbender::gkr::ops::run_round_update_with_inverses;

} // namespace airbender::gkr::backward
