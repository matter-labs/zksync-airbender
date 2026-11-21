#pragma once

#include "gkr/baby_bear/backward/window/common.cuh"
#include "gkr/backward/window/window_abi.cuh"

namespace airbender::gkr::backward {

// The complete by-value launch descriptor, passed as a single
// `__grid_constant__` kernel parameter. Its Rust mirror is
// `src/backward/window/binding.rs`.
struct alignas(BWD_WINDOW_DESC_ALIGN) bwd_window_desc {
  bwd_source_window slot[BWD_WINDOW_ADDR_SLOTS];
  // Production factored-eq low table; high tables stay in `ab_gkr_eq_high`.
  const e4 *eq_low;
  // Row-tile-major 27-cell partial tensor.
  e4 *partials;
  u32 log_rows;
  gkr_eq_sizes eq_sizes;
  // Cumulative instruction endpoints.
  u32 sections[BWD_WINDOW_SECTION_WORDS];
  u16 program[BWD_WINDOW_PROGRAM_WORD_CAP];
  u32 immediates[BWD_WINDOW_MAX_IMMEDIATES];
};

static_assert(sizeof(bwd_window_desc) == 21552, "bwd_window_desc/WindowLaunchBinding ABI size drift");
static_assert(alignof(bwd_window_desc) == BWD_WINDOW_DESC_ALIGN, "bwd_window_desc ABI alignment drift");
static_assert(sizeof(bwd_window_desc) + sizeof(u32) <= BWD_WINDOW_DESC_CAP, "bwd_window_desc exceeds the __grid_constant__ parameter budget");
static_assert(__builtin_offsetof(bwd_window_desc, slot) == 0, "slot ABI offset drift");
static_assert(__builtin_offsetof(bwd_window_desc, eq_low) == 1024, "eq_low ABI offset drift");
static_assert(__builtin_offsetof(bwd_window_desc, partials) == 1032, "partials ABI offset drift");
static_assert(__builtin_offsetof(bwd_window_desc, log_rows) == 1040, "log_rows ABI offset drift");
static_assert(__builtin_offsetof(bwd_window_desc, eq_sizes) == 1044, "eq_sizes ABI offset drift");
static_assert(__builtin_offsetof(bwd_window_desc, sections) == 1056, "sections ABI offset drift");
static_assert(__builtin_offsetof(bwd_window_desc, program) == 1072, "program ABI offset drift");
static_assert(__builtin_offsetof(bwd_window_desc, immediates) == 19504, "immediates ABI offset drift");

} // namespace airbender::gkr::backward
