//! Launch microbenchmark for the DIT NTT engine (bench feature only).
//!
//! Drives the bench-gated DIT kernel variants exported by `gpu_ntt_native`
//! (`native/bench/dit_bench_kernels.cu`) plus the production two-pass STREAM
//! symbols, measuring pure launch + execution time across four kernel families
//! over a single fixed workload (`log_n + log_lde = 27`, one column per coset).
//!
//! The four families share a coset-major param model identical to the
//! production launcher `crate::ntt::dit::monomials_to_evals_dit` — this module
//! reuses that file's geometry/sizing helpers (`ntt_two_pass_smem_bytes`,
//! `clean_triangle_count`, `log_n2_for`) and the runtime d-table fill
//! (`fill_d_table`) rather than re-deriving them. The triangle buffers come from
//! a `crate::ntt_twiddles::DeviceContext`, exactly as the production path and
//! the gpu_ntt tests construct them.
//!
//! Workload: `log_lde = 27 - log_n`, `num_cosets = 1 << log_lde`, `coset_step =
//! 1` (coset_factor_shift = 0 since `log_n + log_lde = 27 = OMEGA_LOG_ORDER`),
//! `cfp_0 = 0`, one contiguous output column per coset so
//! `coset_out_stride = 1 << log_n`.
//!
//! The four families:
//! - two-pass STREAM (runtime `cosets_per_block`, free grid) — `ab_dit_two_pass_*`.
//! - two-pass FIXED-K (`K` compile-time, grid derived) — `ab_dit_two_pass_fixed_*`.
//! - single-pass FIXED-K (`K` compile-time, grid derived) — `ab_dit_single_fixed_*`.
//! - single-pass STREAM (runtime `cosets_per_block`, free grid) — `ab_dit_single_stream_*`.
#![allow(dead_code)]

use std::mem::size_of;

use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, Dim3, KernelFunction};
use era_cudart::memory::DeviceAllocation;
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use era_cudart_sys::{cudaFuncSetAttribute, CudaFuncAttribute};

use crate::ntt::dit::{clean_triangle_count, fill_d_table, log_n2_for, ntt_two_pass_smem_bytes};
use crate::ntt_twiddles::DeviceContext;
use gpu_core::primitives::context::DeviceProperties;
use gpu_core::primitives::field::BF;

// ===========================================================================
// Kernel bindings — 132 `cuda_kernel!` declarations across four ABI families.
// Each binding declares the `extern "C"` symbol AND generates a unique
// `<Type>Function` / `<Type>Arguments`. Within each family, the FIRST binding
// names the shared dispatch type (`Bench2pStream`, `Bench2pFixed`,
// `Bench1pStream`, `Bench1pFixed`); the dispatchers below build that one
// `<Family>Function` while referencing every symbol. Re-binding the production
// `ab_dit_two_pass_*` symbols here is safe: these are `extern "C"`
// declarations, not definitions.
// ===========================================================================

// --- Family A: two-pass STREAM (9-arg ABI). Re-binds the production
// `ab_dit_two_pass_*` symbols (safe: extern declarations, not definitions). The
// first binding names the shared `Bench2pStreamFunction`; later bindings exist
// only to bring their extern symbol into scope for the dispatcher.
cuda_kernel!(Bench2pStream, ab_dit_two_pass_9_3(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pStream103, ab_dit_two_pass_10_3(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pStream113, ab_dit_two_pass_11_3(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pStream123, ab_dit_two_pass_12_3(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pStream133, ab_dit_two_pass_13_3(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pStream82, ab_dit_two_pass_8_2(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pStream92, ab_dit_two_pass_9_2(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pStream102, ab_dit_two_pass_10_2(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pStream112, ab_dit_two_pass_11_2(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pStream122, ab_dit_two_pass_12_2(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));

// --- Family B: two-pass FIXED-K (8-arg ABI, no cosets_per_block).
cuda_kernel!(Bench2pFixed, ab_dit_two_pass_fixed_9_3_1(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed93K2, ab_dit_two_pass_fixed_9_3_2(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed93K4, ab_dit_two_pass_fixed_9_3_4(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed93K8, ab_dit_two_pass_fixed_9_3_8(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed93K16, ab_dit_two_pass_fixed_9_3_16(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed103K1, ab_dit_two_pass_fixed_10_3_1(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed103K2, ab_dit_two_pass_fixed_10_3_2(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed103K4, ab_dit_two_pass_fixed_10_3_4(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed103K8, ab_dit_two_pass_fixed_10_3_8(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed103K16, ab_dit_two_pass_fixed_10_3_16(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed113K1, ab_dit_two_pass_fixed_11_3_1(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed113K2, ab_dit_two_pass_fixed_11_3_2(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed113K4, ab_dit_two_pass_fixed_11_3_4(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed113K8, ab_dit_two_pass_fixed_11_3_8(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed113K16, ab_dit_two_pass_fixed_11_3_16(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed123K1, ab_dit_two_pass_fixed_12_3_1(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed123K2, ab_dit_two_pass_fixed_12_3_2(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed123K4, ab_dit_two_pass_fixed_12_3_4(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed123K8, ab_dit_two_pass_fixed_12_3_8(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed123K16, ab_dit_two_pass_fixed_12_3_16(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed133K1, ab_dit_two_pass_fixed_13_3_1(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed133K2, ab_dit_two_pass_fixed_13_3_2(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed133K4, ab_dit_two_pass_fixed_13_3_4(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed133K8, ab_dit_two_pass_fixed_13_3_8(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed133K16, ab_dit_two_pass_fixed_13_3_16(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed82K1, ab_dit_two_pass_fixed_8_2_1(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed82K2, ab_dit_two_pass_fixed_8_2_2(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed82K4, ab_dit_two_pass_fixed_8_2_4(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed82K8, ab_dit_two_pass_fixed_8_2_8(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed82K16, ab_dit_two_pass_fixed_8_2_16(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed92K1, ab_dit_two_pass_fixed_9_2_1(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed92K2, ab_dit_two_pass_fixed_9_2_2(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed92K4, ab_dit_two_pass_fixed_9_2_4(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed92K8, ab_dit_two_pass_fixed_9_2_8(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed92K16, ab_dit_two_pass_fixed_9_2_16(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed102K1, ab_dit_two_pass_fixed_10_2_1(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed102K2, ab_dit_two_pass_fixed_10_2_2(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed102K4, ab_dit_two_pass_fixed_10_2_4(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed102K8, ab_dit_two_pass_fixed_10_2_8(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed102K16, ab_dit_two_pass_fixed_10_2_16(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed112K1, ab_dit_two_pass_fixed_11_2_1(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed112K2, ab_dit_two_pass_fixed_11_2_2(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed112K4, ab_dit_two_pass_fixed_11_2_4(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed112K8, ab_dit_two_pass_fixed_11_2_8(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed112K16, ab_dit_two_pass_fixed_11_2_16(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed122K1, ab_dit_two_pass_fixed_12_2_1(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed122K2, ab_dit_two_pass_fixed_12_2_2(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed122K4, ab_dit_two_pass_fixed_12_2_4(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed122K8, ab_dit_two_pass_fixed_12_2_8(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench2pFixed122K16, ab_dit_two_pass_fixed_12_2_16(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));

// --- Family C: single-pass STREAM (7-arg ABI).
cuda_kernel!(Bench1pStream, ab_dit_single_stream_3_3(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pStream43, ab_dit_single_stream_4_3(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pStream53, ab_dit_single_stream_5_3(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pStream63, ab_dit_single_stream_6_3(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pStream73, ab_dit_single_stream_7_3(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pStream83, ab_dit_single_stream_8_3(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pStream22, ab_dit_single_stream_2_2(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pStream32, ab_dit_single_stream_3_2(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pStream42, ab_dit_single_stream_4_2(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pStream52, ab_dit_single_stream_5_2(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pStream62, ab_dit_single_stream_6_2(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pStream72, ab_dit_single_stream_7_2(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));

// --- Family D: single-pass FIXED-K (6-arg ABI).
cuda_kernel!(Bench1pFixed, ab_dit_single_fixed_3_3_1(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed33K2, ab_dit_single_fixed_3_3_2(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed33K4, ab_dit_single_fixed_3_3_4(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed33K8, ab_dit_single_fixed_3_3_8(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed33K16, ab_dit_single_fixed_3_3_16(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed43K1, ab_dit_single_fixed_4_3_1(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed43K2, ab_dit_single_fixed_4_3_2(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed43K4, ab_dit_single_fixed_4_3_4(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed43K8, ab_dit_single_fixed_4_3_8(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed43K16, ab_dit_single_fixed_4_3_16(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed53K1, ab_dit_single_fixed_5_3_1(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed53K2, ab_dit_single_fixed_5_3_2(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed53K4, ab_dit_single_fixed_5_3_4(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed53K8, ab_dit_single_fixed_5_3_8(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed53K16, ab_dit_single_fixed_5_3_16(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed63K1, ab_dit_single_fixed_6_3_1(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed63K2, ab_dit_single_fixed_6_3_2(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed63K4, ab_dit_single_fixed_6_3_4(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed63K8, ab_dit_single_fixed_6_3_8(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed63K16, ab_dit_single_fixed_6_3_16(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed73K1, ab_dit_single_fixed_7_3_1(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed73K2, ab_dit_single_fixed_7_3_2(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed73K4, ab_dit_single_fixed_7_3_4(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed73K8, ab_dit_single_fixed_7_3_8(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed73K16, ab_dit_single_fixed_7_3_16(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed83K1, ab_dit_single_fixed_8_3_1(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed83K2, ab_dit_single_fixed_8_3_2(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed83K4, ab_dit_single_fixed_8_3_4(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed83K8, ab_dit_single_fixed_8_3_8(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed83K16, ab_dit_single_fixed_8_3_16(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed22K1, ab_dit_single_fixed_2_2_1(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed22K2, ab_dit_single_fixed_2_2_2(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed22K4, ab_dit_single_fixed_2_2_4(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed22K8, ab_dit_single_fixed_2_2_8(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed22K16, ab_dit_single_fixed_2_2_16(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed32K1, ab_dit_single_fixed_3_2_1(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed32K2, ab_dit_single_fixed_3_2_2(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed32K4, ab_dit_single_fixed_3_2_4(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed32K8, ab_dit_single_fixed_3_2_8(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed32K16, ab_dit_single_fixed_3_2_16(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed42K1, ab_dit_single_fixed_4_2_1(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed42K2, ab_dit_single_fixed_4_2_2(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed42K4, ab_dit_single_fixed_4_2_4(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed42K8, ab_dit_single_fixed_4_2_8(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed42K16, ab_dit_single_fixed_4_2_16(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed52K1, ab_dit_single_fixed_5_2_1(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed52K2, ab_dit_single_fixed_5_2_2(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed52K4, ab_dit_single_fixed_5_2_4(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed52K8, ab_dit_single_fixed_5_2_8(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed52K16, ab_dit_single_fixed_5_2_16(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed62K1, ab_dit_single_fixed_6_2_1(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed62K2, ab_dit_single_fixed_6_2_2(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed62K4, ab_dit_single_fixed_6_2_4(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed62K8, ab_dit_single_fixed_6_2_8(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed62K16, ab_dit_single_fixed_6_2_16(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed72K1, ab_dit_single_fixed_7_2_1(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed72K2, ab_dit_single_fixed_7_2_2(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed72K4, ab_dit_single_fixed_7_2_4(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed72K8, ab_dit_single_fixed_7_2_8(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));
cuda_kernel!(Bench1pFixed72K16, ab_dit_single_fixed_7_2_16(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, coset_out_stride: u32));

// ===========================================================================
// Per-family dispatchers (config -> shared `<Family>Function`). Mirrors the
// production `crate::ntt::dit::two_pass_func` form: every symbol is referenced
// here so the extern declarations are used, but each family collapses to one
// `<Family>Function` so all configs share one `<Family>Arguments::new` at the
// launch site.
// ===========================================================================

/// Family A dispatcher: two-pass STREAM (9-arg). All share `Bench2pStreamFunction`.
fn two_pass_stream_func(log_n: usize, log_vpt: usize) -> Bench2pStreamFunction {
    match (log_n, log_vpt) {
        (9, 3) => Bench2pStreamFunction(ab_dit_two_pass_9_3),
        (10, 3) => Bench2pStreamFunction(ab_dit_two_pass_10_3),
        (11, 3) => Bench2pStreamFunction(ab_dit_two_pass_11_3),
        (12, 3) => Bench2pStreamFunction(ab_dit_two_pass_12_3),
        (13, 3) => Bench2pStreamFunction(ab_dit_two_pass_13_3),
        (8, 2) => Bench2pStreamFunction(ab_dit_two_pass_8_2),
        (9, 2) => Bench2pStreamFunction(ab_dit_two_pass_9_2),
        (10, 2) => Bench2pStreamFunction(ab_dit_two_pass_10_2),
        (11, 2) => Bench2pStreamFunction(ab_dit_two_pass_11_2),
        (12, 2) => Bench2pStreamFunction(ab_dit_two_pass_12_2),
        _ => panic!("unsupported two-pass stream config (log_n={log_n}, log_vpt={log_vpt})"),
    }
}

/// Family B dispatcher: two-pass FIXED-K (8-arg). All share `Bench2pFixedFunction`.
fn two_pass_fixed_func(log_n: usize, log_vpt: usize, k: u32) -> Bench2pFixedFunction {
    match (log_n, log_vpt, k) {
        (9, 3, 1) => Bench2pFixedFunction(ab_dit_two_pass_fixed_9_3_1),
        (9, 3, 2) => Bench2pFixedFunction(ab_dit_two_pass_fixed_9_3_2),
        (9, 3, 4) => Bench2pFixedFunction(ab_dit_two_pass_fixed_9_3_4),
        (9, 3, 8) => Bench2pFixedFunction(ab_dit_two_pass_fixed_9_3_8),
        (9, 3, 16) => Bench2pFixedFunction(ab_dit_two_pass_fixed_9_3_16),
        (10, 3, 1) => Bench2pFixedFunction(ab_dit_two_pass_fixed_10_3_1),
        (10, 3, 2) => Bench2pFixedFunction(ab_dit_two_pass_fixed_10_3_2),
        (10, 3, 4) => Bench2pFixedFunction(ab_dit_two_pass_fixed_10_3_4),
        (10, 3, 8) => Bench2pFixedFunction(ab_dit_two_pass_fixed_10_3_8),
        (10, 3, 16) => Bench2pFixedFunction(ab_dit_two_pass_fixed_10_3_16),
        (11, 3, 1) => Bench2pFixedFunction(ab_dit_two_pass_fixed_11_3_1),
        (11, 3, 2) => Bench2pFixedFunction(ab_dit_two_pass_fixed_11_3_2),
        (11, 3, 4) => Bench2pFixedFunction(ab_dit_two_pass_fixed_11_3_4),
        (11, 3, 8) => Bench2pFixedFunction(ab_dit_two_pass_fixed_11_3_8),
        (11, 3, 16) => Bench2pFixedFunction(ab_dit_two_pass_fixed_11_3_16),
        (12, 3, 1) => Bench2pFixedFunction(ab_dit_two_pass_fixed_12_3_1),
        (12, 3, 2) => Bench2pFixedFunction(ab_dit_two_pass_fixed_12_3_2),
        (12, 3, 4) => Bench2pFixedFunction(ab_dit_two_pass_fixed_12_3_4),
        (12, 3, 8) => Bench2pFixedFunction(ab_dit_two_pass_fixed_12_3_8),
        (12, 3, 16) => Bench2pFixedFunction(ab_dit_two_pass_fixed_12_3_16),
        (13, 3, 1) => Bench2pFixedFunction(ab_dit_two_pass_fixed_13_3_1),
        (13, 3, 2) => Bench2pFixedFunction(ab_dit_two_pass_fixed_13_3_2),
        (13, 3, 4) => Bench2pFixedFunction(ab_dit_two_pass_fixed_13_3_4),
        (13, 3, 8) => Bench2pFixedFunction(ab_dit_two_pass_fixed_13_3_8),
        (13, 3, 16) => Bench2pFixedFunction(ab_dit_two_pass_fixed_13_3_16),
        (8, 2, 1) => Bench2pFixedFunction(ab_dit_two_pass_fixed_8_2_1),
        (8, 2, 2) => Bench2pFixedFunction(ab_dit_two_pass_fixed_8_2_2),
        (8, 2, 4) => Bench2pFixedFunction(ab_dit_two_pass_fixed_8_2_4),
        (8, 2, 8) => Bench2pFixedFunction(ab_dit_two_pass_fixed_8_2_8),
        (8, 2, 16) => Bench2pFixedFunction(ab_dit_two_pass_fixed_8_2_16),
        (9, 2, 1) => Bench2pFixedFunction(ab_dit_two_pass_fixed_9_2_1),
        (9, 2, 2) => Bench2pFixedFunction(ab_dit_two_pass_fixed_9_2_2),
        (9, 2, 4) => Bench2pFixedFunction(ab_dit_two_pass_fixed_9_2_4),
        (9, 2, 8) => Bench2pFixedFunction(ab_dit_two_pass_fixed_9_2_8),
        (9, 2, 16) => Bench2pFixedFunction(ab_dit_two_pass_fixed_9_2_16),
        (10, 2, 1) => Bench2pFixedFunction(ab_dit_two_pass_fixed_10_2_1),
        (10, 2, 2) => Bench2pFixedFunction(ab_dit_two_pass_fixed_10_2_2),
        (10, 2, 4) => Bench2pFixedFunction(ab_dit_two_pass_fixed_10_2_4),
        (10, 2, 8) => Bench2pFixedFunction(ab_dit_two_pass_fixed_10_2_8),
        (10, 2, 16) => Bench2pFixedFunction(ab_dit_two_pass_fixed_10_2_16),
        (11, 2, 1) => Bench2pFixedFunction(ab_dit_two_pass_fixed_11_2_1),
        (11, 2, 2) => Bench2pFixedFunction(ab_dit_two_pass_fixed_11_2_2),
        (11, 2, 4) => Bench2pFixedFunction(ab_dit_two_pass_fixed_11_2_4),
        (11, 2, 8) => Bench2pFixedFunction(ab_dit_two_pass_fixed_11_2_8),
        (11, 2, 16) => Bench2pFixedFunction(ab_dit_two_pass_fixed_11_2_16),
        (12, 2, 1) => Bench2pFixedFunction(ab_dit_two_pass_fixed_12_2_1),
        (12, 2, 2) => Bench2pFixedFunction(ab_dit_two_pass_fixed_12_2_2),
        (12, 2, 4) => Bench2pFixedFunction(ab_dit_two_pass_fixed_12_2_4),
        (12, 2, 8) => Bench2pFixedFunction(ab_dit_two_pass_fixed_12_2_8),
        (12, 2, 16) => Bench2pFixedFunction(ab_dit_two_pass_fixed_12_2_16),
        _ => panic!("unsupported two-pass fixed config (log_n={log_n}, log_vpt={log_vpt}, k={k})"),
    }
}

/// Family C dispatcher: single-pass STREAM (7-arg). All share `Bench1pStreamFunction`.
fn single_stream_func(log_n: usize, log_vpt: usize) -> Bench1pStreamFunction {
    match (log_n, log_vpt) {
        (3, 3) => Bench1pStreamFunction(ab_dit_single_stream_3_3),
        (4, 3) => Bench1pStreamFunction(ab_dit_single_stream_4_3),
        (5, 3) => Bench1pStreamFunction(ab_dit_single_stream_5_3),
        (6, 3) => Bench1pStreamFunction(ab_dit_single_stream_6_3),
        (7, 3) => Bench1pStreamFunction(ab_dit_single_stream_7_3),
        (8, 3) => Bench1pStreamFunction(ab_dit_single_stream_8_3),
        (2, 2) => Bench1pStreamFunction(ab_dit_single_stream_2_2),
        (3, 2) => Bench1pStreamFunction(ab_dit_single_stream_3_2),
        (4, 2) => Bench1pStreamFunction(ab_dit_single_stream_4_2),
        (5, 2) => Bench1pStreamFunction(ab_dit_single_stream_5_2),
        (6, 2) => Bench1pStreamFunction(ab_dit_single_stream_6_2),
        (7, 2) => Bench1pStreamFunction(ab_dit_single_stream_7_2),
        _ => panic!("unsupported single-pass stream config (log_n={log_n}, log_vpt={log_vpt})"),
    }
}

/// Family D dispatcher: single-pass FIXED-K (6-arg). All share `Bench1pFixedFunction`.
fn single_fixed_func(log_n: usize, log_vpt: usize, k: u32) -> Bench1pFixedFunction {
    match (log_n, log_vpt, k) {
        (3, 3, 1) => Bench1pFixedFunction(ab_dit_single_fixed_3_3_1),
        (3, 3, 2) => Bench1pFixedFunction(ab_dit_single_fixed_3_3_2),
        (3, 3, 4) => Bench1pFixedFunction(ab_dit_single_fixed_3_3_4),
        (3, 3, 8) => Bench1pFixedFunction(ab_dit_single_fixed_3_3_8),
        (3, 3, 16) => Bench1pFixedFunction(ab_dit_single_fixed_3_3_16),
        (4, 3, 1) => Bench1pFixedFunction(ab_dit_single_fixed_4_3_1),
        (4, 3, 2) => Bench1pFixedFunction(ab_dit_single_fixed_4_3_2),
        (4, 3, 4) => Bench1pFixedFunction(ab_dit_single_fixed_4_3_4),
        (4, 3, 8) => Bench1pFixedFunction(ab_dit_single_fixed_4_3_8),
        (4, 3, 16) => Bench1pFixedFunction(ab_dit_single_fixed_4_3_16),
        (5, 3, 1) => Bench1pFixedFunction(ab_dit_single_fixed_5_3_1),
        (5, 3, 2) => Bench1pFixedFunction(ab_dit_single_fixed_5_3_2),
        (5, 3, 4) => Bench1pFixedFunction(ab_dit_single_fixed_5_3_4),
        (5, 3, 8) => Bench1pFixedFunction(ab_dit_single_fixed_5_3_8),
        (5, 3, 16) => Bench1pFixedFunction(ab_dit_single_fixed_5_3_16),
        (6, 3, 1) => Bench1pFixedFunction(ab_dit_single_fixed_6_3_1),
        (6, 3, 2) => Bench1pFixedFunction(ab_dit_single_fixed_6_3_2),
        (6, 3, 4) => Bench1pFixedFunction(ab_dit_single_fixed_6_3_4),
        (6, 3, 8) => Bench1pFixedFunction(ab_dit_single_fixed_6_3_8),
        (6, 3, 16) => Bench1pFixedFunction(ab_dit_single_fixed_6_3_16),
        (7, 3, 1) => Bench1pFixedFunction(ab_dit_single_fixed_7_3_1),
        (7, 3, 2) => Bench1pFixedFunction(ab_dit_single_fixed_7_3_2),
        (7, 3, 4) => Bench1pFixedFunction(ab_dit_single_fixed_7_3_4),
        (7, 3, 8) => Bench1pFixedFunction(ab_dit_single_fixed_7_3_8),
        (7, 3, 16) => Bench1pFixedFunction(ab_dit_single_fixed_7_3_16),
        (8, 3, 1) => Bench1pFixedFunction(ab_dit_single_fixed_8_3_1),
        (8, 3, 2) => Bench1pFixedFunction(ab_dit_single_fixed_8_3_2),
        (8, 3, 4) => Bench1pFixedFunction(ab_dit_single_fixed_8_3_4),
        (8, 3, 8) => Bench1pFixedFunction(ab_dit_single_fixed_8_3_8),
        (8, 3, 16) => Bench1pFixedFunction(ab_dit_single_fixed_8_3_16),
        (2, 2, 1) => Bench1pFixedFunction(ab_dit_single_fixed_2_2_1),
        (2, 2, 2) => Bench1pFixedFunction(ab_dit_single_fixed_2_2_2),
        (2, 2, 4) => Bench1pFixedFunction(ab_dit_single_fixed_2_2_4),
        (2, 2, 8) => Bench1pFixedFunction(ab_dit_single_fixed_2_2_8),
        (2, 2, 16) => Bench1pFixedFunction(ab_dit_single_fixed_2_2_16),
        (3, 2, 1) => Bench1pFixedFunction(ab_dit_single_fixed_3_2_1),
        (3, 2, 2) => Bench1pFixedFunction(ab_dit_single_fixed_3_2_2),
        (3, 2, 4) => Bench1pFixedFunction(ab_dit_single_fixed_3_2_4),
        (3, 2, 8) => Bench1pFixedFunction(ab_dit_single_fixed_3_2_8),
        (3, 2, 16) => Bench1pFixedFunction(ab_dit_single_fixed_3_2_16),
        (4, 2, 1) => Bench1pFixedFunction(ab_dit_single_fixed_4_2_1),
        (4, 2, 2) => Bench1pFixedFunction(ab_dit_single_fixed_4_2_2),
        (4, 2, 4) => Bench1pFixedFunction(ab_dit_single_fixed_4_2_4),
        (4, 2, 8) => Bench1pFixedFunction(ab_dit_single_fixed_4_2_8),
        (4, 2, 16) => Bench1pFixedFunction(ab_dit_single_fixed_4_2_16),
        (5, 2, 1) => Bench1pFixedFunction(ab_dit_single_fixed_5_2_1),
        (5, 2, 2) => Bench1pFixedFunction(ab_dit_single_fixed_5_2_2),
        (5, 2, 4) => Bench1pFixedFunction(ab_dit_single_fixed_5_2_4),
        (5, 2, 8) => Bench1pFixedFunction(ab_dit_single_fixed_5_2_8),
        (5, 2, 16) => Bench1pFixedFunction(ab_dit_single_fixed_5_2_16),
        (6, 2, 1) => Bench1pFixedFunction(ab_dit_single_fixed_6_2_1),
        (6, 2, 2) => Bench1pFixedFunction(ab_dit_single_fixed_6_2_2),
        (6, 2, 4) => Bench1pFixedFunction(ab_dit_single_fixed_6_2_4),
        (6, 2, 8) => Bench1pFixedFunction(ab_dit_single_fixed_6_2_8),
        (6, 2, 16) => Bench1pFixedFunction(ab_dit_single_fixed_6_2_16),
        (7, 2, 1) => Bench1pFixedFunction(ab_dit_single_fixed_7_2_1),
        (7, 2, 2) => Bench1pFixedFunction(ab_dit_single_fixed_7_2_2),
        (7, 2, 4) => Bench1pFixedFunction(ab_dit_single_fixed_7_2_4),
        (7, 2, 8) => Bench1pFixedFunction(ab_dit_single_fixed_7_2_8),
        (7, 2, 16) => Bench1pFixedFunction(ab_dit_single_fixed_7_2_16),
        _ => {
            panic!("unsupported single-pass fixed config (log_n={log_n}, log_vpt={log_vpt}, k={k})")
        }
    }
}

// ===========================================================================
// Geometry. One fixed workload per (log_n, log_vpt): a full LDE that lands at
// `log_n + log_lde = 27` so `coset_factor_shift = OMEGA_LOG_ORDER - 27 = 0` ⇒
// `coset_step = 1` and `cfp_0 = 0`. Output is one contiguous BF column per
// coset, so `coset_out_stride = 1 << log_n`.
// ===========================================================================

/// Sum of `log_n + log_lde` for the bench workload (== OMEGA_LOG_ORDER, so the
/// coset factor shift is exactly 0).
pub const TOTAL_LOG: usize = 27;

const CFP_0: u32 = 0;
const COSET_STEP: u32 = 1;

/// Number of cosets for the fixed workload at `log_n`.
fn num_cosets_for(log_n: usize) -> usize {
    1usize << (TOTAL_LOG - log_n)
}

/// Per-coset output stride (one contiguous BF column) for the fixed workload.
fn coset_out_stride_for(log_n: usize) -> u32 {
    1u32 << log_n
}

/// Single-pass `SLOTS_PER_BLOCK = floor(128 / lanes)`, `lanes = 1 <<
/// (log_n - log_vpt)`. Mirrors the engine geometry baked into the wrappers
/// (NUM_WARPS = 4 ⇒ 128 threads per block).
fn single_slots_per_block(log_n: usize, log_vpt: usize) -> usize {
    let lanes = 1usize << (log_n - log_vpt);
    (4 * 32) / lanes
}

const SINGLE_BLOCK_DIM: u32 = 4 * 32; // NUM_WARPS * 32 = 128

// ===========================================================================
// Direct-launch drivers. One per family. Each takes the fixed workload device
// pointers (mono input, strided output, d-table scratch), the chosen geometry
// knob (free `grid` for STREAM, compile-time `k` for FIXED), the borrowed
// `DeviceContext` triangles, the stream, and device props. Every path asserts
// exact divisibility so an invalid config panics loudly rather than silently
// mis-covering the coset range. The fixed workload uses one column, so each
// driver issues a single launch (no column loop).
// ===========================================================================

/// Two-pass STREAM: caller-chosen launch `grid` (any value in `[1, num_cosets]`).
/// The guarded grid-stride kernel walks the full `num_cosets`; the d-table
/// advances `grid` cosets per kernel iteration (`step_per_iter = grid * coset_step`).
#[allow(clippy::too_many_arguments)]
fn launch_two_pass_stream(
    log_n: usize,
    log_vpt: usize,
    grid: u32,
    ctx: &DeviceContext,
    mono: *const BF,
    out: *mut BF,
    d_scratch: &mut DeviceSlice<BF>,
    stream: &CudaStream,
    props: &DeviceProperties,
) -> CudaResult<()> {
    let n = 1usize << log_n;
    let num_cosets = num_cosets_for(log_n);
    let step_per_iter = grid.wrapping_mul(COSET_STEP);

    let smem = ntt_two_pass_smem_bytes(log_n as u32, log_vpt as u32);
    assert!(
        smem <= props.max_dynamic_smem_per_block_optin,
        "two-pass DIT at log_n={log_n} needs {smem} bytes dynamic smem (cap {})",
        props.max_dynamic_smem_per_block_optin,
    );

    let tw_p1 = ctx.coupled_triangle(log_n as u32, log_vpt as u32).as_ptr();
    let log_n2 = log_n2_for(log_n as u32, log_vpt as u32);
    let tw_p2 = ctx.clean_triangle(log_n2, log_vpt as u32).as_ptr();

    assert!(
        d_scratch.len() >= n,
        "d_scratch len ({}) < N ({n})",
        d_scratch.len()
    );
    let d_table = &mut d_scratch[..n];
    fill_d_table(log_n as u32, d_table, step_per_iter, stream)?;
    let d_table_ptr = d_table.as_ptr();

    let func = two_pass_stream_func(log_n, log_vpt);
    unsafe {
        cudaFuncSetAttribute(
            func.as_ptr(),
            CudaFuncAttribute::MaxDynamicSharedMemorySize,
            smem as i32,
        )
        .wrap()?;
    }

    let grid_dim: Dim3 = (grid as u32).into();
    let block_dim: Dim3 = ((n >> log_vpt) as u32).into();
    let mut config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    config.dynamic_smem_bytes = smem;
    let args = Bench2pStreamArguments::new(
        mono,
        tw_p1,
        tw_p2,
        d_table_ptr,
        out,
        CFP_0,
        COSET_STEP,
        num_cosets as u32,
        coset_out_stride_for(log_n),
    );
    func.launch(&config, &args)
}

/// Two-pass FIXED-K: compile-time `K`, so `grid = num_cosets / K` and the
/// d-table advances `grid` cosets per iteration. No `cosets_per_block` arg.
#[allow(clippy::too_many_arguments)]
fn launch_two_pass_fixed(
    log_n: usize,
    log_vpt: usize,
    k: u32,
    ctx: &DeviceContext,
    mono: *const BF,
    out: *mut BF,
    d_scratch: &mut DeviceSlice<BF>,
    stream: &CudaStream,
    props: &DeviceProperties,
) -> CudaResult<()> {
    let n = 1usize << log_n;
    let num_cosets = num_cosets_for(log_n);
    let k_usize = k as usize;
    assert!(
        num_cosets % k_usize == 0,
        "two-pass fixed: num_cosets ({num_cosets}) not divisible by k ({k})"
    );
    let grid = num_cosets / k_usize;
    let step_per_iter = (grid as u32).wrapping_mul(COSET_STEP);

    let smem = ntt_two_pass_smem_bytes(log_n as u32, log_vpt as u32);
    assert!(
        smem <= props.max_dynamic_smem_per_block_optin,
        "two-pass DIT at log_n={log_n} needs {smem} bytes dynamic smem (cap {})",
        props.max_dynamic_smem_per_block_optin,
    );

    let tw_p1 = ctx.coupled_triangle(log_n as u32, log_vpt as u32).as_ptr();
    let log_n2 = log_n2_for(log_n as u32, log_vpt as u32);
    let tw_p2 = ctx.clean_triangle(log_n2, log_vpt as u32).as_ptr();

    assert!(
        d_scratch.len() >= n,
        "d_scratch len ({}) < N ({n})",
        d_scratch.len()
    );
    let d_table = &mut d_scratch[..n];
    fill_d_table(log_n as u32, d_table, step_per_iter, stream)?;
    let d_table_ptr = d_table.as_ptr();

    let func = two_pass_fixed_func(log_n, log_vpt, k);
    unsafe {
        cudaFuncSetAttribute(
            func.as_ptr(),
            CudaFuncAttribute::MaxDynamicSharedMemorySize,
            smem as i32,
        )
        .wrap()?;
    }

    let grid_dim: Dim3 = (grid as u32).into();
    let block_dim: Dim3 = ((n >> log_vpt) as u32).into();
    let mut config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    config.dynamic_smem_bytes = smem;
    let args = Bench2pFixedArguments::new(
        mono,
        tw_p1,
        tw_p2,
        d_table_ptr,
        out,
        CFP_0,
        COSET_STEP,
        coset_out_stride_for(log_n),
    );
    func.launch(&config, &args)
}

/// Single-pass FIXED-K: each block does `SLOTS_PER_BLOCK * K` cosets, so
/// `grid = num_cosets / (slots_per_block * K)`. No d-table; smem = clean
/// triangle bytes (< 48 KB, no opt-in needed).
#[allow(clippy::too_many_arguments)]
fn launch_single_fixed(
    log_n: usize,
    log_vpt: usize,
    k: u32,
    ctx: &DeviceContext,
    mono: *const BF,
    out: *mut BF,
    stream: &CudaStream,
) -> CudaResult<()> {
    let num_cosets = num_cosets_for(log_n);
    let slots_per_block = single_slots_per_block(log_n, log_vpt);
    let cosets_per_block_total = slots_per_block * (k as usize);
    assert!(
        num_cosets % cosets_per_block_total == 0,
        "single-pass fixed: num_cosets ({num_cosets}) not divisible by \
         slots_per_block*k ({cosets_per_block_total}) at log_n={log_n}, log_vpt={log_vpt}, k={k}"
    );
    let grid = num_cosets / cosets_per_block_total;

    let tw_clean = ctx.clean_triangle(log_n as u32, log_vpt as u32).as_ptr();
    let smem = clean_triangle_count(log_n as u32, log_vpt as u32) * size_of::<BF>();

    let func = single_fixed_func(log_n, log_vpt, k);
    let grid_dim: Dim3 = (grid as u32).into();
    let block_dim: Dim3 = SINGLE_BLOCK_DIM.into();
    let mut config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    config.dynamic_smem_bytes = smem;
    let args = Bench1pFixedArguments::new(
        mono,
        tw_clean,
        out,
        CFP_0,
        COSET_STEP,
        coset_out_stride_for(log_n),
    );
    func.launch(&config, &args)
}

/// Single-pass STREAM: caller-chosen launch `grid` (any value). The kernel's
/// slot stride is `gridDim.x * SLOTS_PER_BLOCK` and a guard (`coset_idx <
/// num_cosets`) covers the full coset range. No d-table; smem = clean triangle
/// bytes.
#[allow(clippy::too_many_arguments)]
fn launch_single_stream(
    log_n: usize,
    log_vpt: usize,
    grid: u32,
    ctx: &DeviceContext,
    mono: *const BF,
    out: *mut BF,
    stream: &CudaStream,
) -> CudaResult<()> {
    let num_cosets = num_cosets_for(log_n);

    let tw_clean = ctx.clean_triangle(log_n as u32, log_vpt as u32).as_ptr();
    let smem = clean_triangle_count(log_n as u32, log_vpt as u32) * size_of::<BF>();

    let func = single_stream_func(log_n, log_vpt);
    let grid_dim: Dim3 = grid.into();
    let block_dim: Dim3 = SINGLE_BLOCK_DIM.into();
    let mut config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    config.dynamic_smem_bytes = smem;
    let args = Bench1pStreamArguments::new(
        mono,
        tw_clean,
        out,
        CFP_0,
        COSET_STEP,
        num_cosets as u32,
        coset_out_stride_for(log_n),
    );
    func.launch(&config, &args)
}

// ===========================================================================
// Ping-pong harness + Criterion-facing config enum.
//
// `DitBenchHarness` owns: a `DeviceContext` (keeps the twiddle `__constant__`
// tables + the precomputed `DitTriangles` alive), two input buffers (each N),
// two output buffers (each 2^27 = 512 MB — the full LDE span, since the streamed
// cosets write `coset_idx * (1<<log_n)` strided offsets up to 2^27), and one
// d-table scratch (N). `run` alternates buffers per iteration so the L2 working
// set rotates and small-`log_n` re-runs don't read entirely from L2.
//
// Timing is left entirely to Criterion (the `CudaMeasurement`); the harness only
// enqueues a launch. GB/s is computed downstream from Criterion times.
// ===========================================================================

/// Which kernel family + geometry knob to launch for one bench point.
#[derive(Clone, Copy, Debug)]
pub enum LaunchCfg {
    /// Two-pass STREAM, free power-of-two `grid` (a pow2 divisor of num_cosets).
    TwoPassStream { grid: u32 },
    /// Two-pass FIXED-K, compile-time `K` (grid = num_cosets / K).
    TwoPassFixed { k: u32 },
    /// Single-pass FIXED-K, compile-time `K` (grid = num_cosets / (slots*K)).
    SinglePassFixed { k: u32 },
    /// Single-pass STREAM, free power-of-two `grid`
    /// (cosets_per_block = num_cosets / (grid * slots_per_block)).
    SinglePassStream { grid: u32 },
}

/// Returns `false` when `cfg` would fail the divisibility / pow2 asserts in the
/// matching launch path for `(log_n, log_vpt)` — so a Criterion sweep can skip
/// invalid combos instead of panicking. Mirrors each driver's assertions
/// exactly. Also requires the config be one the dispatchers support.
pub fn is_valid(log_n: usize, log_vpt: usize, cfg: LaunchCfg) -> bool {
    if !(2..=13).contains(&log_n) || (log_vpt != 2 && log_vpt != 3) || log_n < log_vpt {
        return false;
    }
    let num_cosets = num_cosets_for(log_n);
    match cfg {
        LaunchCfg::TwoPassStream { grid } => {
            // Two-pass requires log_n > log_vpt + 5 (the production split point).
            // grid is FREE: the guarded grid-stride loop covers num_cosets for
            // any grid in [1, num_cosets] (no pow2 / divisibility requirement).
            log_n > log_vpt + 5 && grid >= 1 && (grid as usize) <= num_cosets
        }
        LaunchCfg::TwoPassFixed { k } => {
            log_n > log_vpt + 5 && k != 0 && num_cosets % (k as usize) == 0
        }
        LaunchCfg::SinglePassFixed { k } => {
            if log_n > log_vpt + 5 || k == 0 {
                return false;
            }
            let denom = single_slots_per_block(log_n, log_vpt) * (k as usize);
            denom != 0 && num_cosets % denom == 0
        }
        LaunchCfg::SinglePassStream { grid } => {
            // grid is FREE: the guarded kernel maps coset_idx = s + spb*(b +
            // c*grid) and loops while coset_idx < num_cosets, covering [0,
            // num_cosets) exactly once for ANY grid (no divisibility).
            log_n <= log_vpt + 5 && grid >= 1 && (grid as usize) <= num_cosets
        }
    }
}

/// `powers_of_w_coarse_log_count` for the twiddle context. Matches the
/// `GMEM_COARSE_LOG_COUNT` default used by the prover and the gpu_ntt tests.
const TWIDDLE_LOG_COUNT: u32 = 13;

pub struct DitBenchHarness {
    /// Keeps the NTT twiddle `__constant__` tables + the precomputed
    /// `DitTriangles` alive for the harness' lifetime (the launchers read them).
    _ctx: DeviceContext,
    props: DeviceProperties,
    log_n: usize,
    log_vpt: usize,
    log_lde: usize,
    /// Two input buffers, each `1 << log_n`, ping-ponged per iteration.
    inputs: [DeviceAllocation<BF>; 2],
    /// Two output buffers, each `1 << 27` (512 MB), ping-ponged per iteration.
    outputs: [DeviceAllocation<BF>; 2],
    /// Two-pass d-table scratch (len `1 << log_n`); ignored by single-pass.
    d_scratch: DeviceAllocation<BF>,
    iter: usize,
}

impl DitBenchHarness {
    pub fn new(log_n: usize, log_vpt: usize, _stream: &CudaStream) -> CudaResult<Self> {
        let _ctx = DeviceContext::create(TWIDDLE_LOG_COUNT)?;
        let props = DeviceProperties::new()?;
        let n = 1usize << log_n;
        let out_len = 1usize << TOTAL_LOG;
        let inputs = [
            DeviceAllocation::<BF>::alloc(n)?,
            DeviceAllocation::<BF>::alloc(n)?,
        ];
        let outputs = [
            DeviceAllocation::<BF>::alloc(out_len)?,
            DeviceAllocation::<BF>::alloc(out_len)?,
        ];
        let d_scratch = DeviceAllocation::<BF>::alloc(n)?;
        Ok(Self {
            _ctx,
            props,
            log_n,
            log_vpt,
            log_lde: TOTAL_LOG - log_n,
            inputs,
            outputs,
            d_scratch,
            iter: 0,
        })
    }

    /// Enqueue one launch of the chosen config, ping-ponging input/output
    /// buffers. Caller drives timing via Criterion.
    pub fn run(&mut self, cfg: LaunchCfg, stream: &CudaStream) -> CudaResult<()> {
        let i = self.iter & 1;
        let log_n = self.log_n;
        let log_vpt = self.log_vpt;
        let mono = self.inputs[i].as_ptr();
        let out = self.outputs[i].as_mut_ptr();
        match cfg {
            LaunchCfg::TwoPassStream { grid } => launch_two_pass_stream(
                log_n,
                log_vpt,
                grid,
                &self._ctx,
                mono,
                out,
                &mut self.d_scratch[..],
                stream,
                &self.props,
            )?,
            LaunchCfg::TwoPassFixed { k } => launch_two_pass_fixed(
                log_n,
                log_vpt,
                k,
                &self._ctx,
                mono,
                out,
                &mut self.d_scratch[..],
                stream,
                &self.props,
            )?,
            LaunchCfg::SinglePassFixed { k } => {
                launch_single_fixed(log_n, log_vpt, k, &self._ctx, mono, out, stream)?
            }
            LaunchCfg::SinglePassStream { grid } => {
                launch_single_stream(log_n, log_vpt, grid, &self._ctx, mono, out, stream)?
            }
        }
        self.iter += 1;
        Ok(())
    }

    /// Grid for exactly ONE WAVE of the two-pass streaming kernel:
    /// `sm_count × max_active_blocks_per_SM(kernel)`, clamped to `[1,
    /// num_cosets]`. The resident-block count is queried at runtime via the
    /// occupancy API (no hand-derived smem/thread math). The guarded grid-stride
    /// loop covers the remaining cosets.
    pub fn one_wave_grid_two_pass(&self) -> CudaResult<u32> {
        let smem = ntt_two_pass_smem_bytes(self.log_n as u32, self.log_vpt as u32);
        let block = ((1u32 << self.log_n) >> self.log_vpt) as i32;
        let func = two_pass_stream_func(self.log_n, self.log_vpt);
        unsafe {
            cudaFuncSetAttribute(
                func.as_ptr(),
                CudaFuncAttribute::MaxDynamicSharedMemorySize,
                smem as i32,
            )
            .wrap()?;
        }
        let occ = era_cudart::occupancy::max_active_blocks_per_multiprocessor(&func, block, smem)?;
        let num_cosets = num_cosets_for(self.log_n);
        Ok((self.props.sm_count * (occ.max(1) as usize))
            .min(num_cosets)
            .max(1) as u32)
    }

    /// Grid for one wave of the single-pass streaming kernel (smem = clean
    /// triangle, < 48 KB; block = 128).
    pub fn one_wave_grid_single(&self) -> CudaResult<u32> {
        let smem = clean_triangle_count(self.log_n as u32, self.log_vpt as u32) * size_of::<BF>();
        let func = single_stream_func(self.log_n, self.log_vpt);
        let occ = era_cudart::occupancy::max_active_blocks_per_multiprocessor(
            &func,
            SINGLE_BLOCK_DIM as i32,
            smem,
        )?;
        let num_cosets = num_cosets_for(self.log_n);
        Ok((self.props.sm_count * (occ.max(1) as usize))
            .min(num_cosets)
            .max(1) as u32)
    }

    /// One-line geometry summary for logging (grid / block / cosets_per_block).
    pub fn describe(&self, cfg: &LaunchCfg) -> String {
        let log_n = self.log_n;
        let log_vpt = self.log_vpt;
        let num_cosets = num_cosets_for(log_n);
        match *cfg {
            LaunchCfg::TwoPassStream { grid } => {
                let block = (1usize << log_n) >> log_vpt;
                let cpb = num_cosets / (grid as usize).max(1);
                format!(
                    "two_pass_stream log_n={log_n} vpt={log_vpt} lde={} num_cosets={num_cosets} \
                     grid={grid} block={block} cosets_per_block={cpb}",
                    self.log_lde
                )
            }
            LaunchCfg::TwoPassFixed { k } => {
                let block = (1usize << log_n) >> log_vpt;
                let grid = num_cosets / (k as usize).max(1);
                format!(
                    "two_pass_fixed log_n={log_n} vpt={log_vpt} lde={} num_cosets={num_cosets} \
                     k={k} grid={grid} block={block}",
                    self.log_lde
                )
            }
            LaunchCfg::SinglePassFixed { k } => {
                let slots = single_slots_per_block(log_n, log_vpt);
                let denom = slots * (k as usize).max(1);
                let grid = num_cosets / denom.max(1);
                format!(
                    "single_fixed log_n={log_n} vpt={log_vpt} lde={} num_cosets={num_cosets} \
                     k={k} slots_per_block={slots} grid={grid} block={SINGLE_BLOCK_DIM}",
                    self.log_lde
                )
            }
            LaunchCfg::SinglePassStream { grid } => {
                let slots = single_slots_per_block(log_n, log_vpt);
                let denom = (grid as usize).max(1) * slots;
                let cpb = num_cosets / denom.max(1);
                format!(
                    "single_stream log_n={log_n} vpt={log_vpt} lde={} num_cosets={num_cosets} \
                     grid={grid} slots_per_block={slots} cosets_per_block={cpb} \
                     block={SINGLE_BLOCK_DIM}",
                    self.log_lde
                )
            }
        }
    }
}
