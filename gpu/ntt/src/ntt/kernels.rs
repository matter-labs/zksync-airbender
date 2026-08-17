#![allow(non_snake_case)]

use era_cudart::cuda_kernel_signature_and_arguments;
use gpu_core::primitives::device_structures::{MutPtrAndStride, PtrAndStride};
use gpu_core::primitives::field::BaseField;

type BF = BaseField;

cuda_kernel_signature_and_arguments!(
    pub(super) StridedTilesStages,
    inputs_matrix: PtrAndStride<BF>,
    outputs_matrix: MutPtrAndStride<BF>,
    log_n: i32,
    start_stage: i32,
    num_cols_per_coset: i32,
    log_cosets_in_tile: i32,
);
// Hand-expanded copy of era_cudart 0.156.0's `cuda_kernel_function!` with a
// `pub(super)` field (its multi-arm `cuda_kernel!` macro forces the tuple
// field private for the multi-kernel-per-signature arm used here); re-sync
// this expansion on any era_cudart bump.
pub(super) struct StridedTilesStagesFunction(pub(super) StridedTilesStagesSignature);
impl era_cudart::execution::KernelFunction for StridedTilesStagesFunction {
    type Signature = StridedTilesStagesSignature;
    fn as_ptr(&self) -> *const std::os::raw::c_void {
        self.0 as *const std::os::raw::c_void
    }
}
macro_rules! strided_tiles_stages {
    ($kernel_name:ident) => {
        ::era_cudart::cuda_kernel_declaration!(pub(super) $kernel_name(
    inputs_matrix: PtrAndStride<BF>,
    outputs_matrix: MutPtrAndStride<BF>,
    log_n: i32,
    start_stage: i32,
    num_cols_per_coset: i32,
    log_cosets_in_tile: i32,
        ));
    };
}

// 2-pass evals to monomials
strided_tiles_stages!(ab_evals_to_monomials_first_9_stages_kernel);
strided_tiles_stages!(ab_evals_to_monomials_first_10_stages_kernel);

// 3-pass evals to monomials
strided_tiles_stages!(ab_evals_to_monomials_nonfinal_8_stages_kernel);

// 2-pass monomials to evals
strided_tiles_stages!(ab_monomials_to_evals_last_9_stages_kernel);
strided_tiles_stages!(ab_monomials_to_evals_last_10_stages_kernel);

// 3-pass monomials to evals
strided_tiles_stages!(ab_monomials_to_evals_noninitial_8_stages_kernel);
// evict-first variant for the LAST noninitial pass (hybrid LDE path)
strided_tiles_stages!(ab_monomials_to_evals_noninitial_8_stages_evict_kernel);

cuda_kernel_signature_and_arguments!(
    pub(super) EvalsToMonomialsFinal,
    inputs_matrix: PtrAndStride<BF>,
    outputs_matrix: MutPtrAndStride<BF>,
    transposed_monomials: bool,
    log_n: i32,
    num_cols_per_coset: i32,
    log_cosets_in_tile: i32,
);
pub(super) struct EvalsToMonomialsFinalFunction(pub(super) EvalsToMonomialsFinalSignature);
impl era_cudart::execution::KernelFunction for EvalsToMonomialsFinalFunction {
    type Signature = EvalsToMonomialsFinalSignature;
    fn as_ptr(&self) -> *const std::os::raw::c_void {
        self.0 as *const std::os::raw::c_void
    }
}
macro_rules! evals_to_monomials_final {
    ($kernel_name:ident) => {
        ::era_cudart::cuda_kernel_declaration!(pub(super) $kernel_name(
    inputs_matrix: PtrAndStride<BF>,
    outputs_matrix: MutPtrAndStride<BF>,
    transposed_monomials: bool,
    log_n: i32,
    num_cols_per_coset: i32,
    log_cosets_in_tile: i32,
        ));
    };
}

// 2-pass evals to monomials
evals_to_monomials_final!(ab_evals_to_monomials_last_14_stages_kernel);

// 3-pass evals to monomials
evals_to_monomials_final!(ab_evals_to_monomials_final_5_stages_kernel);
evals_to_monomials_final!(ab_evals_to_monomials_final_6_stages_kernel);
evals_to_monomials_final!(ab_evals_to_monomials_final_7_stages_kernel);
evals_to_monomials_final!(ab_evals_to_monomials_final_8_stages_kernel);

cuda_kernel_signature_and_arguments!(
    pub(super) LdeFusedWriteback,
    scratch_matrix: MutPtrAndStride<BF>,
    outputs_matrix: MutPtrAndStride<BF>,
    log_n: i32,
    coset_index_base: i32,
    coset_factor_shift: i32,
    num_cols_per_coset: i32,
    log_cosets_in_tile: i32,
);
pub(super) struct LdeFusedWritebackFunction(pub(super) LdeFusedWritebackSignature);
impl era_cudart::execution::KernelFunction for LdeFusedWritebackFunction {
    type Signature = LdeFusedWritebackSignature;
    fn as_ptr(&self) -> *const std::os::raw::c_void {
        self.0 as *const std::os::raw::c_void
    }
}
macro_rules! lde_fused_writeback {
    ($kernel_name:ident) => {
        ::era_cudart::cuda_kernel_declaration!(pub(super) $kernel_name(
    scratch_matrix: MutPtrAndStride<BF>,
    outputs_matrix: MutPtrAndStride<BF>,
    log_n: i32,
    coset_index_base: i32,
    coset_factor_shift: i32,
    num_cols_per_coset: i32,
    log_cosets_in_tile: i32,
        ));
    };
}

// Fused hypercube-iNTT-final + monomial writeback + coset-scale +
// forward-initial (transposed path, first coset of a column)
lde_fused_writeback!(ab_lde_fused_boundary_writeback_5_stages_kernel);
lde_fused_writeback!(ab_lde_fused_boundary_writeback_6_stages_kernel);
lde_fused_writeback!(ab_lde_fused_boundary_writeback_7_stages_kernel);
lde_fused_writeback!(ab_lde_fused_boundary_writeback_8_stages_kernel);

cuda_kernel_signature_and_arguments!(
    pub(super) MonomialsToEvalsInitial,
    inputs_matrix: PtrAndStride<BF>,
    outputs_matrix: MutPtrAndStride<BF>,
    transposed_monomials: bool,
    log_n: i32,
    coset_factor_power: i32,
);
pub(super) struct MonomialsToEvalsInitialFunction(pub(super) MonomialsToEvalsInitialSignature);
impl era_cudart::execution::KernelFunction for MonomialsToEvalsInitialFunction {
    type Signature = MonomialsToEvalsInitialSignature;
    fn as_ptr(&self) -> *const std::os::raw::c_void {
        self.0 as *const std::os::raw::c_void
    }
}
macro_rules! monomials_to_evals_initial {
    ($kernel_name:ident) => {
        ::era_cudart::cuda_kernel_declaration!(pub(super) $kernel_name(
    inputs_matrix: PtrAndStride<BF>,
    outputs_matrix: MutPtrAndStride<BF>,
    transposed_monomials: bool,
    log_n: i32,
    coset_factor_power: i32,
        ));
    };
}

// 2-pass monomials to evals
monomials_to_evals_initial!(ab_monomials_to_evals_first_14_stages_kernel);

// 3-pass monomials to evals initial kernels are registered below alongside
// the rest of the multi-coset MonomialsToEvalsCompact family.

// Compact 1-pass (all-stages-in-block) monomials to evals for log_n in [4, 12].
// These kernels consume the multi-coset signature: gridDim.x packs
// (col_tile, coset_in_tile, intra_block=0); the kernel decomposes blockIdx.x
// to recover (coset, col) and computes `coset_factor_power` from
// `coset_index_base + coset_in_tile`.
cuda_kernel_signature_and_arguments!(
    pub(super) MonomialsToEvalsCompact,
    inputs_matrix: PtrAndStride<BF>,
    outputs_matrix: MutPtrAndStride<BF>,
    transposed_monomials: bool,
    log_n: i32,
    coset_index_base: i32,
    coset_factor_shift: i32,
    num_cols_per_coset: i32,
    log_cosets_in_tile: i32,
);
pub(super) struct MonomialsToEvalsCompactFunction(pub(super) MonomialsToEvalsCompactSignature);
impl era_cudart::execution::KernelFunction for MonomialsToEvalsCompactFunction {
    type Signature = MonomialsToEvalsCompactSignature;
    fn as_ptr(&self) -> *const std::os::raw::c_void {
        self.0 as *const std::os::raw::c_void
    }
}
macro_rules! monomials_to_evals_compact {
    ($kernel_name:ident) => {
        ::era_cudart::cuda_kernel_declaration!(pub(super) $kernel_name(
    inputs_matrix: PtrAndStride<BF>,
    outputs_matrix: MutPtrAndStride<BF>,
    transposed_monomials: bool,
    log_n: i32,
    coset_index_base: i32,
    coset_factor_shift: i32,
    num_cols_per_coset: i32,
    log_cosets_in_tile: i32,
        ));
    };
}

monomials_to_evals_compact!(ab_monomials_to_evals_all_4_stages_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_all_5_stages_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_all_6_stages_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_all_7_stages_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_all_8_stages_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_all_9_stages_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_all_10_stages_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_all_11_stages_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_all_12_stages_kernel);

// Smem-packed multi-NTT-per-block 1-pass kernels for log_n in [6, 8]: each
// block holds `1 << LOG_IPB` independent NTT instances so a 256-thread block
// stays fully utilized through the butterfly stages. Same MonomialsToEvalsCompact
// signature as the compact 1-pass kernels (multi-coset args are reused; the
// kernel internally re-decomposes blockIdx.x to (col, coset_in_tile) packed
// IPB-at-a-time).
monomials_to_evals_compact!(ab_monomials_to_evals_smem_packed_6_stages_ipb3_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_smem_packed_7_stages_ipb2_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_smem_packed_8_stages_ipb1_kernel);

// Sub-warp register-resident multi-NTT-per-block 1-pass kernels for log_n in
// [1, 5]: each thread holds one element in a register; the butterfly exchange
// uses `__shfl_xor_sync` instead of smem. Same MonomialsToEvalsCompact signature.
monomials_to_evals_compact!(ab_monomials_to_evals_subwarp_1_stages_ipb7_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_subwarp_2_stages_ipb6_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_subwarp_3_stages_ipb5_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_subwarp_4_stages_ipb4_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_subwarp_5_stages_ipb3_kernel);
// IPB=1 variants for log_n in [1, 3] cover workloads below IPB_max where the
// strategy can't fall back to compact 1-pass (which only exists for log_n >= 4).
monomials_to_evals_compact!(ab_monomials_to_evals_subwarp_1_stages_ipb0_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_subwarp_2_stages_ipb0_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_subwarp_3_stages_ipb0_kernel);

// 3-pass monomials to evals: initial kernels share the multi-coset
// MonomialsToEvalsCompact signature so the 3-pass dispatcher can fold the
// coset axis into gridDim.x.
monomials_to_evals_compact!(ab_monomials_to_evals_initial_5_stages_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_initial_6_stages_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_initial_7_stages_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_initial_8_stages_kernel);

// 2-pass first-K-stages compact kernels for log_n in [13, 20]. Pass 1 does the
// first K = log_n - 8 butterfly stages per chunk of 2^K bitreversed inputs;
// pass 2 is the existing noninitial_8 starting at start_stage = K. Multi-coset
// signature shared with the compact 1-pass kernels.
monomials_to_evals_compact!(ab_monomials_to_evals_first_5_stages_compact_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_first_6_stages_compact_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_first_7_stages_compact_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_first_8_stages_compact_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_first_9_stages_compact_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_first_10_stages_compact_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_first_11_stages_compact_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_first_12_stages_compact_kernel);

cuda_kernel_signature_and_arguments!(
    pub(super) LdeIntermediate,
    inputs_matrix: PtrAndStride<BF>,
    outputs_matrix: MutPtrAndStride<BF>,
    log_n: u32,
    coset_index_base: u32,
    coset_factor_shift: u32,
    num_cols_per_coset: u32,
    num_cosets_in_tile: u32,
);
pub(super) struct LdeIntermediateFunction(pub(super) LdeIntermediateSignature);
impl era_cudart::execution::KernelFunction for LdeIntermediateFunction {
    type Signature = LdeIntermediateSignature;
    fn as_ptr(&self) -> *const std::os::raw::c_void {
        self.0 as *const std::os::raw::c_void
    }
}
macro_rules! lde_intermediate {
    ($kernel_name:ident) => {
        ::era_cudart::cuda_kernel_declaration!(pub(super) $kernel_name(
    inputs_matrix: PtrAndStride<BF>,
    outputs_matrix: MutPtrAndStride<BF>,
    log_n: u32,
    coset_index_base: u32,
    coset_factor_shift: u32,
    num_cols_per_coset: u32,
    num_cosets_in_tile: u32,
        ));
    };
}

lde_intermediate!(ab_lde_first_10_stages_kernel);
lde_intermediate!(ab_lde_first_9_stages_kernel);
lde_intermediate!(ab_lde_first_8_stages_kernel);
lde_intermediate!(ab_lde_first_7_stages_kernel);
lde_intermediate!(ab_lde_first_6_stages_kernel);
