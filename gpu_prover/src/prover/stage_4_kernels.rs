use crate::device_structures::{
    DeviceMatrixChunk, DeviceMatrixChunkImpl, DeviceMatrixChunkMutImpl, MutPtrAndStride,
    PtrAndStride,
};
use crate::field::{BaseField, Ext2Field, Ext4Field};
use crate::ops_complex::BatchInv;
use crate::prover::arg_utils::{get_grand_product_col, StateLinkageConstraints};
use crate::utils::WARP_SIZE;

use cs::one_row_compiler::CompiledCircuitArtifact;
use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::{DeviceSlice, DeviceVariable};
use era_cudart::stream::CudaStream;
use fft::materialize_powers_serial_starting_with_one;
use field::{Field, FieldExtension};
use prover::prover_stages::cached_data::ProverCachedData;
use std::alloc::Global;

type BF = BaseField;
type E2 = Ext2Field;
type E4 = Ext4Field;

// There's nothing wrong with tweaking these, within reason.
// Their purpose is to double-check our understanding of current circuits.
const MAX_WITNESS_COLS: usize = 672;
const MAX_MEMORY_COLS: usize = 256;
const NUM_STATE_LINKAGE_CONSTRAINTS: usize = 2;
const MAX_LAZY_INIT_TEARDOWN_SETS: usize = 16;

const DOES_NOT_NEED_Z_OMEGA: u32 = u32::MAX;

cuda_kernel!(
    DeepDenomAtZ,
    deep_denom_at_z,
    denom_at_z: *mut E4,
    z: *const E4,
    log_n: u32,
    bit_reversed: bool,
);

deep_denom_at_z!(deep_denom_at_z_kernel);

pub fn compute_deep_denom_at_z_on_main_domain(
    denom_at_z: &mut DeviceSlice<E4>,
    d_z: &DeviceVariable<E4>,
    log_n: u32,
    bit_reversed: bool,
    stream: &CudaStream,
) -> CudaResult<()> {
    let inv_batch: u32 = <E4 as BatchInv>::BATCH_SIZE;
    let n = 1 << log_n;
    assert_eq!(denom_at_z.len(), n as usize);
    let denom_at_z = denom_at_z.as_mut_ptr();
    let z = d_z.as_ptr();
    let block_dim = WARP_SIZE * 4;
    let grid_dim = (n + inv_batch * block_dim - 1) / (inv_batch * block_dim);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = DeepDenomAtZArguments::new(denom_at_z, z, log_n, bit_reversed);
    DeepDenomAtZFunction(deep_denom_at_z_kernel).launch(&config, &args)
}

// Clone but not Copy, I'd rather know explicitly when it's being cloned.
#[derive(Clone)]
#[repr(C)]
pub struct ColIdxsToChallengeIdxsMap {
    // these could be u16, but there's no need to economize,
    // args fit comfortably in < 8KB regardless
    pub map: [u32; MAX_MEMORY_COLS],
}

#[derive(Clone, Default)]
#[repr(C)]
pub(super) struct ChallengesTimesEvalsSums {
    at_z_sum_neg: E4,
    at_z_omega_sum_neg: E4,
}

cuda_kernel!(
    DeepQuotient,
    deep_quotient,
    setup_cols: PtrAndStride<BF>,
    witness_cols: PtrAndStride<BF>,
    memory_cols: PtrAndStride<BF>,
    stage_2_bf_cols: PtrAndStride<BF>,
    stage_2_e4_cols: PtrAndStride<BF>,
    composition_col: PtrAndStride<BF>,
    denom_at_z: *const E4,
    setup_challenges_at_z: *const E4,
    witness_challenges_at_z: *const E4,
    memory_challenges_at_z: *const E4,
    stage_2_bf_challenges_at_z: *const E4,
    stage_2_e4_challenges_at_z: *const E4,
    composition_challenge_at_z: *const E4,
    state_linkage_constraints: StateLinkageConstraints,
    memory_cols_to_challenges_at_z_omega_map: ColIdxsToChallengeIdxsMap,
    witness_challenges_at_z_omega: *const E4,
    memory_challenges_at_z_omega: *const E4,
    grand_product_challenge_at_z_omega: *const E4,
    challenges_times_evals_sums: *const ChallengesTimesEvalsSums,
    quotient: MutPtrAndStride<BF>,
    num_setup_cols: u32,
    num_witness_cols: u32,
    num_memory_cols: u32,
    num_stage_2_bf_cols: u32,
    num_stage_2_e4_cols: u32,
    stage_2_memory_grand_product_offset: u32,
    log_n: u32,
    bit_reversed: bool,
);

deep_quotient!(deep_quotient_kernel);

pub(super) fn prepare_challenges_for_gpu_transfer(
    evals: &[E4],
    alpha: E4,
    omega_inv: E2,
    num_terms_at_z: usize,
    num_terms_at_z_omega: usize,
    scratch_e4: &mut [E4],
    challenges_times_evals_sums: &mut ChallengesTimesEvalsSums,
) {
    let num_terms_total = num_terms_at_z + num_terms_at_z_omega;
    assert_eq!(num_terms_total, evals.len());
    assert_eq!(num_terms_total, scratch_e4.len());
    let mut challenges =
        materialize_powers_serial_starting_with_one::<_, Global>(alpha, num_terms_total);
    // Fold omega adjustment into challenges at z * omega
    for challenge in (&mut challenges[num_terms_at_z..]).iter_mut() {
        challenge.mul_assign_by_base(&omega_inv);
    }
    // accumulate challenges * evals at z
    let challenges_at_z = &challenges[0..num_terms_at_z];
    let evals_at_z = &evals[0..num_terms_at_z];
    let challenges_times_evals_at_z_sum_neg = *challenges_at_z
        .iter()
        .zip(evals_at_z)
        .fold(E4::ZERO, |acc, (challenge, eval)| {
            *acc.clone().add_assign(challenge.clone().mul_assign(&eval))
        })
        .negate();
    // accumulate challenges * evals at z * omega
    let challenges_at_z_omega = &challenges[num_terms_at_z..];
    let evals_at_z_omega = &evals[num_terms_at_z..];
    let challenges_times_evals_at_z_omega_sum_neg = *challenges_at_z_omega
        .iter()
        .zip(evals_at_z_omega)
        .fold(E4::ZERO, |acc, (challenge, eval)| {
            *acc.clone().add_assign(challenge.clone().mul_assign(&eval))
        })
        .negate();
    (&mut scratch_e4[..num_terms_total]).copy_from_slice(&challenges);
    *challenges_times_evals_sums = ChallengesTimesEvalsSums {
        at_z_sum_neg: challenges_times_evals_at_z_sum_neg,
        at_z_omega_sum_neg: challenges_times_evals_at_z_omega_sum_neg,
    };
}

pub fn compute_deep_quotient_on_main_domain(
    setup_cols: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    witness_cols: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    memory_cols: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    stage_2_cols: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    composition_col: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    denom_at_z: &DeviceSlice<E4>,
    scratch_e4: &DeviceSlice<E4>,
    challenges_times_evals_sums: &DeviceVariable<ChallengesTimesEvalsSums>,
    quotient: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    cached_data: &ProverCachedData,
    circuit: &CompiledCircuitArtifact<BF>,
    log_n: u32,
    bit_reversed: bool,
    stream: &CudaStream,
) -> CudaResult<()> {
    let n = 1 << log_n;
    let num_setup_cols = circuit.setup_layout.total_width;
    let num_witness_cols = circuit.witness_layout.total_width;
    assert!(num_witness_cols <= MAX_WITNESS_COLS);
    let num_memory_cols = circuit.memory_layout.total_width;
    assert!(num_memory_cols <= MAX_MEMORY_COLS);
    let num_stage_2_bf_cols = circuit.stage_2_layout.num_base_field_polys();
    let num_stage_2_e4_cols = circuit.stage_2_layout.num_ext4_field_polys();
    assert_eq!(setup_cols.rows(), n);
    assert_eq!(setup_cols.cols(), num_setup_cols,);
    assert_eq!(witness_cols.rows(), n);
    assert_eq!(witness_cols.cols(), num_witness_cols,);
    assert_eq!(memory_cols.rows(), n);
    assert_eq!(memory_cols.cols(), num_memory_cols,);
    assert_eq!(composition_col.rows(), n);
    assert_eq!(composition_col.cols(), 4);
    assert_eq!(quotient.rows(), n);
    assert_eq!(quotient.cols(), 4);
    assert_eq!(stage_2_cols.rows(), n);
    assert_eq!(stage_2_cols.cols(), circuit.stage_2_layout.total_width);
    assert_eq!(
        stage_2_cols.cols(),
        4 * (((num_stage_2_bf_cols + 3) / 4) + num_stage_2_e4_cols)
    );
    // for convenience, demarcate bf and vectorized e4 sections of stage_2_cols
    let e4_cols_offset = circuit.stage_2_layout.ext4_polys_offset;
    assert_eq!(e4_cols_offset % 4, 0);
    assert!(num_stage_2_bf_cols <= e4_cols_offset);
    assert!(e4_cols_offset - num_stage_2_bf_cols < 4);
    // the above should also suffice to show e4_cols_offset = 4 * ceil(num_stage_2_bf_cols / 4)
    // which implies stage_2_cols.cols() = e4_cols_offset + num_stage_2_e4_cols
    let (stage_2_bf_cols, stage_2_e4_cols) = {
        let stride = stage_2_cols.stride();
        let offset = stage_2_cols.offset();
        let slice = stage_2_cols.slice();
        let (bf_slice, e4_slice) = slice.split_at(e4_cols_offset * stride);
        (
            DeviceMatrixChunk::new(
                &bf_slice[0..num_stage_2_bf_cols * stride],
                stride,
                offset,
                n,
            ),
            DeviceMatrixChunk::new(e4_slice, stride, offset, n),
        )
    };
    if cached_data.process_shuffle_ram_init {
        assert_eq!(
            circuit.state_linkage_constraints.len(),
            NUM_STATE_LINKAGE_CONSTRAINTS
        );
    } else {
        assert_eq!(circuit.state_linkage_constraints.len(), 0);
    }
    let num_witness_terms_at_z_omega = circuit.state_linkage_constraints.len();
    let state_linkage_constraints = StateLinkageConstraints::new(circuit);
    let mut memory_cols_to_challenges_at_z_omega_map = ColIdxsToChallengeIdxsMap {
        map: [DOES_NOT_NEED_Z_OMEGA; MAX_MEMORY_COLS],
    };
    let mut num_memory_terms_at_z_omega: usize = 0;
    if cached_data.process_shuffle_ram_init {
        assert!(cached_data.shuffle_ram_inits_and_teardowns.len() > 0);
        assert!(cached_data.shuffle_ram_inits_and_teardowns.len() <= MAX_LAZY_INIT_TEARDOWN_SETS);
        for init_and_teardown in cached_data.shuffle_ram_inits_and_teardowns.iter() {
            let start = init_and_teardown.lazy_init_addresses_columns.start();
            memory_cols_to_challenges_at_z_omega_map.map[start] =
                num_memory_terms_at_z_omega as u32;
            num_memory_terms_at_z_omega += 1;
            memory_cols_to_challenges_at_z_omega_map.map[start + 1] =
                num_memory_terms_at_z_omega as u32;
            num_memory_terms_at_z_omega += 1;
        }
    } else {
        assert_eq!(cached_data.shuffle_ram_inits_and_teardowns.len(), 0);
    }
    // double-check number of terms at z
    let num_terms_at_z = circuit.num_openings_at_z();
    let mut num_terms_at_z_doublecheck = num_setup_cols;
    num_terms_at_z_doublecheck += num_witness_cols;
    num_terms_at_z_doublecheck += num_memory_cols;
    num_terms_at_z_doublecheck += num_stage_2_bf_cols;
    num_terms_at_z_doublecheck += num_stage_2_e4_cols;
    num_terms_at_z_doublecheck += 1; // composition quotient
    assert_eq!(num_terms_at_z, num_terms_at_z_doublecheck);
    // double-check number of terms at z * omega
    let num_terms_at_z_omega = circuit.num_openings_at_z_omega();
    let mut num_terms_at_z_omega_doublecheck = num_witness_terms_at_z_omega;
    num_terms_at_z_omega_doublecheck += num_memory_terms_at_z_omega;
    num_terms_at_z_omega_doublecheck += 1; // grand product
    assert_eq!(num_terms_at_z_omega, num_terms_at_z_omega_doublecheck);
    // double-check number of challenges passed by the caller
    let num_terms_total = num_terms_at_z + num_terms_at_z_omega;
    assert_eq!(num_terms_total, scratch_e4.len());
    // prepare data matrix args
    let stage_2_memory_grand_product_offset = get_grand_product_col(circuit);
    let setup_cols = setup_cols.as_ptr_and_stride();
    let witness_cols = witness_cols.as_ptr_and_stride();
    let memory_cols = memory_cols.as_ptr_and_stride();
    let stage_2_bf_cols = stage_2_bf_cols.as_ptr_and_stride();
    let stage_2_e4_cols = stage_2_e4_cols.as_ptr_and_stride();
    let composition_col = composition_col.as_ptr_and_stride();
    let denom_at_z = denom_at_z.as_ptr();
    // prepare challenges for each matrix
    let (setup_challenges_at_z, rest) = scratch_e4.split_at(num_setup_cols);
    let (witness_challenges_at_z, rest) = rest.split_at(num_witness_cols);
    let (memory_challenges_at_z, rest) = rest.split_at(num_memory_cols);
    let (stage_2_bf_challenges_at_z, rest) = rest.split_at(num_stage_2_bf_cols);
    let (stage_2_e4_challenges_at_z, rest) = rest.split_at(num_stage_2_e4_cols);
    let (composition_challenge_at_z, rest) = rest.split_at(1);
    let (witness_challenges_at_z_omega, rest) = rest.split_at(num_witness_terms_at_z_omega);
    let (memory_challenges_at_z_omega, rest) = rest.split_at(num_memory_terms_at_z_omega);
    let (grand_product_challenge_at_z_omega, rest) = rest.split_at(1);
    assert_eq!(rest.len(), 0);
    let setup_challenges_at_z = setup_challenges_at_z.as_ptr();
    let witness_challenges_at_z = witness_challenges_at_z.as_ptr();
    let memory_challenges_at_z = memory_challenges_at_z.as_ptr();
    let stage_2_bf_challenges_at_z = stage_2_bf_challenges_at_z.as_ptr();
    let stage_2_e4_challenges_at_z = stage_2_e4_challenges_at_z.as_ptr();
    let composition_challenge_at_z = composition_challenge_at_z.as_ptr();
    let witness_challenges_at_z_omega = witness_challenges_at_z_omega.as_ptr();
    let memory_challenges_at_z_omega = memory_challenges_at_z_omega.as_ptr();
    let grand_product_challenge_at_z_omega = grand_product_challenge_at_z_omega.as_ptr();
    let challenges_times_evals_sums = challenges_times_evals_sums.as_ptr();
    let quotient = quotient.as_mut_ptr_and_stride();
    // denom at z * omega loads are offset by 16B.
    // A wide block modestly amortizes the unaligned loads.
    let block_dim = 512;
    let grid_dim = (n + block_dim - 1) / block_dim;
    let config = CudaLaunchConfig::basic(grid_dim as u32, block_dim as u32, stream);
    let args = DeepQuotientArguments::new(
        setup_cols,
        witness_cols,
        memory_cols,
        stage_2_bf_cols,
        stage_2_e4_cols,
        composition_col,
        denom_at_z,
        setup_challenges_at_z,
        witness_challenges_at_z,
        memory_challenges_at_z,
        stage_2_bf_challenges_at_z,
        stage_2_e4_challenges_at_z,
        composition_challenge_at_z,
        state_linkage_constraints,
        memory_cols_to_challenges_at_z_omega_map,
        witness_challenges_at_z_omega,
        memory_challenges_at_z_omega,
        grand_product_challenge_at_z_omega,
        challenges_times_evals_sums,
        quotient,
        num_setup_cols as u32,
        num_witness_cols as u32,
        num_memory_cols as u32,
        num_stage_2_bf_cols as u32,
        num_stage_2_e4_cols as u32,
        stage_2_memory_grand_product_offset as u32,
        log_n,
        bit_reversed,
    );
    DeepQuotientFunction(deep_quotient_kernel).launch(&config, &args)
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::context::Context;
    use crate::device_structures::DeviceMatrixMut;
    use crate::ops_complex::bit_reverse_in_place;

    use era_cudart::memory::{
        memory_copy_async, CudaHostAllocFlags, DeviceAllocation, HostAllocation,
    };
    use field::Field;
    use prover::tests::{run_basic_delegation_test_impl, run_keccak_test_impl, GpuComparisonArgs};
    use serial_test::serial;

    type BF = BaseField;
    type E4 = Ext4Field;

    fn comparison_hook(gpu_comparison_args: &GpuComparisonArgs) {
        let GpuComparisonArgs {
            circuit,
            setup,
            external_values,
            public_inputs: _,
            twiddles,
            lde_precomputations: _,
            table_driver: _,
            lookup_mapping: _,
            log_n,
            circuit_sequence,
            delegation_processing_type,
            prover_data,
        } = gpu_comparison_args;
        let log_n = *log_n;
        let circuit_sequence = *circuit_sequence;
        let delegation_processing_type = delegation_processing_type.unwrap_or(0);
        let domain_size = 1 << log_n;

        let cached_data = ProverCachedData::new(
            &circuit,
            &external_values.challenges,
            domain_size,
            circuit_sequence,
            delegation_processing_type,
        );

        let evals = &prover_data.deep_poly_result.values_at_z;
        let z = prover_data.deep_poly_result.z;
        let alpha = prover_data.deep_poly_result.alpha;
        // Repackage row-major data as column-major for GPU
        let range = 0..domain_size;
        let domain_index = 0;
        let mut trace_view = prover_data.stage_1_result.ldes[domain_index]
            .trace
            .row_view(range.clone());
        let mut stage_2_trace_view = prover_data.stage_2_result.ldes[domain_index]
            .trace
            .row_view(range.clone());
        let mut setup_trace_view = setup.ldes[domain_index].trace.row_view(range.clone());
        let mut quotient_trace_view = prover_data.quotient_commitment_result.ldes[domain_index]
            .trace
            .row_view(range.clone());
        let num_setup_cols = circuit.setup_layout.total_width;
        let num_witness_cols = circuit.witness_layout.total_width;
        let num_memory_cols = circuit.memory_layout.total_width;
        let num_trace_cols = num_witness_cols + num_memory_cols;
        let num_stage_2_cols = circuit.stage_2_layout.total_width;
        // let num_stage_2_bf_cols = circuit.stage_2_layout.num_base_field_polys();
        // let num_stage_2_e4_cols = circuit.stage_2_layout.num_ext4_field_polys();
        let mut h_setup_cols: Vec<BF> = vec![BF::ZERO; domain_size * num_setup_cols];
        let mut h_trace_cols: Vec<BF> = vec![BF::ZERO; domain_size * num_trace_cols];
        let mut h_stage_2_cols: Vec<BF> = vec![BF::ZERO; domain_size * num_stage_2_cols];
        let mut h_composition_col: Vec<BF> = vec![BF::ZERO; 4 * domain_size];
        // imitating access patterns in zksync_airbender's prover_stages/stage4.rs
        unsafe {
            for i in 0..domain_size {
                let setup_trace_view_row = setup_trace_view.current_row_ref();
                let trace_view_row = trace_view.current_row_ref();
                let stage_2_trace_view_row = stage_2_trace_view.current_row_ref();
                let quotient_trace_view_row = quotient_trace_view.current_row_ref();
                {
                    let mut src = setup_trace_view_row.as_ptr();
                    for j in 0..num_setup_cols {
                        h_setup_cols[i + j * domain_size] = src.read();
                        src = src.add(1);
                    }
                }
                {
                    let mut src = trace_view_row.as_ptr();
                    for j in 0..num_trace_cols {
                        h_trace_cols[i + j * domain_size] = src.read();
                        src = src.add(1);
                    }
                }
                {
                    let mut src = stage_2_trace_view_row.as_ptr();
                    for j in 0..num_stage_2_cols {
                        h_stage_2_cols[i + j * domain_size] = src.read();
                        src = src.add(1);
                    }
                }
                {
                    let src = quotient_trace_view_row.as_ptr().cast::<E4>();
                    assert!(src.is_aligned());
                    let coeffs = src.read().into_coeffs_in_base();
                    for (j, coeff) in coeffs.iter().enumerate() {
                        h_composition_col[i + j * domain_size] = *coeff;
                    }
                }
                setup_trace_view.advance_row();
                trace_view.advance_row();
                stage_2_trace_view.advance_row();
                quotient_trace_view.advance_row();
            }
        }
        // Allocate GPU args
        let stream = CudaStream::default();
        let mut d_alloc_setup_cols =
            DeviceAllocation::<BF>::alloc(domain_size * num_setup_cols).unwrap();
        let mut d_alloc_trace_cols =
            DeviceAllocation::<BF>::alloc(domain_size * num_trace_cols).unwrap();
        let mut d_alloc_stage_2_cols =
            DeviceAllocation::<BF>::alloc(domain_size * num_stage_2_cols).unwrap();
        let mut d_alloc_composition_col = DeviceAllocation::<BF>::alloc(4 * domain_size).unwrap();
        let mut d_z = DeviceAllocation::<E4>::alloc(1).unwrap();
        let mut d_denom_at_z = DeviceAllocation::<E4>::alloc(domain_size).unwrap();
        let num_terms_at_z = circuit.num_openings_at_z();
        let num_terms_at_z_omega = circuit.num_openings_at_z_omega();
        let num_terms_total = num_terms_at_z + num_terms_at_z_omega;
        // TODO: In practice, we should also experiment with CudaHostAllocFlags::WRITE_COMBINED
        let mut h_e4_scratch =
            HostAllocation::<E4>::alloc(num_terms_total, CudaHostAllocFlags::DEFAULT).unwrap();
        let mut d_e4_scratch = DeviceAllocation::<E4>::alloc(num_terms_total).unwrap();
        let mut d_alloc_quotient = DeviceAllocation::<BF>::alloc(4 * domain_size).unwrap();
        let mut h_quotient =
            HostAllocation::<BF>::alloc(4 * domain_size, CudaHostAllocFlags::DEFAULT).unwrap();
        memory_copy_async(&mut d_alloc_setup_cols, &h_setup_cols, &stream).unwrap();
        memory_copy_async(&mut d_alloc_trace_cols, &h_trace_cols, &stream).unwrap();
        memory_copy_async(&mut d_alloc_stage_2_cols, &h_stage_2_cols, &stream).unwrap();
        memory_copy_async(&mut d_alloc_composition_col, &h_composition_col, &stream).unwrap();
        memory_copy_async(&mut d_z, &[z], &stream).unwrap();
        let mut d_setup_cols = DeviceMatrixMut::new(&mut d_alloc_setup_cols, domain_size);
        let mut d_trace_cols = DeviceMatrixMut::new(&mut d_alloc_trace_cols, domain_size);
        let mut d_stage_2_cols = DeviceMatrixMut::new(&mut d_alloc_stage_2_cols, domain_size);
        let mut d_composition_col = DeviceMatrixMut::new(&mut d_alloc_composition_col, domain_size);
        let mut d_quotient = DeviceMatrixMut::new(&mut d_alloc_quotient, domain_size);
        for &bit_reversed in [false, true].iter() {
            if bit_reversed {
                bit_reverse_in_place(&mut d_setup_cols, &stream).unwrap();
                bit_reverse_in_place(&mut d_trace_cols, &stream).unwrap();
                bit_reverse_in_place(&mut d_stage_2_cols, &stream).unwrap();
                bit_reverse_in_place(&mut d_composition_col, &stream).unwrap();
            }
            compute_deep_denom_at_z_on_main_domain(
                &mut d_denom_at_z,
                &d_z[0],
                log_n as u32,
                bit_reversed,
                &stream,
            )
            .unwrap();
            let mut h_challenges_times_evals_sums = ChallengesTimesEvalsSums::default();
            prepare_challenges_for_gpu_transfer(
                evals,
                alpha,
                twiddles.omega_inv,
                num_terms_at_z,
                num_terms_at_z_omega,
                &mut h_e4_scratch,
                &mut h_challenges_times_evals_sums,
            );
            let mut d_challenges_times_evals_sums =
                DeviceAllocation::<ChallengesTimesEvalsSums>::alloc(1).unwrap();
            memory_copy_async(&mut d_e4_scratch, &h_e4_scratch, &stream).unwrap();
            memory_copy_async(
                &mut d_challenges_times_evals_sums,
                &[h_challenges_times_evals_sums],
                &stream,
            )
            .unwrap();
            let slice = d_trace_cols.slice();
            let stride = d_trace_cols.stride();
            let offset = d_trace_cols.offset();
            let d_witness_cols = DeviceMatrixChunk::new(
                &slice[0..num_witness_cols * stride],
                stride,
                offset,
                domain_size,
            );
            let d_memory_cols = DeviceMatrixChunk::new(
                &slice[num_witness_cols * stride..],
                stride,
                offset,
                domain_size,
            );
            compute_deep_quotient_on_main_domain(
                &d_setup_cols,
                &d_witness_cols,
                &d_memory_cols,
                &d_stage_2_cols,
                &d_composition_col,
                &d_denom_at_z,
                &d_e4_scratch,
                &d_challenges_times_evals_sums[0],
                &mut d_quotient,
                &cached_data,
                &circuit,
                log_n as u32,
                bit_reversed,
                &stream,
            )
            .unwrap();
            // zksync_airbender's CPU results are bitreversed.
            // If our results are not bitreversed, we need to bitrev to match.
            if !bit_reversed {
                bit_reverse_in_place(&mut d_quotient, &stream).unwrap();
            }
            memory_copy_async(&mut h_quotient, d_quotient.slice(), &stream).unwrap();
            stream.synchronize().unwrap();
            unsafe {
                let cpu_deep_trace_ptr = prover_data.deep_poly_result.ldes[domain_index]
                    .trace
                    .ptr
                    .cast::<E4>();
                assert!(cpu_deep_trace_ptr.is_aligned());
                for i in 0..domain_size {
                    let coeffs: [BF; 4] = std::array::from_fn(|j| h_quotient[i + j * domain_size]);
                    assert_eq!(
                        E4::from_array_of_base(coeffs),
                        cpu_deep_trace_ptr.add(i).read(),
                        "bit_reversed = {}, i = {}",
                        bit_reversed,
                        i,
                    );
                }
            }
        }
    }

    #[test]
    #[serial]
    fn test_stage_4_for_main_and_blake() {
        let ctx = Context::create(12).unwrap();
        run_basic_delegation_test_impl(
            Some(Box::new(comparison_hook)),
            Some(Box::new(comparison_hook)),
        );
        ctx.destroy().unwrap();
    }

    #[test]
    #[serial]
    #[ignore]
    fn test_stage_4_for_main_and_keccak() {
        let ctx = Context::create(12).unwrap();
        run_keccak_test_impl(
            Some(Box::new(comparison_hook)),
            Some(Box::new(comparison_hook)),
        );
        ctx.destroy().unwrap();
    }
}
