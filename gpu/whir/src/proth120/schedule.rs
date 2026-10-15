use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::{DeviceSlice, DeviceVariable};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::device_tracing::Range;
use gpu_core::primitives::field::PR;
use gpu_gkr::gkr_ops::assemble_query_indexes;
use gpu_gkr::setup::proth120::PackedSetupSource;
use gpu_hash::keccak256::{
    keccak256_pow, transcript_commit_fields, transcript_draw_fields, transcript_draw_u32,
};
use gpu_ntt::proth120::{update_eq_poly, EqSample};
use gpu_ops::powers::get_powers_by_ref;
use gpu_prover_context::ProverContext;
use gpu_trace::trace::packed::PackedCosetRecomputeOracle;

use super::commit::{schedule_commit_intermediate, IntermediateOracle};
use super::openings::schedule_open_intermediate;
use super::outputs::{
    schedule_readback_and_assemble, L1WhirProofDevice, L1WhirProofHost, L1WhirScheduled,
};
use super::shape::L1WhirShape;
use super::state::{
    schedule_accumulate_base, schedule_batched_opening, schedule_eq_from_point,
    schedule_fold_state, schedule_monomial_eval, schedule_monomials, schedule_round_update,
    schedule_three_point, L1WhirState,
};
use crate::upstream::{domain_generator_for_size, WhirSchedule};

pub(crate) fn query_words(queries: usize, query_domain_log2: u32) -> usize {
    ((queries * query_domain_log2 as usize).div_ceil(32) + 1).next_multiple_of(8)
}

pub(crate) fn schedule_pow_and_query_indexes(
    seed: &mut DeviceSlice<u8>,
    queries: usize,
    pow_bits: u32,
    query_domain_log2: u32,
    nonce_dst: &mut DeviceVariable<u64>,
    context: &ProverContext,
) -> CudaResult<DeviceAllocation<u32>> {
    assert!(
        queries > 0 && (1..=32).contains(&query_domain_log2),
        "Proth120 WHIR: query phase geometry invalid"
    );
    let stream = context.get_exec_stream();
    keccak256_pow(seed, pow_bits, nonce_dst, stream)?;
    let mut raw = context.alloc(
        query_words(queries, query_domain_log2),
        AllocationPlacement::BestFit,
    )?;
    transcript_draw_u32(seed, &mut raw, stream)?;
    let mut indexes = context.alloc(queries, AllocationPlacement::BestFit)?;
    assemble_query_indexes(&raw, &mut indexes, query_domain_log2, stream)?;
    Ok(indexes)
}

pub(crate) fn schedule_delinearization(
    seed: &mut DeviceSlice<u8>,
    queries: usize,
    context: &ProverContext,
) -> CudaResult<DeviceAllocation<PR>> {
    let stream = context.get_exec_stream();
    let mut delta = context.alloc(1, AllocationPlacement::BestFit)?;
    transcript_draw_fields(seed, &mut delta, stream)?;
    let mut powers = context.alloc(queries + 1, AllocationPlacement::BestFit)?;
    get_powers_by_ref(
        unsafe { DeviceVariable::from_raw_parts(delta.as_ptr()) },
        1,
        &mut powers,
        stream,
    )?;
    Ok(powers)
}

pub(crate) fn schedule_eq_update(
    state: &mut L1WhirState,
    ood_point: &DeviceSlice<PR>,
    weight: &DeviceSlice<PR>,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(
        ood_point.len() == 1 && weight.len() == 1,
        "Proth120 WHIR: eq update sample lengths invalid"
    );
    let stream = context.get_exec_stream();
    let mut sample = context.alloc::<EqSample>(1, AllocationPlacement::BestFit)?;
    let slots: &mut DeviceSlice<PR> = unsafe { sample.transmute_mut() };
    memory_copy_async(&mut slots[0..1], ood_point, stream)?;
    memory_copy_async(&mut slots[1..2], weight, stream)?;
    let len = state.current_len;
    update_eq_poly(&mut state.eq[..len], &sample, &sample[..0], stream)
}

pub struct L1WhirInputs<'a> {
    pub claims: &'a DeviceSlice<PR>,
    pub base_layer_point: &'a DeviceSlice<PR>,
    pub batching_challenge: &'a DeviceSlice<PR>,
}

fn start_phase(name: String, context: &ProverContext) -> CudaResult<(String, Range)> {
    let range = Range::new(&name)?;
    range.start(context.get_exec_stream())?;
    Ok((name, range))
}

fn end_phase(
    phase: (String, Range),
    ranges: &mut Vec<(String, Range)>,
    context: &ProverContext,
) -> CudaResult<()> {
    phase.1.end(context.get_exec_stream())?;
    ranges.push(phase);
    Ok(())
}

fn validate_inputs(
    base: &PackedCosetRecomputeOracle<PR>,
    setup: &PackedSetupSource<'_>,
    seed: &DeviceSlice<u8>,
    inputs: &L1WhirInputs<'_>,
    schedule: &WhirSchedule,
    shape: &L1WhirShape,
    context: &ProverContext,
) {
    let base_cfg = base
        .config()
        .expect("Proth120 WHIR: base oracle has not been committed");
    let setup_cfg = setup
        .oracle()
        .config()
        .expect("Proth120 WHIR: setup oracle has not been committed");
    let tile_bytes = shape
        .rounds
        .iter()
        .filter_map(|round| round.oracle)
        .map(|oracle| {
            16usize
                .checked_shl(oracle.log_n + oracle.tile_cosets_log2)
                .expect("Proth120 WHIR: tile length overflow")
        })
        .max()
        .expect("Proth120 WHIR: schedule has no intermediate oracle");
    let expected = L1WhirShape::from_schedule(
        schedule,
        shape.log_message,
        base_cfg.log_lde_factor,
        base_cfg.log_values_per_leaf,
        tile_bytes,
    );
    assert!(
        shape.rounds == expected.rounds
            && shape.log_base_lde == expected.log_base_lde
            && shape.cap_log == expected.cap_log
            && shape.term_capacity == expected.term_capacity
            && shape.total_sumcheck_polys == expected.total_sumcheck_polys
            && shape.log_final == expected.log_final,
        "Proth120 WHIR: shape differs from schedule"
    );
    assert!(
        inputs.claims.len() == base.packed_columns() + setup.oracle().packed_columns(),
        "Proth120 WHIR: claims length differs from packed columns"
    );
    assert!(
        inputs.base_layer_point.len() == base.log_packed() as usize
            && base.log_packed() == shape.log_message
            && setup.oracle().log_packed() == shape.log_message,
        "Proth120 WHIR: point and packed message lengths differ"
    );
    assert!(
        seed.len() == 32 && inputs.batching_challenge.len() == 1,
        "Proth120 WHIR: seed or batching challenge length invalid"
    );
    assert!(
        base_cfg.log_values_per_leaf == shape.rounds[0].folds
            && setup_cfg.log_values_per_leaf == shape.rounds[0].folds
            && base_cfg.log_lde_factor == shape.log_base_lde
            && setup_cfg.log_lde_factor == shape.log_base_lde
            && base_cfg.cap_log == shape.cap_log
            && setup_cfg.cap_log == shape.cap_log,
        "Proth120 WHIR: base or setup commitment geometry differs from schedule"
    );
    let max_domain = shape
        .rounds
        .iter()
        .filter_map(|r| r.oracle)
        .map(|o| o.log_domain)
        .max()
        .unwrap();
    let context_log = context.proth120_ntt_device_context().log_max_domain();
    assert!(
        context_log >= max_domain,
        "Proth120 WHIR: context log_max_domain below oracle domain"
    );
}

#[allow(clippy::needless_pass_by_value)]
pub fn schedule_l1_whir_fold(
    base: &mut PackedCosetRecomputeOracle<PR>,
    setup: &mut PackedSetupSource<'_>,
    seed: &mut DeviceSlice<u8>,
    inputs: L1WhirInputs<'_>,
    schedule: &WhirSchedule,
    shape: &L1WhirShape,
    context: &ProverContext,
) -> CudaResult<L1WhirScheduled> {
    validate_inputs(base, setup, seed, &inputs, schedule, shape, context);
    let stream = context.get_exec_stream();
    let mut ranges = Vec::new();
    let memory_columns = base.packed_columns();
    let setup_columns = setup.oracle().packed_columns();
    let mut outputs = L1WhirProofDevice::new(shape, memory_columns, setup_columns, context)?;
    let mut host = L1WhirProofHost::new(shape, &outputs, memory_columns, setup_columns, context);
    let phase = start_phase("gkr.whir.pr.accumulate".to_owned(), context)?;
    memory_copy_async(&mut host.claims, inputs.claims, stream)?;
    memory_copy_async(
        &mut host.original_evaluation_point,
        inputs.base_layer_point,
        stream,
    )?;
    memory_copy_async(
        &mut host.batching_challenge,
        inputs.batching_challenge,
        stream,
    )?;
    let mut state = L1WhirState::new(shape.log_message, shape.term_capacity, context)?;
    let mut powers = context.alloc(inputs.claims.len(), AllocationPlacement::BestFit)?;
    get_powers_by_ref(
        unsafe { DeviceVariable::from_raw_parts(inputs.batching_challenge.as_ptr()) },
        0,
        &mut powers,
        stream,
    )?;
    schedule_accumulate_base(base.raw(), setup.raw(), &powers, &mut state, context)?;
    base.release_raw();
    setup.release_raw();
    schedule_monomials(&mut state, context)?;
    schedule_eq_from_point(inputs.base_layer_point, &mut state, context)?;
    schedule_batched_opening(
        &powers,
        inputs.claims,
        &mut outputs.batched_opening,
        context,
    )?;
    drop(powers);
    end_phase(phase, &mut ranges, context)?;
    let mut previous: Option<IntermediateOracle> = None;
    let mut poly_index = 0;
    let mut challenge = context.alloc(1, AllocationPlacement::BestFit)?;
    for (r, round) in shape.rounds.iter().enumerate() {
        let phase = start_phase(format!("gkr.whir.pr.round.{r}.folds"), context)?;
        if let Some(oracle) = previous.as_ref() {
            state
                .in_domain
                .start_round(oracle, state.current_len, oracle.shape.log_v, context)?;
        }
        for _ in 0..round.folds {
            schedule_three_point(&mut state, context)?;
            schedule_round_update(
                &mut state,
                seed,
                &mut outputs.sumcheck_polys[3 * poly_index..3 * (poly_index + 1)],
                &mut challenge,
                context,
            )?;
            schedule_fold_state(&mut state, &challenge, context)?;
            poly_index += 1;
        }
        let len = state.current_len;
        assert_eq!(
            len,
            1 << round.log_poly_after,
            "Proth120 WHIR: folded length differs from round"
        );
        end_phase(phase, &mut ranges, context)?;
        let phase = start_phase(format!("gkr.whir.pr.round.{r}.commit"), context)?;
        let current = if let Some(oracle_shape) = round.oracle {
            Some(schedule_commit_intermediate(
                &state.monomials,
                &oracle_shape,
                &mut outputs.intermediate[r].cap,
                seed,
                context,
            )?)
        } else {
            memory_copy_async(&mut outputs.final_monomials, &state.monomials, stream)?;
            transcript_commit_fields(seed, &outputs.final_monomials, stream)?;
            None
        };
        end_phase(phase, &mut ranges, context)?;
        let ood_point = if current.is_some() {
            let phase = start_phase(format!("gkr.whir.pr.round.{r}.ood"), context)?;
            let mut point = context.alloc(1, AllocationPlacement::BestFit)?;
            transcript_draw_fields(seed, &mut point, stream)?;
            schedule_monomial_eval(&state, &point, &mut outputs.ood_samples[r..r + 1], context)?;
            transcript_commit_fields(seed, &outputs.ood_samples[r..r + 1], stream)?;
            end_phase(phase, &mut ranges, context)?;
            Some(point)
        } else {
            None
        };
        let phase = start_phase(format!("gkr.whir.pr.round.{r}.pow"), context)?;
        let indexes = schedule_pow_and_query_indexes(
            seed,
            round.queries,
            round.pow_bits,
            round.query_domain_log2,
            unsafe { DeviceVariable::from_raw_parts_mut(outputs.pow_nonces[r..].as_mut_ptr()) },
            context,
        )?;
        let weights = if current.is_some() {
            Some(schedule_delinearization(seed, round.queries, context)?)
        } else {
            None
        };
        end_phase(phase, &mut ranges, context)?;
        let phase = start_phase(format!("gkr.whir.pr.round.{r}.openings"), context)?;
        if r == 0 {
            base.open_queries(
                &indexes,
                &mut outputs.memory.leaves,
                &mut outputs.memory.paths,
                &mut outputs.memory.tree_indexes,
                context,
            )?;
            setup.open_queries(
                &indexes,
                &mut outputs.setup.leaves,
                &mut outputs.setup.paths,
                &mut outputs.setup.tree_indexes,
                context,
            )?;
            base.release_commitment_state();
            setup.release_commitment_state();
        } else {
            schedule_open_intermediate(
                previous
                    .as_ref()
                    .expect("Proth120 WHIR: previous oracle missing"),
                &indexes,
                round.query_domain_log2,
                &mut outputs.intermediate[r - 1],
                context,
            )?;
            drop(previous.take());
        }
        end_phase(phase, &mut ranges, context)?;
        if let (Some(point), Some(weights)) = (ood_point.as_ref(), weights.as_ref()) {
            let phase = start_phase(format!("gkr.whir.pr.round.{r}.eq"), context)?;
            state.in_domain.append(
                &indexes,
                &weights[1..],
                round.query_domain_log2,
                domain_generator_for_size::<PR>(1u64 << round.query_domain_log2),
                context,
            )?;
            schedule_eq_update(&mut state, point, &weights[..1], context)?;
            end_phase(phase, &mut ranges, context)?;
        }
        previous = current;
    }
    assert_eq!(
        poly_index, shape.total_sumcheck_polys,
        "Proth120 WHIR: sumcheck polynomial count differs"
    );
    drop(state);
    drop(challenge);
    schedule_readback_and_assemble(
        outputs,
        host,
        base.cap_digests(),
        setup.oracle().cap_digests(),
        schedule,
        memory_columns,
        setup_columns,
        ranges,
        context,
    )
}
