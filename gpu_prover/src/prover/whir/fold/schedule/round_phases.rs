use super::super::*;

/// Commits the next WHIR extension oracle: builds it from `state.sumchecked_poly_monomial_form`,
/// D2D-copies its unified device cap to the slab at `oracle_idx`, schedules a D2H of the cap
/// into a pinned host buffer, and registers a `final_callbacks` closure that publishes the
/// host cap into `proof.intermediate_whir_oracles[oracle_idx].commitment` and folds the
/// commitment into the host-side transcript seed. Range tracking is the caller's
/// responsibility.
#[allow(clippy::too_many_arguments)]
pub(super) fn schedule_commit_next_oracle_phase(
    state: &GpuWhirState,
    oracle_idx: usize,
    lde_factor: usize,
    next_folding_steps: usize,
    tree_cap_size: usize,
    proof_slab: Option<&DeviceAllocation<E4>>,
    proof_layout: &ProofLayout,
    shared_state_handle: UnsafeMutAccessor<ScheduledWhirProofState>,
    seed_accessor: UnsafeMutAccessor<Seed>,
    intermediate_oracle_cap_hosts: &mut Vec<HostAllocation<[Digest]>>,
    final_callbacks: &mut Callbacks<'static>,
    stream: &era_cudart::stream::CudaStream,
    context: &ProverContext,
) -> CudaResult<GpuWhirExtensionOracle> {
    let oracle = GpuWhirExtensionOracle::schedule_from_device_monomial_coeffs(
        &state.sumchecked_poly_monomial_form,
        state.current_len,
        lde_factor,
        1 << next_folding_steps,
        tree_cap_size,
        context,
    )?;
    copy_intermediate_cap_to_slab(
        oracle.unified_device_cap(),
        proof_slab,
        proof_layout,
        oracle_idx,
        stream,
    )?;
    let oracle_cap_host_for_proof =
        schedule_unified_cap_d2h(oracle.unified_device_cap(), context, stream)?;
    let oracle_cap_host_accessor = oracle_cap_host_for_proof.get_accessor();
    intermediate_oracle_cap_hosts.push(oracle_cap_host_for_proof);
    final_callbacks.schedule(
        {
            let shared_state = shared_state_handle;
            move || unsafe {
                let proof_state = shared_state.get_mut();
                let commitment = &mut proof_state
                    .proof
                    .as_mut()
                    .unwrap()
                    .intermediate_whir_oracles[oracle_idx]
                    .commitment;
                commitment
                    .cap
                    .cap
                    .copy_from_slice(oracle_cap_host_accessor.get());
                add_whir_commitment_to_transcript(seed_accessor.get_mut(), commitment);
            }
        },
        stream,
    )?;
    Ok(oracle)
}

/// Draws an OOD sample point, schedules the monomial-eval reduction for the current state's
/// folded polynomial, registers a `final_callbacks` closure that sums the partial readbacks,
/// commits the value to the transcript seed, and publishes it into
/// `proof.ood_samples[oracle_idx]`. Also D2D-copies the OOD value into the slab.
///
/// Returns `ood_point_host` so the caller can capture an accessor for the subsequent
/// delinearization phase. Range tracking is the caller's responsibility.
#[allow(clippy::too_many_arguments)]
pub(super) fn schedule_ood_sample_phase(
    state: &mut GpuWhirState,
    oracle_idx: usize,
    proof_slab: Option<&DeviceAllocation<E4>>,
    proof_layout: &ProofLayout,
    shared_state_handle: UnsafeMutAccessor<ScheduledWhirProofState>,
    seed_accessor: UnsafeMutAccessor<Seed>,
    ood_points: &mut Vec<WhirHostUpload>,
    ood_partial_readbacks: &mut Vec<Vec<HostAllocation<[E4]>>>,
    ood_values: &mut Vec<HostAllocation<[E4]>>,
    final_callbacks: &mut Callbacks<'static>,
    stream: &era_cudart::stream::CudaStream,
    context: &ProverContext,
) -> CudaResult<HostAllocation<[E4]>> {
    let (ood_point_upload, ood_point_host, ood_point_device) =
        schedule_callback_populated_upload(context, 1, move |dst: &mut [E4]| unsafe {
            dst[0] = draw_random_field_els::<BF, E4>(seed_accessor.get_mut(), 1)[0];
        })?;
    let ood_partials = schedule_monomial_eval_device(state, &ood_point_device, context)?;
    let mut ood_value_host = unsafe { context.alloc_host_uninit_slice(1) };
    let ood_value_accessor = ood_value_host.get_mut_accessor();
    final_callbacks.schedule(
        {
            let shared_state = shared_state_handle;
            let partial_accessors = ood_partials
                .iter()
                .map(HostAllocation::get_accessor)
                .collect::<Vec<_>>();
            move || unsafe {
                let mut value = E4::ZERO;
                for partial in partial_accessors.iter() {
                    value.add_assign(&partial.get()[0]);
                }
                ood_value_accessor.get_mut()[0] = value;
                commit_field_els::<BF, E4>(seed_accessor.get_mut(), &[value]);
                shared_state.get_mut().proof.as_mut().unwrap().ood_samples[oracle_idx] = value;
            }
        },
        stream,
    )?;
    copy_ood_sample_to_slab(
        &ood_value_host,
        proof_slab,
        proof_layout,
        oracle_idx,
        stream,
    )?;
    ood_partial_readbacks.push(ood_partials);
    ood_points.push(ood_point_upload);
    ood_values.push(ood_value_host);
    Ok(ood_point_host)
}

/// Schedules the PoW verify + query-index draw for one WHIR round: allocates the host nonce
/// and per-query index buffers, schedules `schedule_pow_verify_and_query_indexes`, D2D-copies
/// the nonce into the slab, registers the post-PoW callback that mirrors the seed and
/// publishes the nonce into `proof.pow_nonces[pow_round_idx]`, and (under `cfg(test)`)
/// snapshots the pre-PoW seed.
///
/// Returns `(query_indexes_host, query_index_callbacks_for_round)` so the caller can:
/// (a) capture the indexes accessor for the subsequent per-query loop, (b) extend the
/// per-round callbacks container with query-specific work, and (c) eventually push both
/// into the orchestrator's keepalive vecs. The nonce host buffer and PoW keepalives are
/// pushed into their respective vecs inside this fn.
#[allow(clippy::too_many_arguments)]
pub(super) fn schedule_pow_and_query_indexes_phase(
    seed_host: &mut HostAllocation<Seed>,
    seed_accessor: UnsafeMutAccessor<Seed>,
    shared_state_handle: UnsafeMutAccessor<ScheduledWhirProofState>,
    num_queries: usize,
    pow_bits: u32,
    pow_round_idx: usize,
    query_domain_log2: usize,
    proof_slab: Option<&DeviceAllocation<E4>>,
    proof_layout: &ProofLayout,
    pow_keepalives_list: &mut Vec<PowAndQueryIndexesKeepalives>,
    pow_nonces: &mut Vec<HostAllocation<u64>>,
    stream: &era_cudart::stream::CudaStream,
    context: &ProverContext,
) -> CudaResult<(HostAllocation<[u32]>, Callbacks<'static>)> {
    let mut nonce_host = unsafe { context.alloc_host_uninit::<u64>() };
    let mut query_indexes_host = unsafe { context.alloc_host_uninit_slice(num_queries) };
    let nonce_accessor = nonce_host.get_mut_accessor();
    let mut query_index_callbacks_for_round = Callbacks::new();
    #[cfg(test)]
    query_index_callbacks_for_round.schedule(
        {
            let shared_state = shared_state_handle;
            move || unsafe {
                shared_state.get_mut().pre_pow_seeds[pow_round_idx] = *seed_accessor.get();
            }
        },
        stream,
    )?;
    let pow_keepalives = schedule_pow_verify_and_query_indexes(
        seed_host,
        &mut nonce_host,
        &mut query_indexes_host,
        num_queries,
        pow_bits,
        query_domain_log2,
        context,
    )?;
    copy_pow_nonce_to_slab(
        &pow_keepalives,
        proof_slab,
        proof_layout,
        pow_round_idx,
        stream,
    )?;
    let h_seed_mirror_accessor = pow_keepalives.h_seed_mirror.get_accessor();
    pow_keepalives_list.push(pow_keepalives);
    query_index_callbacks_for_round.schedule(
        {
            let shared_state = shared_state_handle;
            move || unsafe {
                // Fused post-PoW host bookkeeping: advance the host seed from the device
                // mirror, then publish the nonce.
                let src = h_seed_mirror_accessor.get();
                seed_accessor.get_mut().0.copy_from_slice(src);
                shared_state.get_mut().proof.as_mut().unwrap().pow_nonces[pow_round_idx] =
                    *nonce_accessor.get();
            }
        },
        stream,
    )?;
    pow_nonces.push(nonce_host);
    Ok((query_indexes_host, query_index_callbacks_for_round))
}

/// Schedules the running-powers upload `[x, x^2, ..., x^(num_queries + 1)]` and an
/// `accumulate_eq_sample_in_place` device op against the OOD anchor point using power index 0.
/// CPU weights the OOD contribution by `x` and the i-th query contribution by `x^(i + 2)` when
/// accumulating `contributions_to_eq_poly` (see `prover/src/gkr/whir/mod.rs`,
/// `current_delinearization_challenge` loop). The kernel reads a single scalar per call, so
/// each call site selects the matching power by sub-slicing the returned device buffer.
///
/// Returns `(delinearization_upload, delinearization_device)`. Caller pushes the upload
/// into `delinearization_challenges` after the per-query loop has finished using the
/// device buffer. Used by base and intermediate rounds; the final round has no delinearization
/// step.
pub(super) fn schedule_delinearization_running_powers_phase(
    state: &mut GpuWhirState,
    num_queries: usize,
    ood_point_host: &HostAllocation<[E4]>,
    seed_accessor: UnsafeMutAccessor<Seed>,
    ood_points: &mut Vec<WhirHostUpload>,
    context: &ProverContext,
) -> CudaResult<(WhirHostUpload, DeviceAllocation<E4>)> {
    let (delinearization_upload, _delinearization_host, delinearization_device) =
        schedule_callback_populated_upload(
            context,
            num_queries + 1,
            move |dst: &mut [E4]| unsafe {
                let base = draw_random_field_els::<BF, E4>(seed_accessor.get_mut(), 1)[0];
                let mut power = base;
                for dst_el in dst.iter_mut() {
                    *dst_el = power;
                    power.mul_assign(&base);
                }
            },
        )?;
    let ood_point_accessor = ood_point_host.get_accessor();
    let (eq_upload, _eq_host) = schedule_accumulate_eq_sample_in_place_device(
        state,
        move |dst| unsafe {
            let mut value = ood_point_accessor.get()[0];
            for dst_el in dst.iter_mut() {
                *dst_el = value;
                value.square();
            }
        },
        &delinearization_device[0..1],
        context,
    )?;
    ood_points.push(eq_upload);
    Ok((delinearization_upload, delinearization_device))
}
