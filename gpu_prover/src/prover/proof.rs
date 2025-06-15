use super::callbacks::Callbacks;
use super::context::ProverContext;
use super::pow::PowOutput;
use super::queries::QueriesOutput;
use super::setup::SetupPrecomputations;
use super::stage_1::StageOneOutput;
use super::stage_2::StageTwoOutput;
use super::stage_3::StageThreeOutput;
use super::stage_4::StageFourOutput;
use super::stage_5::StageFiveOutput;
use super::trace_holder::{flatten_tree_caps, transform_tree_caps};
use super::tracing_data::TracingDataTransfer;
use super::{device_tracing, BF, E4};
use crate::blake2s::Digest;
use cs::one_row_compiler::CompiledCircuitArtifact;
use era_cudart::event::{CudaEvent, CudaEventCreateFlags};
use era_cudart::result::CudaResult;
use era_cudart::stream::{CudaStream, CudaStreamWaitEventFlags};
use fft::{GoodAllocator, LdePrecomputations, Twiddles};
use field::{Mersenne31Complex, Mersenne31Field};
use itertools::Itertools;
use prover::definitions::{ExternalValues, Transcript, OPTIMAL_FOLDING_PROPERTIES};
use prover::prover_stages::cached_data::ProverCachedData;
use prover::prover_stages::Proof;
use prover::transcript::Seed;
use std::ops::Deref;
use std::sync::{Arc, Mutex};

pub struct ProofJob<'a, C: ProverContext> {
    ranges: Vec<device_tracing::Range<'a>>,
    is_finished_event: CudaEvent,
    callbacks: Callbacks<'a>,
    external_values: ExternalValues,
    public_inputs: Arc<Mutex<Vec<BF>>>,
    witness_tree_caps: Arc<Vec<Vec<Digest, C::HostAllocator>>>,
    memory_tree_caps: Arc<Vec<Vec<Digest, C::HostAllocator>>>,
    setup_tree_caps: Arc<Vec<Vec<Digest, C::HostAllocator>>>,
    stage_2_tree_caps: Arc<Vec<Vec<Digest, C::HostAllocator>>>,
    stage_2_last_row: Arc<Vec<BF, C::HostAllocator>>,
    stage_2_offset_for_memory_grand_product_poly: usize,
    stage_2_offset_for_delegation_argument_poly: Option<usize>,
    quotient_tree_caps: Arc<Vec<Vec<Digest, C::HostAllocator>>>,
    evaluations_at_random_points: Arc<Vec<E4, C::HostAllocator>>,
    deep_poly_caps: Arc<Vec<Vec<Digest, C::HostAllocator>>>,
    intermediate_fri_oracle_caps: Vec<Arc<Vec<Vec<Digest, C::HostAllocator>>>>,
    last_fri_step_plain_leaf_values: Arc<Vec<Vec<E4, C::HostAllocator>>>,
    final_monomial_form: Arc<Mutex<Vec<E4>>>,
    pow_output: PowOutput<C>,
    queries_output: QueriesOutput<'a, C>,
    circuit_sequence: u16,
    delegation_type: u16,
}

impl<'a, C: ProverContext> ProofJob<'a, C> {
    pub fn is_finished(&self) -> CudaResult<bool> {
        self.is_finished_event.query()
    }

    pub fn finish(self) -> CudaResult<(Proof, f32)> {
        let Self {
            ranges,
            is_finished_event,
            callbacks,
            external_values,
            public_inputs,
            witness_tree_caps,
            memory_tree_caps,
            setup_tree_caps,
            stage_2_tree_caps,
            stage_2_last_row,
            stage_2_offset_for_memory_grand_product_poly,
            stage_2_offset_for_delegation_argument_poly,
            quotient_tree_caps,
            evaluations_at_random_points,
            deep_poly_caps,
            intermediate_fri_oracle_caps,
            last_fri_step_plain_leaf_values,
            final_monomial_form,
            pow_output,
            queries_output,
            circuit_sequence,
            delegation_type,
        } = self;
        is_finished_event.synchronize()?;
        drop(callbacks);

        #[cfg(feature = "log_gpu_stages_timings")]
        {
            log::debug!("GPU setup time: {:.3} ms", ranges[0].elapsed()?);
            log::debug!("GPU stage 1 time: {:.3} ms", ranges[1].elapsed()?);
            log::debug!("GPU stage 2 time: {:.3} ms", ranges[2].elapsed()?);
            log::debug!("GPU stage 3 time: {:.3} ms", ranges[3].elapsed()?);
            log::debug!("GPU stage 4 time: {:.3} ms", ranges[4].elapsed()?);
            log::debug!("GPU stage 5 time: {:.3} ms", ranges[5].elapsed()?);
            log::debug!("GPU pow time: {:.3} ms", ranges[6].elapsed()?);
            log::debug!("GPU queries time: {:.3} ms", ranges[7].elapsed()?);
        }
        let proof_time_ms = ranges[8].elapsed()?;

        let public_inputs = public_inputs.lock().unwrap().clone();
        let witness_tree_caps = transform_tree_caps(&witness_tree_caps);
        let memory_tree_caps = transform_tree_caps(&memory_tree_caps);
        let setup_tree_caps = transform_tree_caps(&setup_tree_caps);
        let stage_2_tree_caps = transform_tree_caps(&stage_2_tree_caps);
        let memory_grand_product_accumulator = StageTwoOutput::<C>::get_grand_product_accumulator(
            stage_2_offset_for_memory_grand_product_poly,
            &stage_2_last_row,
        );
        let delegation_argument_accumulator = StageTwoOutput::<C>::get_sum_over_delegation_poly(
            stage_2_offset_for_delegation_argument_poly,
            &stage_2_last_row,
        );
        let quotient_tree_caps = transform_tree_caps(&quotient_tree_caps);
        let evaluations_at_random_points =
            evaluations_at_random_points.iter().copied().collect_vec();
        let deep_poly_caps = transform_tree_caps(&deep_poly_caps);
        let intermediate_fri_oracle_caps = intermediate_fri_oracle_caps
            .iter()
            .map(|o| o.as_slice())
            .filter(|c| !c.is_empty())
            .map(transform_tree_caps)
            .collect_vec();
        let last_fri_step_plain_leaf_values = last_fri_step_plain_leaf_values
            .iter()
            .map(|v| v.to_vec())
            .collect_vec();
        let final_monomial_form = final_monomial_form.lock().unwrap().clone();
        let pow_nonce = *pow_output.nonce.lock().unwrap().deref().deref();
        let queries = queries_output.produce_query_sets();
        let proof = Proof {
            external_values,
            public_inputs,
            witness_tree_caps,
            memory_tree_caps,
            setup_tree_caps,
            stage_2_tree_caps,
            memory_grand_product_accumulator,
            delegation_argument_accumulator,
            quotient_tree_caps,
            evaluations_at_random_points,
            deep_poly_caps,
            intermediate_fri_oracle_caps,
            last_fri_step_plain_leaf_values,
            final_monomial_form,
            queries,
            pow_nonce,
            circuit_sequence,
            delegation_type,
        };
        Ok((proof, proof_time_ms))
    }
}

pub fn prove<'a, C: ProverContext>(
    circuit: Arc<CompiledCircuitArtifact<BF>>,
    external_values: ExternalValues,
    setup: &mut SetupPrecomputations<C>,
    tracing_data_transfer: TracingDataTransfer<'a, C>,
    twiddles: &Twiddles<Mersenne31Complex, impl GoodAllocator>,
    lde_precomputations: &LdePrecomputations<impl GoodAllocator>,
    circuit_sequence: usize,
    delegation_processing_type: Option<u16>,
    lde_factor: usize,
    num_queries: usize,
    pow_bits: u32,
    external_pow_nonce: Option<u64>,
    context: &C,
) -> CudaResult<ProofJob<'a, C>>
where
    C::HostAllocator: 'a,
{
    #[cfg(feature = "log_gpu_mem_usage")]
    context.log_mem_pool_stats("initial")?;

    let trace_len = circuit.trace_len;
    assert!(trace_len.is_power_of_two());
    let log_domain_size = trace_len.trailing_zeros();
    let optimal_folding = OPTIMAL_FOLDING_PROPERTIES[log_domain_size as usize];
    assert!(circuit_sequence <= u16::MAX as usize);
    let delegation_processing_type = delegation_processing_type.unwrap_or_default();
    let cached_data_values = ProverCachedData::new(
        &circuit,
        &external_values,
        trace_len,
        circuit_sequence,
        delegation_processing_type,
    );
    assert!(lde_factor.is_power_of_two());
    let log_lde_factor = lde_factor.trailing_zeros();
    let log_tree_cap_size = optimal_folding.total_caps_size_log2 as u32;
    let stream = context.get_exec_stream();
    let mut callbacks = Callbacks::new();

    let proof_range = device_tracing::Range::new("proof")?;
    proof_range.start(stream)?;

    // setup
    let setup_range = device_tracing::Range::new("setup")?;
    setup_range.start(stream)?;
    setup.ensure_commitment_produced(context)?;
    setup_range.end(stream)?;

    let mut stage_1_output = StageOneOutput::allocate_trace_holders(
        &circuit,
        log_lde_factor,
        log_tree_cap_size,
        context,
    )?;
    #[cfg(feature = "log_gpu_mem_usage")]
    context.log_mem_pool_stats("after stage_1.allocate_trace_holders")?;

    let mut stage_2_output = StageTwoOutput::allocate_trace_evaluations(
        &circuit,
        log_lde_factor,
        log_tree_cap_size,
        context,
    )?;
    #[cfg(feature = "log_gpu_mem_usage")]
    context.log_mem_pool_stats("after stage_2.allocate_trace_evaluations")?;

    // witness_generation
    let witness_generation_range = device_tracing::Range::new("witness_generation")?;
    witness_generation_range.start(stream)?;
    stage_1_output.generate_witness(
        &circuit,
        setup,
        tracing_data_transfer,
        circuit_sequence,
        context,
    )?;
    witness_generation_range.end(stream)?;
    #[cfg(feature = "log_gpu_mem_usage")]
    context.log_mem_pool_stats("after generate_witness")?;

    // stage 1
    let stage_1_range = device_tracing::Range::new("stage_1")?;
    stage_1_range.start(stream)?;
    stage_1_output.commit_witness(&circuit, context)?;
    stage_1_range.end(stream)?;
    #[cfg(feature = "log_gpu_mem_usage")]
    context.log_mem_pool_stats("after stage_1")?;

    setup.trace_holder.produce_tree_caps(context)?;

    // seed
    let seed = initialize_seed::<C>(
        &circuit,
        external_values.clone(),
        circuit_sequence,
        delegation_processing_type,
        setup,
        &stage_1_output,
        &mut callbacks,
        stream,
    )?;

    // stage 2
    let stage_2_range = device_tracing::Range::new("stage_2")?;
    stage_2_range.start(stream)?;
    stage_2_output.generate(
        seed.clone(),
        &circuit,
        &cached_data_values,
        setup,
        &mut stage_1_output,
        context,
    )?;
    stage_2_range.end(stream)?;
    #[cfg(feature = "log_gpu_mem_usage")]
    context.log_mem_pool_stats("after stage_2")?;

    // stage 3
    let stage_3_range = device_tracing::Range::new("stage_3")?;
    stage_3_range.start(stream)?;
    let stage_3_output = StageThreeOutput::new(
        seed.clone(),
        &circuit,
        &cached_data_values,
        &lde_precomputations,
        &twiddles,
        external_values.clone(),
        setup,
        &stage_1_output,
        &stage_2_output,
        log_lde_factor,
        log_tree_cap_size,
        context,
    )?;
    stage_3_range.end(stream)?;
    #[cfg(feature = "log_gpu_mem_usage")]
    context.log_mem_pool_stats("after stage_3")?;

    // stage 4
    let stage_4_range = device_tracing::Range::new("stage_4")?;
    stage_4_range.start(stream)?;
    let stage_4_output = StageFourOutput::new(
        seed.clone(),
        &circuit,
        &cached_data_values,
        &twiddles,
        &setup,
        &stage_1_output,
        &stage_2_output,
        &stage_3_output,
        log_lde_factor,
        log_tree_cap_size,
        &optimal_folding,
        context,
    )?;
    stage_4_range.end(stream)?;
    #[cfg(feature = "log_gpu_mem_usage")]
    context.log_mem_pool_stats("after stage_4 ")?;

    // stage 5
    let stage_5_range = device_tracing::Range::new("stage_5")?;
    stage_5_range.start(stream)?;
    let stage_5_output = StageFiveOutput::new(
        seed.clone(),
        &stage_4_output,
        log_domain_size,
        log_lde_factor,
        &optimal_folding,
        num_queries,
        &lde_precomputations,
        &twiddles,
        context,
    )?;
    stage_5_range.end(stream)?;
    #[cfg(feature = "log_gpu_mem_usage")]
    context.log_mem_pool_stats("after stage_5 ")?;

    // pow
    let pow_range = device_tracing::Range::new("pow")?;
    pow_range.start(stream)?;
    let pow_output = PowOutput::new(
        seed.clone(),
        pow_bits,
        external_pow_nonce,
        &mut callbacks,
        context,
    )?;
    pow_range.end(stream)?;
    #[cfg(feature = "log_gpu_mem_usage")]
    context.log_mem_pool_stats("after pow ")?;

    // pow
    let queries_range = device_tracing::Range::new("queries")?;
    queries_range.start(stream)?;
    let queries_output = QueriesOutput::new(
        seed,
        &setup,
        &stage_1_output,
        &stage_2_output,
        &stage_3_output,
        &stage_4_output,
        &stage_5_output,
        log_domain_size,
        log_lde_factor,
        num_queries,
        &optimal_folding,
        context,
    )?;
    queries_range.end(stream)?;
    #[cfg(feature = "log_gpu_mem_usage")]
    context.log_mem_pool_stats("after queries")?;

    // ensure no transfer spilling back to previously scheduled proofs
    {
        let event = CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?;
        event.record(stream)?;
        context
            .get_h2d_stream()
            .wait_event(&event, CudaStreamWaitEventFlags::DEFAULT)?;
    }

    proof_range.end(stream)?;

    let ranges = vec![
        setup_range,
        stage_1_range,
        stage_2_range,
        stage_3_range,
        stage_4_range,
        stage_5_range,
        pow_range,
        queries_range,
        proof_range,
    ];

    let is_finished_event = CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?;
    is_finished_event.record(stream)?;

    callbacks.extend(stage_1_output.callbacks.unwrap());
    callbacks.extend(stage_2_output.callbacks.unwrap());
    callbacks.extend(stage_3_output.callbacks);
    callbacks.extend(stage_4_output.callbacks);
    callbacks.extend(stage_5_output.callbacks);

    let proof_job = ProofJob {
        ranges,
        is_finished_event,
        callbacks,
        external_values,
        public_inputs: stage_1_output.public_inputs.unwrap(),
        witness_tree_caps: stage_1_output.witness_holder.get_tree_caps(),
        memory_tree_caps: stage_1_output.memory_holder.get_tree_caps(),
        setup_tree_caps: setup.trace_holder.get_tree_caps(),
        stage_2_tree_caps: stage_2_output.trace_holder.get_tree_caps(),
        stage_2_last_row: stage_2_output.last_row.unwrap(),
        stage_2_offset_for_memory_grand_product_poly: stage_2_output.offset_for_grand_product_poly,
        stage_2_offset_for_delegation_argument_poly: stage_2_output
            .offset_for_sum_over_delegation_poly,
        quotient_tree_caps: stage_3_output.trace_holder.get_tree_caps(),
        evaluations_at_random_points: stage_4_output.values_at_z,
        deep_poly_caps: stage_4_output.trace_holder.get_tree_caps(),
        intermediate_fri_oracle_caps: stage_5_output
            .fri_oracles
            .into_iter()
            .map(|o| o.tree_caps)
            .collect_vec(),
        last_fri_step_plain_leaf_values: stage_5_output.last_fri_step_plain_leaf_values,
        final_monomial_form: stage_5_output.final_monomials,
        pow_output,
        queries_output,
        circuit_sequence: circuit_sequence as u16,
        delegation_type: delegation_processing_type,
    };
    Ok(proof_job)
}

fn initialize_seed<'a, C: ProverContext>(
    circuit: &Arc<CompiledCircuitArtifact<Mersenne31Field>>,
    external_values: ExternalValues,
    circuit_sequence: usize,
    delegation_processing_type: u16,
    setup: &SetupPrecomputations<C>,
    stage_1_output: &StageOneOutput<C>,
    callbacks: &mut Callbacks<'a>,
    stream: &CudaStream,
) -> CudaResult<Arc<Mutex<Seed>>>
where
    C::HostAllocator: 'a,
{
    let seed = Arc::new(Mutex::new(Seed(Default::default())));
    let seed_clone = seed.clone();
    let setup_tree_caps = setup.trace_holder.get_tree_caps();
    let witness_tree_caps = stage_1_output.witness_holder.get_tree_caps();
    let memory_tree_caps = stage_1_output.memory_holder.get_tree_caps();
    let public_inputs = stage_1_output.get_public_inputs();
    let circuit_clone = circuit.clone();
    let seed_fn = move || {
        let mut input = vec![];
        input.push(circuit_sequence as u32);
        input.push(delegation_processing_type as u32);
        input.extend(public_inputs.lock().unwrap().iter().map(BF::to_reduced_u32));
        input.extend(flatten_tree_caps(&setup_tree_caps));
        input.extend_from_slice(&external_values.challenges.memory_argument.flatten());
        if let Some(delegation_argument_challenges) =
            external_values.challenges.delegation_argument.as_ref()
        {
            input.extend_from_slice(&delegation_argument_challenges.flatten());
        }
        if circuit_clone
            .memory_layout
            .shuffle_ram_inits_and_teardowns
            .is_some()
        {
            input.extend_from_slice(&external_values.aux_boundary_values.flatten());
        }
        input.extend(flatten_tree_caps(&witness_tree_caps));
        input.extend(flatten_tree_caps(&memory_tree_caps));
        let mut guard = seed_clone.lock().unwrap();
        *guard = Transcript::commit_initial(&input);
    };
    callbacks.schedule(seed_fn, stream)?;
    Ok(seed)
}
