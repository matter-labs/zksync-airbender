use super::*;

/// Query terms stay small while the original/OOD equality polynomial stays
/// dense. All buffers are read and written only by exec-stream operations.
pub(super) struct InDomainState {
    weights: DeviceAllocation<E4>,
    points: DeviceAllocation<BF>,
    exponents: DeviceAllocation<u32>,
    leaves: DeviceAllocation<E4>,
    indexes: DeviceAllocation<u32>,
    count: usize,
    leaf_stride: usize,
    leaf_width: usize,
    max_domain_log2: u32,
}

impl InDomainState {
    pub(super) fn new(
        capacity: usize,
        max_leaf_size: usize,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        assert!(max_leaf_size.is_power_of_two());
        Ok(Self {
            weights: context.alloc(capacity, AllocationPlacement::BestFit)?,
            points: context.alloc(capacity, AllocationPlacement::BestFit)?,
            exponents: context.alloc(capacity, AllocationPlacement::BestFit)?,
            leaves: context.alloc(capacity * max_leaf_size, AllocationPlacement::BestFit)?,
            indexes: context.alloc(capacity, AllocationPlacement::BestFit)?,
            count: 0,
            leaf_stride: 0,
            leaf_width: 0,
            max_domain_log2: 0,
        })
    }

    pub(super) fn append(
        &mut self,
        indexes: &DeviceSlice<u32>,
        weights: &DeviceSlice<E4>,
        domain_log2: u32,
        generator: BF,
        context: &ProverContext,
    ) -> CudaResult<()> {
        assert_eq!(indexes.len(), weights.len());
        let end = self.count + indexes.len();
        assert!(end <= self.weights.len());
        crate::in_domain::add_terms(
            indexes,
            weights,
            domain_log2,
            generator,
            &mut self.weights[self.count..end],
            &mut self.points[self.count..end],
            &mut self.exponents[self.count..end],
            context.get_exec_stream(),
        )?;
        self.count = end;
        self.max_domain_log2 = self.max_domain_log2.max(domain_log2);
        // New terms have no current-oracle leaves until the next group.
        self.leaf_width = 0;
        Ok(())
    }

    pub(super) fn start_round(
        &mut self,
        oracle: &mut GpuWhirExtensionOracle,
        current_len: usize,
        folding_steps: usize,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let domain_log2 = current_len.trailing_zeros() + oracle.lde_factor().trailing_zeros();
        assert!(
            self.max_domain_log2 <= domain_log2,
            "symbolic term outside current oracle domain"
        );
        self.leaf_stride = 1usize << folding_steps;
        self.leaf_width = self.leaf_stride;
        assert!(self.count * self.leaf_stride <= self.leaves.len());
        if self.count != 0 {
            crate::in_domain::prepare_indexes(
                &self.exponents[..self.count],
                domain_log2,
                folding_steps as u32,
                &mut self.indexes[..self.count],
                context.get_exec_stream(),
            )?;
            oracle.schedule_in_domain_leaves(
                &self.indexes[..self.count],
                &mut self.leaves[..self.count * self.leaf_stride],
                context,
            )?;
        }
        Ok(())
    }

    /// Combines correction, transcript update and term fold in one
    /// CTA; the dense state still folds afterward on the same stream.
    pub(super) fn try_update_and_fold(
        &mut self,
        reductions: &mut DeviceSlice<E4>,
        seed: &mut DeviceSlice<u32>,
        coefficients: &mut DeviceSlice<E4>,
        challenge: &mut DeviceSlice<E4>,
        context: &ProverContext,
    ) -> CudaResult<bool> {
        if self.count == 0 {
            return Ok(false);
        }
        assert!(self.leaf_width >= 2);
        crate::in_domain::correct_update_and_fold(
            &mut self.leaves[..self.count * self.leaf_stride],
            self.leaf_stride as u32,
            self.leaf_width as u32,
            &mut self.weights[..self.count],
            &mut self.points[..self.count],
            &mut self.exponents[..self.count],
            reductions,
            seed,
            coefficients,
            challenge,
            context.get_exec_stream(),
        )?;
        self.leaf_width >>= 1;
        self.max_domain_log2 = self.max_domain_log2.saturating_sub(1);
        Ok(true)
    }
}

// After leaf-only refresh and step fusion, Sec100 paired proofs also improve
// at log trace 20 (10/10 WHIR wins). Log 21 has no shipped fixture; smaller
// sizes remain dense. See AGENTS.md and the September 29 follow-up audit.
const MIN_SYMBOLIC_TRACE_LOG2: u32 = 20;

fn symbolic_enabled(trace_len: usize) -> bool {
    // The symbolic identity consumes coefficient leaves. Evaluation encoding
    // deliberately keeps the dense equality path.
    if cfg!(feature = "eval_leaves") {
        return false;
    }
    trace_len >= 1usize << MIN_SYMBOLIC_TRACE_LOG2
}

pub(super) fn configure_symbolic_terms(
    state: &mut GpuWhirState,
    query_schedule: &[usize],
    folding_schedule: &[usize],
    context: &ProverContext,
) -> CudaResult<()> {
    if symbolic_enabled(state.current_len) {
        let capacity = query_schedule[..query_schedule.len() - 1].iter().sum();
        let max_leaf_size = 1usize << folding_schedule.iter().skip(1).copied().max().unwrap_or(0);
        state.in_domain = Some(InDomainState::new(capacity, max_leaf_size, context)?);
    }
    Ok(())
}

/// Only query terms move out of the dense table; the OOD term at slot zero
/// remains in the original equality polynomial and follows its normal folds.
pub(super) fn schedule_query_eq_update(
    state: &mut GpuWhirState,
    indexes: &DeviceSlice<u32>,
    domain_log2: u32,
    generator: BF,
    powers: &mut DeviceSlice<E4>,
    weights: &DeviceSlice<E4>,
    count_per_query: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    let dense_count = if let Some(terms) = &mut state.in_domain {
        terms.append(indexes, &weights[1..], domain_log2, generator, context)?;
        1
    } else {
        gpu_ops::squaring::query_squaring_sequences_bf_to_e4(
            generator,
            indexes,
            &mut powers[count_per_query..],
            count_per_query as u32,
            context.get_exec_stream(),
        )?;
        indexes.len() + 1
    };
    let _scratch = schedule_accumulate_eq_samples_batched(
        state,
        &powers[..dense_count * count_per_query],
        &weights[..dense_count],
        dense_count,
        count_per_query,
        context,
    )?;
    Ok(())
}
