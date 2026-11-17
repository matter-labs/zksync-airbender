use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::field::PR;
use gpu_prover_context::ProverContext;

use super::commit::IntermediateOracle;
use super::kernels;
use super::openings::schedule_horner_leaves;

const MAX_LEAF_WIDTH: usize = 32;

pub(crate) struct InDomainState {
    weights: DeviceAllocation<PR>,
    points: DeviceAllocation<PR>,
    exponents: DeviceAllocation<u32>,
    leaves: DeviceAllocation<PR>,
    indexes: DeviceAllocation<u32>,
    leaf_points: DeviceAllocation<PR>,
    capacity: usize,
    count: usize,
    leaf_stride: usize,
    leaf_width: usize,
    max_domain_log2: u32,
}

impl InDomainState {
    pub(crate) fn new(capacity: usize, context: &ProverContext) -> CudaResult<Self> {
        let slots = capacity.max(1);
        Ok(Self {
            weights: context.alloc(slots, AllocationPlacement::BestFit)?,
            points: context.alloc(slots, AllocationPlacement::BestFit)?,
            exponents: context.alloc(slots, AllocationPlacement::BestFit)?,
            leaves: context.alloc(slots * MAX_LEAF_WIDTH, AllocationPlacement::BestFit)?,
            indexes: context.alloc(slots, AllocationPlacement::BestFit)?,
            leaf_points: context.alloc(slots, AllocationPlacement::BestFit)?,
            capacity,
            count: 0,
            leaf_stride: 0,
            leaf_width: 0,
            max_domain_log2: 0,
        })
    }

    #[allow(dead_code)]
    pub(crate) fn count(&self) -> usize {
        self.count
    }

    pub(crate) fn append(
        &mut self,
        indexes: &DeviceSlice<u32>,
        weights: &DeviceSlice<PR>,
        query_domain_log2: u32,
        generator: PR,
        context: &ProverContext,
    ) -> CudaResult<()> {
        assert_eq!(
            indexes.len(),
            weights.len(),
            "Proth120 WHIR: in-domain indexes and weights lengths differ"
        );
        let end = self.count + indexes.len();
        assert!(
            end <= self.capacity,
            "Proth120 WHIR: in-domain term capacity exceeded"
        );
        kernels::in_domain_add_terms(
            indexes,
            weights,
            query_domain_log2,
            generator,
            &mut self.weights[self.count..end],
            &mut self.points[self.count..end],
            &mut self.exponents[self.count..end],
            context.get_exec_stream(),
        )?;
        self.count = end;
        self.max_domain_log2 = self.max_domain_log2.max(query_domain_log2);
        self.leaf_width = 0;
        Ok(())
    }

    pub(crate) fn start_round(
        &mut self,
        oracle: &IntermediateOracle,
        current_len: usize,
        log_v: u32,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let shape = oracle.shape;
        assert_eq!(
            current_len,
            1 << shape.log_n,
            "Proth120 WHIR: in-domain refresh length differs from the oracle"
        );
        assert_eq!(
            log_v, shape.log_v,
            "Proth120 WHIR: in-domain refresh leaf width differs from the oracle"
        );
        assert!(
            self.max_domain_log2 <= shape.log_domain,
            "Proth120 WHIR: symbolic term outside the current oracle domain"
        );
        self.leaf_stride = 1 << log_v;
        assert!(
            self.leaf_stride <= MAX_LEAF_WIDTH,
            "Proth120 WHIR: in-domain leaf width exceeds scratch capacity"
        );
        self.leaf_width = self.leaf_stride;
        if self.count != 0 {
            kernels::in_domain_prepare_indexes(
                &self.exponents[..self.count],
                &self.points[..self.count],
                shape.log_domain,
                log_v,
                &mut self.indexes[..self.count],
                &mut self.leaf_points[..self.count],
                context.get_exec_stream(),
            )?;
            schedule_horner_leaves(
                &oracle.monomials,
                shape.log_n,
                log_v,
                &self.leaf_points[..self.count],
                &mut self.leaves[..self.count << log_v],
                0,
                context,
            )?;
        }
        Ok(())
    }

    pub(crate) fn try_update(
        &mut self,
        reductions: &mut DeviceSlice<PR>,
        seed: &mut DeviceSlice<u8>,
        coeffs: &mut DeviceSlice<PR>,
        context: &ProverContext,
    ) -> CudaResult<bool> {
        if self.count == 0 {
            return Ok(false);
        }
        assert!(
            self.leaf_width >= 2,
            "Proth120 WHIR: in-domain terms folded without refreshed leaves"
        );
        kernels::in_domain_correct_update(
            &self.leaves[..self.count * self.leaf_stride],
            self.leaf_stride as u32,
            self.leaf_width as u32,
            &self.weights[..self.count],
            &self.points[..self.count],
            reductions,
            seed,
            coeffs,
            context.get_exec_stream(),
        )?;
        Ok(true)
    }

    pub(crate) fn fold(
        &mut self,
        challenge: &DeviceSlice<PR>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        if self.count == 0 {
            return Ok(());
        }
        kernels::in_domain_fold(
            &mut self.leaves[..self.count * self.leaf_stride],
            self.leaf_stride as u32,
            self.leaf_width as u32,
            &mut self.weights[..self.count],
            &mut self.points[..self.count],
            &mut self.exponents[..self.count],
            challenge,
            context.get_exec_stream(),
        )?;
        self.leaf_width >>= 1;
        self.max_domain_log2 = self.max_domain_log2.saturating_sub(1);
        Ok(())
    }
}
