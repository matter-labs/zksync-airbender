use super::context::ProverContext;
use super::trace_holder::TraceHolder;
use super::transfer::Transfer;
use super::BF;
use cs::one_row_compiler::CompiledCircuitArtifact;
use era_cudart::result::CudaResult;
use fft::GoodAllocator;
use std::sync::Arc;

pub struct SetupPrecomputations<'a> {
    pub(crate) trace_holder: TraceHolder<BF>,
    pub(crate) transfer: Transfer<'a>,
    pub(crate) is_commitment_produced: bool,
}

impl<'a> SetupPrecomputations<'a> {
    pub fn new(
        circuit: &CompiledCircuitArtifact<BF>,
        log_lde_factor: u32,
        log_tree_cap_size: u32,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let trace_len = circuit.trace_len;
        assert!(trace_len.is_power_of_two());
        let log_domain_size = trace_len.trailing_zeros();
        let columns_count = circuit.setup_layout.total_width;
        let trace_holder = TraceHolder::new(
            log_domain_size,
            log_lde_factor,
            0,
            log_tree_cap_size,
            columns_count,
            true,
            context,
        )?;
        let transfer = Transfer::new()?;
        transfer.record_allocated(context)?;
        Ok(Self {
            trace_holder,
            transfer,
            is_commitment_produced: false,
        })
    }

    pub fn schedule_transfer(
        &mut self,
        trace: Arc<Vec<BF, impl GoodAllocator + 'a>>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let dst = self.trace_holder.get_evaluations_mut();
        self.transfer.schedule(trace, dst, context)?;
        self.transfer.record_transferred(context)
    }

    pub fn ensure_commitment_produced(&mut self, context: &ProverContext) -> CudaResult<()> {
        if self.is_commitment_produced {
            return Ok(());
        }
        self.produce_commitment(context)
    }

    fn produce_commitment(&mut self, context: &ProverContext) -> CudaResult<()> {
        self.transfer.ensure_transferred(context)?;
        self.trace_holder
            .make_evaluations_sum_to_zero_extend_and_commit(context)?;
        self.is_commitment_produced = true;
        Ok(())
    }
}
