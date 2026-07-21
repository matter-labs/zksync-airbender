use crate::bwd::source::FoldState;
use crate::eval_plan::backward::BackwardEvaluationError;

pub mod experiment;
pub mod genome;
pub mod materialization;
pub mod pager;
pub mod problem;
pub mod production;
pub mod replay;
mod uniform_pager;

pub use genome::{
    BackwardAdapter, BackwardGenome, BackwardSearchArm, decode_cache_actions,
    decode_fragment_order, paging_seed,
};
pub(crate) use materialization::native_read_cost;
pub use materialization::{
    SourceOriginKind, SourceRoundUse, StaticMaterialization, build_static_materialization,
    miss_cost,
};
pub use pager::{
    ExactPagingPlan, PagerOutcome, PagingAction, PagingObjective, PagingTelemetry,
    ProductionPagingResult, ProductionPagingSolver, reconstruct_paging_plan, solve_exact_paging,
    solve_production_paging, solve_retain_all_if_exact,
};
pub use production::{
    MAX_CONCURRENT_PRODUCTION_EVALUATIONS, ProductionBackwardPlan, ProductionOrderGenome,
    ProductionSearchIdentity, ProductionSearchTelemetry, compulsory_read_floor,
    construct_production_backward_bypass, search_production_backward,
    select_production_backward_seeds,
    select_production_backward_seeds_with_progress,
};
pub use replay::{
    CertifiedBackwardCandidate, PagingCertificate, ScoredAcceptedBackwardCandidate,
    compile_and_certify_paging, compile_and_score_occurrence_plan, occurrence_plan_from_paging,
};
pub use uniform_pager::solve_uniform_exact_paging;

pub const MAX_PAGER_STATES: usize = 250_000;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct SourceOpCost {
    pub bf_add: u128,
    pub bf_mul: u128,
    pub mixed_add: u128,
    pub mixed_mul: u128,
    pub ext_add: u128,
    pub ext_mul: u128,
}

impl SourceOpCost {
    pub fn primitive_equivalents(self) -> Result<u128, BackwardSearchError> {
        let terms = [
            self.bf_add,
            self.bf_mul,
            self.mixed_add
                .checked_mul(4)
                .ok_or(BackwardSearchError::CostOverflow)?,
            self.mixed_mul
                .checked_mul(4)
                .ok_or(BackwardSearchError::CostOverflow)?,
            self.ext_add
                .checked_mul(4)
                .ok_or(BackwardSearchError::CostOverflow)?,
            self.ext_mul
                .checked_mul(12)
                .ok_or(BackwardSearchError::CostOverflow)?,
        ];
        terms.into_iter().try_fold(0u128, |acc, value| {
            acc.checked_add(value)
                .ok_or(BackwardSearchError::CostOverflow)
        })
    }

    pub fn checked_add(self, rhs: Self) -> Result<Self, BackwardSearchError> {
        let add = |lhs: u128, rhs: u128| {
            lhs.checked_add(rhs)
                .ok_or(BackwardSearchError::CostOverflow)
        };
        Ok(Self {
            bf_add: add(self.bf_add, rhs.bf_add)?,
            bf_mul: add(self.bf_mul, rhs.bf_mul)?,
            mixed_add: add(self.mixed_add, rhs.mixed_add)?,
            mixed_mul: add(self.mixed_mul, rhs.mixed_mul)?,
            ext_add: add(self.ext_add, rhs.ext_add)?,
            ext_mul: add(self.ext_mul, rhs.ext_mul)?,
        })
    }

    pub fn checked_scale(self, scale: u128) -> Result<Self, BackwardSearchError> {
        let mul = |value: u128| {
            value
                .checked_mul(scale)
                .ok_or(BackwardSearchError::CostOverflow)
        };
        Ok(Self {
            bf_add: mul(self.bf_add)?,
            bf_mul: mul(self.bf_mul)?,
            mixed_add: mul(self.mixed_add)?,
            mixed_mul: mul(self.mixed_mul)?,
            ext_add: mul(self.ext_add)?,
            ext_mul: mul(self.ext_mul)?,
        })
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct SourceCost {
    pub plain_read_bytes: u128,
    pub lazy_read_bytes: u128,
    pub materialized_read_bytes: u128,
    pub materialization_write_bytes: u128,
    pub ops: SourceOpCost,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct BackwardScore {
    pub infeasible: bool,
    pub whole_pass_dram_bytes: u128,
    pub primitive_source_ops: u128,
    pub instructions: usize,
    pub encoded_lanes: usize,
    pub arithmetic_ops: usize,
    pub ordinal: usize,
}

impl SourceCost {
    pub fn dram_bytes(self) -> Result<u128, BackwardSearchError> {
        [
            self.plain_read_bytes,
            self.lazy_read_bytes,
            self.materialized_read_bytes,
            self.materialization_write_bytes,
        ]
        .into_iter()
        .try_fold(0u128, |acc, value| {
            acc.checked_add(value)
                .ok_or(BackwardSearchError::CostOverflow)
        })
    }

    pub fn checked_add(self, rhs: Self) -> Result<Self, BackwardSearchError> {
        Ok(Self {
            plain_read_bytes: self
                .plain_read_bytes
                .checked_add(rhs.plain_read_bytes)
                .ok_or(BackwardSearchError::CostOverflow)?,
            lazy_read_bytes: self
                .lazy_read_bytes
                .checked_add(rhs.lazy_read_bytes)
                .ok_or(BackwardSearchError::CostOverflow)?,
            materialized_read_bytes: self
                .materialized_read_bytes
                .checked_add(rhs.materialized_read_bytes)
                .ok_or(BackwardSearchError::CostOverflow)?,
            materialization_write_bytes: self
                .materialization_write_bytes
                .checked_add(rhs.materialization_write_bytes)
                .ok_or(BackwardSearchError::CostOverflow)?,
            ops: self.ops.checked_add(rhs.ops)?,
        })
    }

    pub fn checked_scale(self, scale: u128) -> Result<Self, BackwardSearchError> {
        Ok(Self {
            plain_read_bytes: self
                .plain_read_bytes
                .checked_mul(scale)
                .ok_or(BackwardSearchError::CostOverflow)?,
            lazy_read_bytes: self
                .lazy_read_bytes
                .checked_mul(scale)
                .ok_or(BackwardSearchError::CostOverflow)?,
            materialized_read_bytes: self
                .materialized_read_bytes
                .checked_mul(scale)
                .ok_or(BackwardSearchError::CostOverflow)?,
            materialization_write_bytes: self
                .materialization_write_bytes
                .checked_mul(scale)
                .ok_or(BackwardSearchError::CostOverflow)?,
            ops: self.ops.checked_scale(scale)?,
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RoundProfile {
    pub round: u8,
    pub rows: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SourceRoundBinding {
    pub state: FoldState,
    pub store_for_next_round: bool,
}

#[derive(Debug, PartialEq)]
pub enum BackwardSearchError {
    CostOverflow,
    DuplicateSourceRound {
        desc: u16,
        round: u8,
    },
    MissingSourceRound {
        desc: u16,
        round: u8,
    },
    MalformedRoundSequence,
    VirtualSetupMaterialized {
        desc: u16,
        round: u8,
    },
    BackwardEvaluation(BackwardEvaluationError),
    DuplicateStableFragment,
    MissingStableValue,
    MissingStableSite,
    MissingLeafInstant {
        expr: cs::gkr_compiler::dag_ir::ExprId,
    },
    PagingActionCount {
        expected: usize,
        actual: usize,
    },
    IllegalPagingRetain {
        demand_position: usize,
    },
    PagingLiveSetOverCapacity {
        demand_position: usize,
    },
    UniformPagerMixedWidth {
        demand_position: usize,
        width_lanes: u8,
    },
    ProductionPagerResourceLimit {
        max_states: usize,
    },
    PagingActionUnderflow {
        serve: usize,
    },
    PagingActionLeftover {
        remaining: usize,
    },
    PlacementIntegrationFailure,
    PagingReplayDiverged {
        at_entry: usize,
    },
    PagingReplayIncomplete {
        at_entry: usize,
    },
    PagingReplayRefused {
        count: usize,
    },
    PagingSourceAccessMismatch {
        predicted_reads: u64,
        realized_reads: u64,
        predicted_width_lanes: u64,
        realized_width_lanes: u64,
    },
    PagingReadCostMismatch {
        predicted: SourceCost,
        realized: SourceCost,
    },
    PagingWriteCostMismatch {
        predicted: SourceCost,
        realized: SourceCost,
    },
    PagingOccupancyMismatch {
        position: usize,
        predicted: usize,
        realized: usize,
    },
    PagingCertificateMismatch {
        observable: &'static str,
    },
    InvalidGenomeDomain {
        gene: &'static str,
    },
    NonFiniteGenomeValue {
        gene: &'static str,
    },
    CacheGenomeInfeasible {
        demand_position: usize,
    },
    ExactPagerSolverCapped {
        cap: usize,
        demand_position: usize,
        peak_states: usize,
        generated_states: u64,
        merged_states: u64,
    },
    PagingSeedMismatch,
    InvalidFragmentPermutation,
    SearchDriverFailure {
        reason: &'static str,
    },
}
