//! Finite host-block reserve that keeps one execution's trace producers
//! running.
//!
//! Every producer chunk is one block of the finite host pool, so a pool that
//! can be consumed in full by trace the pipeline has not published yet
//! deadlocks: the producer waits for a free block while the blocks it needs sit
//! inside data nobody can release. [`ProducerBudget`] counts the blocks one
//! execution can legitimately hold at the same time, so a constructor can size
//! the pool strictly above it.
//!
//! The four terms are separate reasons a block is held. They are summed without
//! subtracting their overlap, which is intentional: the result is an upper
//! bound, not an occupancy estimate.
//!
//! - `P` — every stream's prior partial circuit. A circuit's chunks are only
//!   drained at its last row (`produce_and_send_result`), so an unfinished
//!   circuit holds every block it has filled so far.
//! - `S` — blocks one snapshot's newly appended rows can allocate.
//! - `U` — unified instances retained for the inits-and-teardowns tail.
//! - `I` — one inits-and-teardowns instance's three page-aligned series.
//!
//! This module computes numbers only: it allocates no pool, starts no thread
//! and reads no runtime state.

use crate::error::ExecutionProverError;
use crate::prover::ExecutionKind;
use common_constants::TimestampScalar;
use execution_prover_model::circuit_type::{
    CircuitType, DelegationCircuitType, UnrolledCircuitType, UnrolledMemoryCircuitType,
    UnrolledNonMemoryCircuitType,
};
use execution_prover_model::trace::PAGE_SIZE_LOG2;
use execution_prover_model::MachineType;
use riscv_transpiler::witness::delegation::bigint::BigintDelegationWitness;
use riscv_transpiler::witness::delegation::blake2_g_function::Blake2sGFunctionDelegationWitness;
use riscv_transpiler::witness::delegation::blake2_round_function::Blake2sRoundFunctionDelegationWitness;
use riscv_transpiler::witness::delegation::keccak_special5::KeccakSpecial5DelegationWitness;
use riscv_transpiler::witness::{
    MemoryOpcodeTracingDataWithTimestamp, NonMemoryOpcodeTracingDataWithTimestamp,
    UnifiedOpcodeTracingDataWithTimestamp,
};

/// Guest cycles between two snapshot publications.
///
/// The checkpoint the shared `SimulationRunner` opts into, read from the JIT
/// rather than restated: a literal here would silently diverge from the
/// interval the producer actually publishes at, and the whole bound depends on
/// the two agreeing.
pub const SNAPSHOT_CYCLE_INTERVAL: usize =
    riscv_transpiler::jit::DEFAULT_MAX_CYCLES_PER_SNAPSHOT as usize;

/// Largest cycle advance a single emitted instruction group can make.
///
/// The checkpoint is only tested between groups, so a snapshot can overshoot
/// the interval by one group. Taken from the emitter, which derives it over
/// every supported lowering group and enforces it when emitting — reproducing
/// the reasoning here would let the two drift.
pub const MAX_CYCLES_PER_INSTRUCTION_GROUP: usize =
    riscv_transpiler::jit::MAX_CYCLES_PER_INSTRUCTION_GROUP;

/// Rows one producer counter gains per guest cycle.
///
/// From the emitter, which derives it from `record_circuit_type` increments and
/// timestamp advances together.
pub const MAX_COUNTER_INCREMENT_PER_CYCLE: usize =
    riscv_transpiler::jit::MAX_COUNTER_INCREMENT_PER_CYCLE;

/// Everything the budget is computed from.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ProducerBudgetInputs {
    pub execution_kind: ExecutionKind,
    pub machine_type: MachineType,
    /// Bytes one host trace block holds (`HostTraceAllocator::capacity`).
    pub block_bytes: usize,
    /// Guest RAM the run is configured with (`JitRunnerRam::ram_size`).
    pub ram_bytes: usize,
    pub snapshot_cycle_interval: usize,
    pub max_cycles_per_instruction_group: usize,
    /// Rows one producer counter gains per guest cycle, from emitter
    /// semantics — never from the representable range of
    /// `record_circuit_type`'s `u16` parameter.
    pub max_counter_increment_per_cycle: usize,
}

impl ProducerBudgetInputs {
    pub fn new(
        execution_kind: ExecutionKind,
        machine_type: MachineType,
        block_bytes: usize,
        ram_bytes: usize,
    ) -> Self {
        Self {
            execution_kind,
            machine_type,
            block_bytes,
            ram_bytes,
            snapshot_cycle_interval: SNAPSHOT_CYCLE_INTERVAL,
            max_cycles_per_instruction_group: MAX_CYCLES_PER_INSTRUCTION_GROUP,
            max_counter_increment_per_cycle: MAX_COUNTER_INCREMENT_PER_CYCLE,
        }
    }

    /// Counter rows one snapshot can append to a single stream: a full interval
    /// plus the group that crossed the checkpoint.
    fn snapshot_rows(&self) -> Result<usize, ExecutionProverError> {
        if self.max_cycles_per_instruction_group == 0 {
            return Err(ExecutionProverError::invalid_configuration(
                "max_cycles_per_instruction_group",
                "an emitted instruction group advances at least one cycle",
            ));
        }
        let cycles = checked_add(
            "snapshot_cycle_interval",
            self.snapshot_cycle_interval,
            self.max_cycles_per_instruction_group,
        )? - 1;
        // A counter's rows are its cycles times its declared per-cycle
        // increment. The multiplier is 1 today — a 649-cycle keccak group bills
        // 649 rows, not 649 per cycle — but it is applied explicitly so a
        // change on the emitter side flows through instead of silently
        // invalidating this bound.
        //
        // The emitter exposes this exact expression as
        // `riscv_transpiler::jit::max_counter_delta_per_snapshot`. It is
        // recomputed here rather than called because these inputs are fields,
        // not the production constants: the overflow tests drive them to values
        // the emitter's `u32` interval cannot represent. The equality is pinned
        // by a test instead.
        checked_mul(
            "max_counter_increment_per_cycle",
            cycles,
            self.max_counter_increment_per_cycle,
        )
    }
}

/// Blocks one execution can hold at once, by reason.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ProducerBudget {
    /// `P`: partial circuits across every stream.
    pub partial_stream_blocks: usize,
    /// `S`: blocks one snapshot's appended rows can allocate.
    pub unpublished_snapshot_blocks: usize,
    /// `U`: unified instances retained for the inits-and-teardowns tail.
    pub retained_unified_blocks: usize,
    /// `I`: one inits-and-teardowns instance.
    pub inits_and_teardowns_blocks: usize,
    /// `R = P + S + U + I`.
    pub reserve_blocks: usize,
}

impl ProducerBudget {
    pub fn compute(inputs: &ProducerBudgetInputs) -> Result<Self, ExecutionProverError> {
        let split_streams = split_streams();
        let unified_streams = unified_streams();
        let streams: &[StreamGeometry] = match inputs.execution_kind {
            ExecutionKind::Unrolled => &split_streams,
            ExecutionKind::Unified => {
                // `UnifiedTracingDataProducers::new` asserts this; reject it
                // before any resource exists instead of aborting a worker.
                if inputs.machine_type != MachineType::Reduced {
                    return Err(ExecutionProverError::invalid_configuration(
                        "machine_type",
                        format!(
                            "unified execution is defined for {:?} only, got {:?}",
                            MachineType::Reduced,
                            inputs.machine_type
                        ),
                    ));
                }
                &unified_streams
            }
        };

        let snapshot_rows = inputs.snapshot_rows()?;
        let mut partial_stream_blocks = 0usize;
        let mut unpublished_snapshot_blocks = 0usize;
        for stream in streams {
            let rows_per_block = rows_per_block(inputs.block_bytes, stream.row_size, stream.name)?;
            partial_stream_blocks = checked_add(
                "partial_stream_blocks",
                partial_stream_blocks,
                ceil_div(stream.domain_size, rows_per_block, stream.name)?,
            )?;
            unpublished_snapshot_blocks = checked_add(
                "unpublished_snapshot_blocks",
                unpublished_snapshot_blocks,
                snapshot_blocks(
                    snapshot_rows,
                    rows_per_block,
                    stream.domain_size,
                    stream.name,
                )?,
            )?;
        }

        let retained_unified_blocks = match inputs.execution_kind {
            ExecutionKind::Unrolled => 0,
            ExecutionKind::Unified => {
                retained_unified_blocks(inputs.block_bytes, inputs.ram_bytes)?
            }
        };
        let inits_and_teardowns_blocks = inits_and_teardowns_blocks(
            inits_and_teardowns_carrier(inputs.execution_kind),
            inputs.block_bytes,
        )?;

        let reserve_blocks = checked_add(
            "reserve_blocks",
            partial_stream_blocks,
            unpublished_snapshot_blocks,
        )?;
        let reserve_blocks =
            checked_add("reserve_blocks", reserve_blocks, retained_unified_blocks)?;
        let reserve_blocks =
            checked_add("reserve_blocks", reserve_blocks, inits_and_teardowns_blocks)?;

        Ok(Self {
            partial_stream_blocks,
            unpublished_snapshot_blocks,
            retained_unified_blocks,
            inits_and_teardowns_blocks,
            reserve_blocks,
        })
    }
}

/// One `TracingDataProducer`'s row type and circuit domain.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct StreamGeometry {
    name: &'static str,
    /// `size_of` the row type the producer's `Vec` holds.
    row_size: usize,
    /// `cycles_per_circuit_for`, i.e. the circuit's full domain.
    domain_size: usize,
}

impl StreamGeometry {
    fn new<T>(name: &'static str, circuit_type: CircuitType) -> Self {
        Self {
            name,
            row_size: size_of::<T>(),
            domain_size: circuit_type.get_domain_size(),
        }
    }
}

/// The four producers `DelegationProducers::new` builds, in its order.
///
/// Both `SplitTracingDataProducers` and `UnifiedTracingDataProducers` construct
/// this set identically and unconditionally.
fn delegation_streams() -> [StreamGeometry; 4] {
    [
        StreamGeometry::new::<Blake2sRoundFunctionDelegationWitness>(
            "blake2 round function delegation",
            CircuitType::Delegation(DelegationCircuitType::Blake2WithCompression),
        ),
        StreamGeometry::new::<BigintDelegationWitness>(
            "bigint delegation",
            CircuitType::Delegation(DelegationCircuitType::BigIntWithControl),
        ),
        StreamGeometry::new::<KeccakSpecial5DelegationWitness>(
            "keccak special5 delegation",
            CircuitType::Delegation(DelegationCircuitType::KeccakSpecial5),
        ),
        StreamGeometry::new::<Blake2sGFunctionDelegationWitness>(
            "blake2 g function delegation",
            CircuitType::Delegation(DelegationCircuitType::Blake2GFunction),
        ),
    ]
}

/// Every producer `SplitTracingDataProducers::new` constructs.
///
/// That constructor takes `_machine_type` and ignores it, so all ten producers
/// exist for every machine type — including the families a given machine never
/// executes. Each one still holds whatever blocks it has been handed, so the
/// budget has to count them. Deriving this set from
/// `get_circuit_types_for_machine_type` instead would under-count.
fn split_streams() -> [StreamGeometry; 10] {
    let [blake, bigint, keccak, blake_g] = delegation_streams();
    [
        blake,
        bigint,
        keccak,
        blake_g,
        StreamGeometry::new::<NonMemoryOpcodeTracingDataWithTimestamp>(
            "add/sub/lui/auipc/mop family",
            CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
                UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop,
            )),
        ),
        StreamGeometry::new::<NonMemoryOpcodeTracingDataWithTimestamp>(
            "binary/shift/csr family",
            CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
                UnrolledNonMemoryCircuitType::ShiftBinary,
            )),
        ),
        StreamGeometry::new::<NonMemoryOpcodeTracingDataWithTimestamp>(
            "slt/branch family",
            CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
                UnrolledNonMemoryCircuitType::JumpBranchSlt,
            )),
        ),
        StreamGeometry::new::<NonMemoryOpcodeTracingDataWithTimestamp>(
            "mul/div family",
            CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
                UnrolledNonMemoryCircuitType::MulDivUnsigned,
            )),
        ),
        StreamGeometry::new::<MemoryOpcodeTracingDataWithTimestamp>(
            "word-size memory family",
            CircuitType::Unrolled(UnrolledCircuitType::Memory(
                UnrolledMemoryCircuitType::LoadStoreWordOnly,
            )),
        ),
        StreamGeometry::new::<MemoryOpcodeTracingDataWithTimestamp>(
            "subword-size memory family",
            CircuitType::Unrolled(UnrolledCircuitType::Memory(
                UnrolledMemoryCircuitType::LoadStoreSubwordOnly,
            )),
        ),
    ]
}

/// Every producer `UnifiedTracingDataProducers::new` constructs: the shared
/// delegation set plus the single unified-cycles producer.
fn unified_streams() -> [StreamGeometry; 5] {
    let [blake, bigint, keccak, blake_g] = delegation_streams();
    [
        blake,
        bigint,
        keccak,
        blake_g,
        StreamGeometry::new::<UnifiedOpcodeTracingDataWithTimestamp>(
            "unified cycles",
            CircuitType::Unrolled(UnrolledCircuitType::Unified),
        ),
    ]
}

/// Which circuit carries the inits-and-teardowns sets, chosen exactly as
/// `run_simulator` chooses it from `TracingType::IS_SPLIT`.
fn inits_and_teardowns_carrier(execution_kind: ExecutionKind) -> UnrolledCircuitType {
    match execution_kind {
        ExecutionKind::Unrolled => UnrolledCircuitType::InitsAndTeardowns,
        ExecutionKind::Unified => UnrolledCircuitType::Unified,
    }
}

/// `S_s`: blocks one snapshot's appended rows can newly allocate for a stream.
///
/// `length` consecutive appended rows intersect at most `ceil(length/domain)+1`
/// circuit segments. Every segment after the first starts at circuit row zero,
/// because `produce_and_send_result` drains the deque at each circuit boundary,
/// so it needs `ceil(segment/rows_per_block)` blocks; the first segment starts
/// at an arbitrary offset inside an existing chunk, which one extra block
/// covers. Summing the rounded segment lengths gives at most
/// `ceil(length/rows_per_block) + ceil(length/domain) + 1`.
///
/// Zero appended rows allocate nothing: `process_snapshot` allocates inside its
/// `while start != end` loop and never eagerly for a next circuit.
///
/// Validated by exhaustive simulation against a literal transcription of the
/// producer loop (`.agents/audits/2026-09-18-execution-prover-budget.md`, and
/// `snapshot_bound_holds_against_the_producer_allocation_oracle` below). Do not
/// substitute another formula without redoing that.
fn snapshot_blocks(
    length: usize,
    rows_per_block: usize,
    domain_size: usize,
    name: &'static str,
) -> Result<usize, ExecutionProverError> {
    if length == 0 {
        return Ok(0);
    }
    let by_capacity = ceil_div(length, rows_per_block, name)?;
    let by_circuit = ceil_div(length, domain_size, name)?;
    let blocks = checked_add(name, by_capacity, by_circuit)?;
    checked_add(name, blocks, 1)
}

/// `U`: unified instances held back for the inits-and-teardowns tail.
///
/// In unified execution the i&t sets ride inside trailing unified instances, so
/// up to `max_instances` whole unified circuits stay unpublished until the
/// simulator has walked memory. `max_instances` is recomputed here from the
/// same RAM and circuit geometry as `InitsAndTeardownsGeometry::max_instances`
/// in `workers/simulation.rs`, which is private to that module.
fn retained_unified_blocks(
    block_bytes: usize,
    ram_bytes: usize,
) -> Result<usize, ExecutionProverError> {
    const NAME: &str = "retained_unified_blocks";
    let carrier = UnrolledCircuitType::Unified;
    // `run_simulator` passes `memory_holder.memory().len()`, which is the guest
    // RAM in `u32` words.
    if !ram_bytes.is_multiple_of(size_of::<u32>()) {
        return Err(ExecutionProverError::invalid_configuration(
            "ram_bytes",
            format!("{ram_bytes} is not a whole number of 32-bit guest words"),
        ));
    }
    let ram_words = ram_bytes / size_of::<u32>();
    let windows_in_ram = ceil_div(ram_words, carrier.get_domain_size(), NAME)?;
    let max_instances = ceil_div(
        windows_in_ram,
        carrier.get_num_inits_and_teardowns_sets(),
        NAME,
    )?;
    let rows_per_block = rows_per_block(
        block_bytes,
        size_of::<UnifiedOpcodeTracingDataWithTimestamp>(),
        NAME,
    )?;
    let blocks_per_instance = ceil_div(carrier.get_domain_size(), rows_per_block, NAME)?;
    checked_mul(NAME, max_instances, blocks_per_instance)
}

/// `I`: blocks one inits-and-teardowns instance's three series occupy.
///
/// An instance covers `num_sets` windows of `domain_size` words, so it holds at
/// most `num_sets * domain_size / page_size` touched pages: one `page_indices`
/// entry and one whole page of values and of timestamps each.
/// `chunk_into_blocks` rounds the value and timestamp block capacities *down*
/// to whole pages (`alignment_in_items`), which is what makes those two terms
/// larger than a plain byte division.
fn inits_and_teardowns_blocks(
    carrier: UnrolledCircuitType,
    block_bytes: usize,
) -> Result<usize, ExecutionProverError> {
    const NAME: &str = "inits_and_teardowns_blocks";
    if carrier.get_domain_size_log2() < PAGE_SIZE_LOG2 {
        return Err(ExecutionProverError::invalid_configuration(
            "inits_and_teardowns carrier",
            format!(
                "trace_len_log2 {} is below page size log2 {PAGE_SIZE_LOG2}",
                carrier.get_domain_size_log2()
            ),
        ));
    }
    let page_size = 1usize << PAGE_SIZE_LOG2;
    let pages_per_set = carrier.get_domain_size() >> PAGE_SIZE_LOG2;
    let pages = checked_mul(
        NAME,
        carrier.get_num_inits_and_teardowns_sets(),
        pages_per_set,
    )?;
    let packed_items = checked_mul(NAME, pages, page_size)?;

    let index_rows = rows_per_block(block_bytes, size_of::<u32>(), NAME)?;
    let value_rows = page_aligned_rows_per_block(block_bytes, size_of::<u32>(), page_size, NAME)?;
    let timestamp_rows =
        page_aligned_rows_per_block(block_bytes, size_of::<TimestampScalar>(), page_size, NAME)?;

    let blocks = ceil_div(pages, index_rows, NAME)?;
    let blocks = checked_add(NAME, blocks, ceil_div(packed_items, value_rows, NAME)?)?;
    checked_add(NAME, blocks, ceil_div(packed_items, timestamp_rows, NAME)?)
}

/// `q_s = floor(block_bytes / row_size)`, the rows a producer carves out of one
/// block (`allocator.capacity() / size_of::<T>()`).
fn rows_per_block(
    block_bytes: usize,
    row_size: usize,
    name: &str,
) -> Result<usize, ExecutionProverError> {
    if row_size == 0 {
        return Err(ExecutionProverError::invalid_configuration(
            "block_bytes",
            format!("{name} has a zero-sized row type"),
        ));
    }
    let rows = block_bytes / row_size;
    if rows == 0 {
        return Err(ExecutionProverError::invalid_configuration(
            "block_bytes",
            format!("a {block_bytes}-byte block holds no whole {name} row of {row_size} bytes"),
        ));
    }
    Ok(rows)
}

/// The same capacity rounded down to whole pages, matching `chunk_into_blocks`.
/// A block below one page cannot make progress at all, which that function
/// asserts; reject it here instead.
fn page_aligned_rows_per_block(
    block_bytes: usize,
    row_size: usize,
    page_size: usize,
    name: &str,
) -> Result<usize, ExecutionProverError> {
    let rows = rows_per_block(block_bytes, row_size, name)?;
    let aligned = (rows / page_size) * page_size;
    if aligned == 0 {
        return Err(ExecutionProverError::invalid_configuration(
            "block_bytes",
            format!(
                "a {block_bytes}-byte block holds {rows} {name} items, below one \
                 {page_size}-item page"
            ),
        ));
    }
    Ok(aligned)
}

fn ceil_div(value: usize, divisor: usize, name: &str) -> Result<usize, ExecutionProverError> {
    if divisor == 0 {
        return Err(ExecutionProverError::invalid_configuration(
            "producer budget",
            format!("{name} divided by zero"),
        ));
    }
    Ok(value.div_ceil(divisor))
}

fn checked_add(name: &str, a: usize, b: usize) -> Result<usize, ExecutionProverError> {
    a.checked_add(b).ok_or_else(|| {
        ExecutionProverError::invalid_configuration(
            "producer budget",
            format!("{name} overflowed adding {a} + {b}"),
        )
    })
}

fn checked_mul(name: &str, a: usize, b: usize) -> Result<usize, ExecutionProverError> {
    a.checked_mul(b).ok_or_else(|| {
        ExecutionProverError::invalid_configuration(
            "producer budget",
            format!("{name} overflowed multiplying {a} * {b}"),
        )
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use riscv_transpiler::jit::JitRunnerRam;
    use std::cmp::min;

    const BLOCK_BYTES_64_MIB: usize = 64 << 20;

    fn inputs(
        execution_kind: ExecutionKind,
        machine_type: MachineType,
        ram: JitRunnerRam,
    ) -> ProducerBudgetInputs {
        ProducerBudgetInputs::new(
            execution_kind,
            machine_type,
            BLOCK_BYTES_64_MIB,
            ram.ram_size(),
        )
    }

    fn report(label: &str, inputs: &ProducerBudgetInputs) -> ProducerBudget {
        let budget = ProducerBudget::compute(inputs).unwrap();
        let snapshot_rows = inputs.snapshot_rows().unwrap();
        let split = split_streams();
        let unified = unified_streams();
        let streams: &[StreamGeometry] = match inputs.execution_kind {
            ExecutionKind::Unrolled => &split,
            ExecutionKind::Unified => &unified,
        };
        println!(
            "--- {label} (block {} B, L {snapshot_rows}) ---",
            inputs.block_bytes
        );
        for stream in streams {
            let q = rows_per_block(inputs.block_bytes, stream.row_size, stream.name).unwrap();
            let f = ceil_div(stream.domain_size, q, stream.name).unwrap();
            let s = snapshot_blocks(snapshot_rows, q, stream.domain_size, stream.name).unwrap();
            println!(
                "  {:<34} w={:<4} D={:<10} q={:<8} F={:<4} S_s={}",
                stream.name, stream.row_size, stream.domain_size, q, f, s
            );
        }
        println!(
            "  P={} S={} U={} I={} R={}",
            budget.partial_stream_blocks,
            budget.unpublished_snapshot_blocks,
            budget.retained_unified_blocks,
            budget.inits_and_teardowns_blocks,
            budget.reserve_blocks
        );
        budget
    }

    /// Pins the reviewed production totals from
    /// `.agents/audits/2026-09-18-execution-prover-budget.md`.
    #[test]
    fn production_geometry_matches_the_reviewed_reserve() {
        for ram in [JitRunnerRam::Medium, JitRunnerRam::Full] {
            let budget = report(
                &format!("unrolled FullUnsigned, {:?} RAM", ram),
                &inputs(ExecutionKind::Unrolled, MachineType::FullUnsigned, ram),
            );
            assert_eq!(
                budget,
                ProducerBudget {
                    partial_stream_blocks: 123,
                    unpublished_snapshot_blocks: 49,
                    retained_unified_blocks: 0,
                    inits_and_teardowns_blocks: 25,
                    reserve_blocks: 197,
                }
            );
        }

        let budget = report(
            "unified Reduced, 1 GiB RAM",
            &inputs(
                ExecutionKind::Unified,
                MachineType::Reduced,
                JitRunnerRam::Medium,
            ),
        );
        assert_eq!(
            budget,
            ProducerBudget {
                partial_stream_blocks: 54,
                unpublished_snapshot_blocks: 34,
                retained_unified_blocks: 128,
                inits_and_teardowns_blocks: 4,
                reserve_blocks: 220,
            }
        );

        let budget = report(
            "unified Reduced, 4 GiB RAM",
            &inputs(
                ExecutionKind::Unified,
                MachineType::Reduced,
                JitRunnerRam::Full,
            ),
        );
        assert_eq!(
            budget,
            ProducerBudget {
                partial_stream_blocks: 54,
                unpublished_snapshot_blocks: 34,
                retained_unified_blocks: 512,
                inits_and_teardowns_blocks: 4,
                reserve_blocks: 604,
            }
        );
    }

    /// `SplitTracingDataProducers::new` ignores its `machine_type`, so the
    /// unrolled reserve must not shrink for a machine that never executes some
    /// of the families it still constructs.
    #[test]
    fn split_budget_ignores_machine_type() {
        let reference = ProducerBudget::compute(&inputs(
            ExecutionKind::Unrolled,
            MachineType::Full,
            JitRunnerRam::Medium,
        ))
        .unwrap();
        for machine_type in [MachineType::FullUnsigned, MachineType::Reduced] {
            let budget = ProducerBudget::compute(&inputs(
                ExecutionKind::Unrolled,
                machine_type,
                JitRunnerRam::Medium,
            ))
            .unwrap();
            assert_eq!(budget, reference, "{machine_type:?}");
        }
    }

    #[test]
    fn unified_execution_rejects_non_reduced_machines() {
        for machine_type in [MachineType::Full, MachineType::FullUnsigned] {
            assert!(ProducerBudget::compute(&inputs(
                ExecutionKind::Unified,
                machine_type,
                JitRunnerRam::Medium
            ))
            .is_err());
        }
    }

    /// Allocation-visible behaviour of `TracingDataProducer::process_snapshot`,
    /// transcribed literally: allocate only when the back chunk is absent or
    /// full, append up to the circuit boundary, and drop every chunk at each
    /// boundary because `produce_and_send_result` drains the deque there.
    ///
    /// `initial_fill == 0` models an empty deque; any other value models a back
    /// chunk already holding that many rows.
    fn oracle_new_blocks(
        domain_size: usize,
        rows_per_block: usize,
        mut start: usize,
        initial_fill: usize,
        length: usize,
    ) -> usize {
        let end = start + length;
        let mut back_len = (initial_fill > 0).then_some(initial_fill);
        let mut allocations = 0;
        while start != end {
            let next_circuit_boundary = (start + 1).next_multiple_of(domain_size);
            if back_len.is_none_or(|len| len == rows_per_block) {
                allocations += 1;
                back_len = Some(0);
            }
            let len = back_len.unwrap();
            let spare_capacity = rows_per_block - len;
            let segment_end = min(end, next_circuit_boundary);
            let diff = min(spare_capacity, segment_end - start);
            assert_ne!(diff, 0);
            back_len = Some(len + diff);
            start += diff;
            if start.is_multiple_of(domain_size) {
                back_len = None;
            }
        }
        allocations
    }

    #[test]
    fn snapshot_bound_holds_against_the_producer_allocation_oracle() {
        let mut cases = 0usize;
        for domain_size in 1..=16usize {
            for rows_per_block in 1..=8usize {
                for start in 0..domain_size {
                    for initial_fill in 0..=rows_per_block {
                        for length in 0..=2 * domain_size + 1 {
                            let bound =
                                snapshot_blocks(length, rows_per_block, domain_size, "oracle")
                                    .unwrap();
                            let actual = oracle_new_blocks(
                                domain_size,
                                rows_per_block,
                                start,
                                initial_fill,
                                length,
                            );
                            assert!(
                                actual <= bound,
                                "D={domain_size} q={rows_per_block} start={start} \
                                 fill={initial_fill} L={length}: {actual} > {bound}"
                            );
                            cases += 1;
                        }
                    }
                }
            }
        }
        assert_eq!(cases, 143_616);
    }

    #[test]
    fn a_block_too_small_for_one_row_is_rejected() {
        let mut inputs = inputs(
            ExecutionKind::Unrolled,
            MachineType::FullUnsigned,
            JitRunnerRam::Medium,
        );
        inputs.block_bytes = 0;
        assert!(ProducerBudget::compute(&inputs).is_err());

        // Large enough for every row type, but below one whole page of packed
        // i&t timestamps, which `chunk_into_blocks` rounds down to.
        inputs.block_bytes = (1usize << PAGE_SIZE_LOG2) * size_of::<TimestampScalar>() - 1;
        assert!(ProducerBudget::compute(&inputs).is_err());
    }

    #[test]
    fn a_zero_cycle_instruction_group_is_rejected() {
        let mut inputs = inputs(
            ExecutionKind::Unrolled,
            MachineType::FullUnsigned,
            JitRunnerRam::Medium,
        );
        inputs.max_cycles_per_instruction_group = 0;
        assert!(inputs.snapshot_rows().is_err());
        assert!(ProducerBudget::compute(&inputs).is_err());
    }

    #[test]
    fn an_overflowing_snapshot_length_is_an_error_not_a_wrap() {
        let mut inputs = inputs(
            ExecutionKind::Unrolled,
            MachineType::FullUnsigned,
            JitRunnerRam::Medium,
        );
        inputs.snapshot_cycle_interval = usize::MAX;
        assert!(inputs.snapshot_rows().is_err());
        assert!(ProducerBudget::compute(&inputs).is_err());
    }

    /// Once `L` is admitted, `S_s = ceil(L/q) + ceil(L/D) + 1` can still
    /// overflow at a capacity of one row per block, so the term carries its own
    /// checked arithmetic even though the production geometry below never
    /// reaches it.
    #[test]
    fn an_overflowing_snapshot_term_is_an_error_not_a_wrap() {
        assert!(snapshot_blocks(usize::MAX, 1, 1, "t").is_err());
        assert!(snapshot_blocks(usize::MAX, 1, usize::MAX, "t").is_err());
        assert_eq!(snapshot_blocks(0, 1, 1, "t").unwrap(), 0);
    }

    /// The summed terms are each bounded by fixed circuit geometry once a
    /// block has passed validation: `P` by `sum(D_s)`, `I` by
    /// `num_sets * domain_size`, `U` by `ram_words / num_sets * domain_size`,
    /// and `S` by ten streams' `L / q` with `q` at least one page of packed
    /// timestamps. No input overflows them on a 64-bit `usize`, so their
    /// checked helpers are exercised directly here instead.
    #[test]
    fn checked_helpers_report_overflow_instead_of_wrapping() {
        assert!(checked_add("t", usize::MAX, 1).is_err());
        assert!(checked_mul("t", usize::MAX / 2 + 1, 2).is_err());
        assert!(ceil_div(1, 0, "t").is_err());
        assert_eq!(checked_add("t", usize::MAX - 1, 1).unwrap(), usize::MAX);
        assert_eq!(checked_mul("t", usize::MAX / 2, 2).unwrap(), usize::MAX - 1);
        assert_eq!(ceil_div(7, 4, "t").unwrap(), 2);
    }

    #[test]
    fn ram_that_is_not_a_whole_number_of_guest_words_is_rejected() {
        let mut inputs = inputs(
            ExecutionKind::Unified,
            MachineType::Reduced,
            JitRunnerRam::Medium,
        );
        inputs.ram_bytes += 1;
        assert!(ProducerBudget::compute(&inputs).is_err());
    }
}

#[cfg(test)]
mod emitter_agreement {
    use super::*;

    /// The locally computed `L_s` must equal the emitter's own helper for the
    /// production interval. They are separate expressions over the same
    /// constants, so only a test keeps them from drifting.
    #[test]
    fn local_snapshot_rows_match_the_emitter_helper() {
        let inputs = ProducerBudgetInputs::new(
            ExecutionKind::Unrolled,
            MachineType::FullUnsigned,
            1 << 26,
            riscv_transpiler::jit::JitRunnerRam::Medium.ram_size(),
        );
        assert_eq!(
            inputs.snapshot_rows().unwrap(),
            riscv_transpiler::jit::max_counter_delta_per_snapshot(
                riscv_transpiler::jit::DEFAULT_MAX_CYCLES_PER_SNAPSHOT
            ),
        );
    }
}
