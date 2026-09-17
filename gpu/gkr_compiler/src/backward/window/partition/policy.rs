//! Program- and device-only partition count selector for R0 window programs. The
//! original entry is kept when the unique source footprint fits
//! one block's modeled cache share, or when the typed issue estimate dominates the unique-input
//! memory time; otherwise the candidate with the lowest footprint pressure wins, fewer parts on a
//! tie. It knows no circuit or layer identity and consumes no measured times. A cache share and a
//! peak issue/bandwidth balance are approximations, not performance guarantees.
use super::super::{
    WindowLoweringError, WindowProgram, WINDOW_OPCODE_GROUP_BF, WINDOW_OPCODE_GROUP_E4,
    WINDOW_OPCODE_LINEAR_BF_PROCEDURAL, WINDOW_OPCODE_LINEAR_E4_WIDE,
    WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_AB, WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_B,
    WINDOW_OPCODE_PRODUCT_E4_E4,
};
use super::{Partitioner, R0PartitionPlan};

// Opcodes shared with the native window ABI.
const OPCODE_LINEAR_BF: u16 = 0;
const OPCODE_PRODUCT_BF_BF: u16 = 2;
const OPCODE_PRODUCT_BF_E4: u16 = 3;
const ID_MASK: u16 = (1 << 15) - 1;

/// The nine selector warps of a block.
const SELECTOR_WARPS: f64 = 9.0;
/// Partition counts the runtime may request; the first is the unsplit original.
pub const REQUESTED_PARTS: [usize; 5] = [1, 2, 4, 8, 16];

/// Estimated issued instructions per selector warp for each record kind.
mod weight {
    pub const BF_HEAD: f64 = 90.0;
    pub const BF_MEMBER_PRODUCT: f64 = 45.0;
    pub const BF_MEMBER_TAIL: f64 = 25.0;
    pub const BF_PRODUCT: f64 = 110.0;
    pub const BF_LINEAR: f64 = 60.0;
    pub const E4_LINEAR: f64 = 130.0;
    pub const E4_SINGLETON_MIXED: f64 = 226.0;
    pub const E4_SINGLETON_FULL: f64 = 376.0;
    pub const E4_HEAD: f64 = 60.0;
    pub const E4_PAIR_MEMBER_MIXED: f64 = 120.0;
    pub const E4_PAIR_MEMBER_FULL: f64 = 250.0;
}

/// Device geometry and rates the selector needs, all queryable or probed on the actual entries.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct R0PartitionHardware {
    pub sm_count: usize,
    /// Modeled cache capacity; zero disables partitioning.
    pub l2_bytes: usize,
    pub clock_hz: f64,
    pub memory_bytes_per_second: f64,
    /// Warp issue slots per SM per cycle: an architectural assumption, not a CUDA attribute.
    pub issue_slots_per_sm_cycle: f64,
    /// Resident blocks per SM of the original entry for this program's kernel family.
    pub original_blocks_per_sm: usize,
    /// Resident blocks per SM of the grid partition entry for this program's kernel family.
    pub grid_blocks_per_sm: usize,
}

impl R0PartitionHardware {
    fn validate(&self) -> Result<(), WindowLoweringError> {
        if self.sm_count == 0 {
            return Err(invalid("hardware has no SMs"));
        }
        for (name, rate) in [
            ("clock", self.clock_hz),
            ("memory bandwidth", self.memory_bytes_per_second),
            ("issue slots", self.issue_slots_per_sm_cycle),
        ] {
            if !rate.is_finite() || rate <= 0.0 {
                return Err(invalid(format!(
                    "hardware {name} rate is not finite and positive"
                )));
            }
        }
        if self.original_blocks_per_sm == 0 || self.grid_blocks_per_sm == 0 {
            return Err(invalid("entry has no resident blocks"));
        }
        Ok(())
    }

    fn cache_share(&self, blocks_per_sm: usize, grid_blocks: usize) -> f64 {
        self.l2_bytes as f64 / grid_blocks.min(self.sm_count * blocks_per_sm) as f64
    }
}

fn invalid(message: impl Into<String>) -> WindowLoweringError {
    WindowLoweringError::Encoding(message.into())
}

/// The cached partition plans of one program for every requestable count, and its generic work.
#[derive(Clone, Debug, PartialEq)]
pub struct R0PartitionCandidates {
    pub plans: Vec<R0PartitionPlan>,
    total_bytes_per_tile: usize,
    work_per_tile: f64,
}

impl R0PartitionCandidates {
    /// Compile device-independent candidates and estimate their instruction work.
    pub fn new(program: &WindowProgram) -> Result<Self, WindowLoweringError> {
        let partitioner = Partitioner::new(program)?;
        let mut plans: Vec<R0PartitionPlan> = Vec::new();
        for requested in REQUESTED_PARTS {
            let parts = requested.min(partitioner.components.len()).max(1);
            if plans.last().is_none_or(|plan| plan.parts.len() != parts) {
                plans.push(partitioner.plan(parts)?);
            }
        }
        let total_bytes_per_tile = plans[0].source_bytes_per_tile.iter().sum();
        if plans
            .iter()
            .any(|plan| plan.source_bytes_per_tile.iter().sum::<usize>() != total_bytes_per_tile)
        {
            return Err(invalid(
                "source-disjoint candidates must conserve the footprint",
            ));
        }
        Ok(Self {
            plans,
            total_bytes_per_tile,
            work_per_tile: work_per_tile(program, &partitioner.units)?,
        })
    }

    /// The validated rule: keep the original when the footprint fits one block's modeled cache
    /// share or the typed issue estimate dominates the unique-input memory time; otherwise the
    /// lowest footprint pressure, fewer parts on a tie.
    pub fn select(
        &self,
        row_tiles: usize,
        hardware: &R0PartitionHardware,
    ) -> Result<&R0PartitionPlan, WindowLoweringError> {
        if row_tiles == 0 {
            return Err(invalid("a window launch needs at least one row tile"));
        }
        hardware.validate()?;
        let tiles = row_tiles as f64;
        let active_sms = hardware.sm_count.min(row_tiles) as f64;
        let memory_seconds =
            self.total_bytes_per_tile as f64 * tiles / hardware.memory_bytes_per_second;
        let issue_seconds = self.work_per_tile * tiles
            / (active_sms * hardware.clock_hz * hardware.issue_slots_per_sm_cycle);
        if hardware.l2_bytes == 0
            || self.total_bytes_per_tile as f64
                <= hardware.cache_share(hardware.original_blocks_per_sm, row_tiles)
            || memory_seconds <= issue_seconds
        {
            return Ok(&self.plans[0]);
        }
        let mut best: Option<((f64, usize), usize)> = None;
        for (index, plan) in self.plans.iter().enumerate() {
            let parts = plan.parts.len();
            let blocks_per_sm = if parts == 1 {
                hardware.original_blocks_per_sm
            } else {
                hardware.grid_blocks_per_sm
            };
            let share = hardware.cache_share(blocks_per_sm, row_tiles * parts);
            let largest = *plan
                .source_bytes_per_tile
                .iter()
                .max()
                .expect("nonempty plan");
            let pressure = (largest as f64 / share).max(1.0);
            let key = (pressure, parts);
            let better = best.as_ref().is_none_or(|(current, _)| key < *current);
            if better {
                best = Some((key, index));
            }
        }
        let (_, index) = best.expect("the original candidate always qualifies");
        Ok(&self.plans[index])
    }
}

fn is_bf_product(opcode: u16) -> bool {
    matches!(
        opcode,
        OPCODE_PRODUCT_BF_BF
            | WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_B
            | WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_AB
    )
}

fn is_bf_linear(opcode: u16) -> bool {
    matches!(
        opcode,
        OPCODE_LINEAR_BF | WINDOW_OPCODE_LINEAR_BF_PROCEDURAL
    )
}

fn work_per_tile(
    program: &WindowProgram,
    units: &[super::Unit],
) -> Result<f64, WindowLoweringError> {
    let mut work = 0.0;
    for unit in units {
        let words = &program.words[unit.words.clone()];
        work += match (unit.section, words[0]) {
            (0, WINDOW_OPCODE_GROUP_BF) => {
                let prefix = usize::from(words[3] & ID_MASK);
                if prefix > usize::from(words[2]) || prefix == 1 {
                    return Err(invalid("malformed BF group prefix"));
                }
                let mut weight = weight::BF_HEAD;
                for (index, member) in words[4..].as_chunks::<4>().0.iter().enumerate() {
                    weight += if index < prefix {
                        if !is_bf_product(member[0]) {
                            return Err(invalid("BF group prefix member is not a product"));
                        }
                        weight::BF_MEMBER_PRODUCT
                    } else {
                        if !is_bf_linear(member[0]) {
                            return Err(invalid("BF group tail member is not linear"));
                        }
                        weight::BF_MEMBER_TAIL
                    };
                }
                weight
            }
            (0, op) if is_bf_linear(op) => weight::BF_LINEAR,
            (0, op) if is_bf_product(op) => weight::BF_PRODUCT,
            (1, WINDOW_OPCODE_LINEAR_E4_WIDE) => weight::E4_LINEAR,
            (2, OPCODE_PRODUCT_BF_E4) => weight::E4_SINGLETON_MIXED,
            (2, WINDOW_OPCODE_PRODUCT_E4_E4) => weight::E4_SINGLETON_FULL,
            (3, WINDOW_OPCODE_GROUP_E4) => {
                let mut weight = weight::E4_HEAD;
                for member in words[4..].as_chunks::<4>().0 {
                    weight += match member[0] {
                        OPCODE_PRODUCT_BF_E4 => weight::E4_PAIR_MEMBER_MIXED,
                        WINDOW_OPCODE_PRODUCT_E4_E4 => weight::E4_PAIR_MEMBER_FULL,
                        _ => return Err(invalid("E4 pair member is not a product")),
                    };
                }
                weight
            }
            (section, op) => {
                return Err(invalid(format!(
                    "opcode {op} is not valid in section {section}"
                )))
            }
        };
    }
    Ok(work * SELECTOR_WARPS)
}

#[cfg(test)]
mod tests;
