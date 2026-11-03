//! Checked base-commitment dimensions, independent of field and storage policy.

use super::{pow_bits, BaseColumns, CommitmentMode, ProverConfig};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BaseOracleRole {
    Memory,
    Witness,
    Setup,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct OraclePacking {
    role: BaseOracleRole,
    logical_columns: usize,
    physical_columns: usize,
    padded_columns: usize,
}

impl OraclePacking {
    pub fn role(&self) -> BaseOracleRole {
        self.role
    }
    pub fn logical_columns(&self) -> usize {
        self.logical_columns
    }
    pub fn physical_columns(&self) -> usize {
        self.physical_columns
    }
    pub fn padded_columns(&self) -> usize {
        self.padded_columns
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BaseCommitmentGeometry {
    trace_len_log2: usize,
    pack_log2: usize,
    message_size_log2: usize,
    commitment_mode: CommitmentMode,
    lde_factor: usize,
    values_per_leaf: usize,
    cap_size: usize,
    logical_columns: BaseColumns,
    oracles: [OraclePacking; 3],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CommitmentGeometryError {
    Overflow { quantity: &'static str },
}

impl std::fmt::Display for CommitmentGeometryError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Overflow { quantity } => write!(f, "base commitment {quantity} overflows usize"),
        }
    }
}

impl std::error::Error for CommitmentGeometryError {}

fn pow2(log: usize, quantity: &'static str) -> Result<usize, CommitmentGeometryError> {
    u32::try_from(log)
        .ok()
        .and_then(|log| 1usize.checked_shl(log))
        .ok_or(CommitmentGeometryError::Overflow { quantity })
}

fn product(a: usize, b: usize, quantity: &'static str) -> Result<usize, CommitmentGeometryError> {
    a.checked_mul(b)
        .ok_or(CommitmentGeometryError::Overflow { quantity })
}

impl BaseCommitmentGeometry {
    /// Checks that every size, LDE factor and oracle LDE domain fits `usize`,
    /// panics on any schedule or tree rule that
    /// [`ProverConfig::validate_for_whir_message_size`] rejects, then projects the
    /// existing column-count authority into memory/witness/setup storage sizes.
    /// Base fold zero is valid; field and backend limits are checked separately.
    pub fn from_config(
        config: &ProverConfig,
        columns: BaseColumns,
    ) -> Result<Self, CommitmentGeometryError> {
        let pack_log2 = config.pack_log2();
        let message_size_log2 = config.trace_len_log2.checked_add(pack_log2).ok_or(
            CommitmentGeometryError::Overflow {
                quantity: "message log2",
            },
        )?;
        let rows = pow2(config.trace_len_log2, "trace size")?;
        let pack = pow2(pack_log2, "packing factor")?;
        let message_size = pow2(message_size_log2, "message size")?;
        let schedule = &config.whir_schedule;
        let base = config.base_round();
        let lde_factor = pow2(base.lde_factor_log2, "LDE factor")?;
        let values_per_leaf = pow2(base.fold_log2, "values per leaf")?;
        for round in &schedule.internal_rounds {
            pow2(round.lde_factor_log2, "intermediate LDE factor")?;
        }
        config.validate_for_whir_message_size(message_size_log2);
        let mut poly_size_log2 = message_size_log2;
        pow2(poly_size_log2 + base.lde_factor_log2, "LDE domain")?;
        for (round, fold_log2) in schedule.internal_rounds.iter().zip(schedule.fold_steps()) {
            poly_size_log2 -= fold_log2;
            pow2(poly_size_log2 + round.lde_factor_log2, "LDE domain")?;
        }
        let widths = if config.merged_memory_and_witness() {
            [
                columns.memory.checked_add(columns.witness).ok_or(
                    CommitmentGeometryError::Overflow {
                        quantity: "merged columns",
                    },
                )?,
                0,
                columns.setup,
            ]
        } else {
            [columns.memory, columns.witness, columns.setup]
        };
        let roles = [
            BaseOracleRole::Memory,
            BaseOracleRole::Witness,
            BaseOracleRole::Setup,
        ];
        let mut oracles = [OraclePacking {
            role: BaseOracleRole::Memory,
            logical_columns: 0,
            physical_columns: 0,
            padded_columns: 0,
        }; 3];
        let mut total_physical_columns = 0usize;
        for i in 0..3 {
            let physical_columns = pow_bits::physically_committed_polys(widths[i], 0, 0, pack_log2);
            let padded_columns = product(physical_columns, pack, "padded columns")?;
            product(widths[i], rows, "logical elements")?;
            product(padded_columns, rows, "padded elements")?;
            let elements = product(physical_columns, message_size, "committed elements")?;
            product(elements, lde_factor, "LDE elements")?;
            total_physical_columns = total_physical_columns.checked_add(physical_columns).ok_or(
                CommitmentGeometryError::Overflow {
                    quantity: "physical columns",
                },
            )?;
            oracles[i] = OraclePacking {
                role: roles[i],
                logical_columns: widths[i],
                physical_columns,
                padded_columns,
            };
        }
        let total_elements = product(
            columns.committed_polys(pack_log2, config.merged_memory_and_witness()),
            message_size,
            "total committed elements",
        )?;
        product(total_elements, lde_factor, "total LDE elements")?;
        Ok(Self {
            trace_len_log2: config.trace_len_log2,
            pack_log2,
            message_size_log2,
            commitment_mode: config.commitment_mode,
            lde_factor,
            values_per_leaf,
            cap_size: config.cap_size,
            logical_columns: columns,
            oracles,
        })
    }

    pub fn trace_len_log2(&self) -> usize {
        self.trace_len_log2
    }
    pub fn pack_log2(&self) -> usize {
        self.pack_log2
    }
    pub fn message_size_log2(&self) -> usize {
        self.message_size_log2
    }
    pub fn commitment_mode(&self) -> CommitmentMode {
        self.commitment_mode
    }
    pub fn lde_factor(&self) -> usize {
        self.lde_factor
    }
    pub fn values_per_leaf(&self) -> usize {
        self.values_per_leaf
    }
    pub fn is_virtual_packing(&self) -> bool {
        self.values_per_leaf == 1
    }
    pub fn cap_size(&self) -> usize {
        self.cap_size
    }
    pub fn logical_columns(&self) -> BaseColumns {
        self.logical_columns
    }
    pub fn oracles(&self) -> &[OraclePacking; 3] {
        &self.oracles
    }
    pub fn oracle(&self, role: BaseOracleRole) -> &OraclePacking {
        &self.oracles[match role {
            BaseOracleRole::Memory => 0,
            BaseOracleRole::Witness => 1,
            BaseOracleRole::Setup => 2,
        }]
    }
    pub fn total_physical_columns(&self) -> usize {
        self.oracles
            .iter()
            .map(OraclePacking::physical_columns)
            .sum()
    }
}

#[cfg(test)]
mod tests;
