//! Base-commitment dimensions, independent of field and storage policy.

use super::{pow_bits, BaseColumns, CommitmentMode, ProverConfig};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BaseOracleRole {
    Memory,
    Witness,
    Setup,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct OraclePacking {
    logical_columns: usize,
    physical_columns: usize,
}

impl OraclePacking {
    pub fn logical_columns(&self) -> usize {
        self.logical_columns
    }
    pub fn physical_columns(&self) -> usize {
        self.physical_columns
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

impl BaseCommitmentGeometry {
    pub fn from_config(config: &ProverConfig, columns: BaseColumns) -> Self {
        let pack_log2 = config.pack_log2();
        let message_size_log2 = config.trace_len_log2 + pack_log2;
        config.validate_for_whir_message_size(message_size_log2);
        let base = config.base_round();
        let widths = if config.merged_memory_and_witness() {
            [columns.memory + columns.witness, 0, columns.setup]
        } else {
            [columns.memory, columns.witness, columns.setup]
        };
        let oracles = widths.map(|logical_columns| OraclePacking {
            logical_columns,
            physical_columns: pow_bits::physically_committed_polys(
                logical_columns,
                0,
                0,
                pack_log2,
            ),
        });
        Self {
            trace_len_log2: config.trace_len_log2,
            pack_log2,
            message_size_log2,
            commitment_mode: config.commitment_mode,
            lde_factor: 1 << base.lde_factor_log2,
            values_per_leaf: 1 << base.fold_log2,
            cap_size: config.cap_size,
            logical_columns: columns,
            oracles,
        }
    }

    /// Address of a logical base claim in the selected commitment layout.
    pub fn logical_claim_address(
        &self,
        address: cs::definitions::GKRAddress,
    ) -> cs::definitions::GKRAddress {
        use cs::definitions::GKRAddress;
        match address {
            GKRAddress::BaseLayerWitness(offset)
                if self.commitment_mode == CommitmentMode::MergedMemoryAndWitness =>
            {
                GKRAddress::BaseLayerMemory(
                    self.logical_columns
                        .memory
                        .checked_add(offset)
                        .expect("merged claim offset overflow"),
                )
            }
            address => address,
        }
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
