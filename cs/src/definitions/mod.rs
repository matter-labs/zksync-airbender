// this is defitnion of table types for purposes of doing no-std only for verifier
use ::field::PrimeField;
use core::ops::Range;

extern crate alloc;

use alloc::vec::Vec;

mod columns;
mod constants;
mod constraints;
mod delegation;
mod lookup;
mod memory_tree;
mod ram_access;
mod setup_tree;
mod stage2;
mod table_type;
mod witness_tree;

pub use self::columns::*;
pub use self::constants::*;
pub use self::constraints::*;
pub use self::delegation::*;
pub use self::lookup::*;
pub use self::memory_tree::*;
pub use self::ram_access::*;
pub use self::setup_tree::*;
pub use self::stage2::*;
pub use self::table_type::*;
pub use self::witness_tree::*;

pub const NUM_TIMESTAMP_DATA_LIMBS: usize = 3;
pub type TimestampScalar = u64;

pub const INITIAL_TIMESTAMP_AT_CHUNK_START: TimestampScalar = 4;
pub const TIMESTAMP_STEP: TimestampScalar = 1 << NUM_EMPTY_BITS_FOR_RAM_TIMESTAMP;

#[inline]
pub const fn timestamp_from_absolute_cycle_index(
    cycle_counter: usize,
    chunk_capacity: usize,
) -> TimestampScalar {
    let trace_len = chunk_capacity + 1;
    debug_assert!(trace_len.is_power_of_two());

    let chunk_index = cycle_counter / chunk_capacity;
    let index_in_chunk = cycle_counter % chunk_capacity;

    timestamp_from_chunk_cycle_and_sequence(index_in_chunk, chunk_capacity, chunk_index)
}

#[inline]
pub const fn timestamp_from_chunk_cycle_and_sequence(
    cycle_in_chunk: usize,
    chunk_capacity: usize,
    circuit_sequence: usize,
) -> TimestampScalar {
    let trace_len = chunk_capacity + 1;
    debug_assert!(trace_len.is_power_of_two());
    debug_assert!(cycle_in_chunk < trace_len);

    let timestamp = INITIAL_TIMESTAMP_AT_CHUNK_START
        + TIMESTAMP_STEP * (cycle_in_chunk as TimestampScalar)
        + timestamp_high_contribution_from_circuit_sequence(circuit_sequence, trace_len);

    timestamp
}

#[inline]
pub const fn timestamp_high_contribution_from_circuit_sequence(
    circuit_sequence: usize,
    trace_len: usize,
) -> TimestampScalar {
    debug_assert!(trace_len.is_power_of_two());
    // low timestamp chunk comes from the setup's two columns
    let timestamp_high_from_circuit_sequence = (circuit_sequence as TimestampScalar)
        << (trace_len.trailing_zeros() + NUM_EMPTY_BITS_FOR_RAM_TIMESTAMP);

    timestamp_high_from_circuit_sequence
}

pub const fn timestamp_scalar_into_column_values(
    timestamp: TimestampScalar,
) -> [u32; NUM_TIMESTAMP_COLUMNS_FOR_RAM] {
    let low = timestamp & ((1 << TIMESTAMP_COLUMNS_NUM_BITS) - 1);
    let high = timestamp >> TIMESTAMP_COLUMNS_NUM_BITS;

    [low as u32, high as u32]
}

pub fn split_timestamp(timestamp: TimestampScalar) -> (u32, u32) {
    let [low, high] = timestamp_scalar_into_column_values(timestamp);

    (low, high)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
#[repr(C)]
pub struct TimestampData(pub [u16; NUM_TIMESTAMP_DATA_LIMBS]);

const _: () = const {
    assert!(core::mem::align_of::<TimestampData>() == 2);
    assert!(core::mem::size_of::<TimestampData>() == 6);

    ()
};

impl Default for TimestampData {
    #[inline(always)]
    fn default() -> Self {
        Self([0; NUM_TIMESTAMP_DATA_LIMBS])
    }
}

impl TimestampData {
    pub const EMPTY: Self = Self([0u16; NUM_TIMESTAMP_DATA_LIMBS]);

    #[inline(always)]
    pub const fn from_scalar(ts: TimestampScalar) -> Self {
        let l0 = ts as u16;
        let l1 = (ts >> 16) as u16;
        let l2 = (ts >> 32) as u16;

        Self([l0, l1, l2])
    }

    pub const fn as_scalar(&self) -> TimestampScalar {
        (self.0[0] as u64) | ((self.0[1] as u64) << 16) | ((self.0[2] as u64) << 32)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct Variable(pub u64);

impl Ord for Variable {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.0.cmp(&other.0)
    }
}

impl PartialOrd for Variable {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Variable {
    pub const fn placeholder_variable() -> Self {
        Self(u64::MAX)
    }

    pub const fn is_placeholder(&self) -> bool {
        self.0 == u64::MAX
    }
}

#[derive(Clone, Copy, Debug)]
pub struct VerifierCompiledCircuitArtifact<'a, F: PrimeField> {
    pub witness_layout: CompiledWitnessSubtree<'a, F>,
    pub memory_layout: CompiledMemorySubtree<'a>,
    pub setup_layout: SetupLayout,
    pub stage_2_layout: LookupAndMemoryArgumentLayout,
    pub degree_2_constraints: &'a [VerifierCompiledDegree2Constraint<'a, F>],
    pub degree_1_constraints: &'a [VerifierCompiledDegree1Constraint<'a, F>],
    pub state_linkage_constraints: &'a [(ColumnAddress, ColumnAddress)],
    pub public_inputs: &'a [(BoundaryConstraintLocation, ColumnAddress)],
    pub lazy_init_address_aux_vars: Option<ShuffleRamAuxComparisonSet>,
    // pub memory_queries_timestamp_comparison_aux_vars: &'a [ColumnAddress],
    // pub batched_memory_access_timestamp_comparison_aux_vars: CompiledBatchedRamTimestampComparisonAuxVars<'a>,
    pub trace_len_log2: usize,
}

impl<'a, F: PrimeField> VerifierCompiledCircuitArtifact<'a, F> {
    pub const fn num_openings_at_z(&self) -> usize {
        let mut num_deep_poly_terms_at_z = 0;
        // all setup at z
        num_deep_poly_terms_at_z += self.setup_layout.total_width;
        // all witness at z
        num_deep_poly_terms_at_z += self.witness_layout.total_width;
        // all memory at z
        num_deep_poly_terms_at_z += self.memory_layout.total_width;
        // all stage 2 at z, but we should count properly
        let stage_2_num_base = self.stage_2_layout.num_base_field_polys();
        num_deep_poly_terms_at_z += stage_2_num_base;
        let stage_2_num_ext = self.stage_2_layout.num_ext4_field_polys();
        num_deep_poly_terms_at_z += stage_2_num_ext;
        // and quotient
        num_deep_poly_terms_at_z += 1;

        num_deep_poly_terms_at_z
    }

    pub const fn num_state_linkage_constraints(&self) -> usize {
        self.state_linkage_constraints.len()
    }

    pub const fn num_openings_at_z_omega(&self) -> usize {
        // now we count how many we open at z * omega
        let mut num_deep_poly_terms_at_z_omega = 0;
        // we open state-linking boundary constraints
        num_deep_poly_terms_at_z_omega += self.state_linkage_constraints.len();

        if self.memory_layout.shuffle_ram_inits_and_teardowns.is_some() {
            // then we open lazy init columns in memory
            num_deep_poly_terms_at_z_omega += REGISTER_SIZE; // width of lazy inits
        }

        // and accumulator for grand product in stage 2
        num_deep_poly_terms_at_z_omega += 1;

        num_deep_poly_terms_at_z_omega
    }

    pub const fn num_quotient_terms_every_row_except_last(&self) -> usize {
        // these are every row except last
        let mut num_quotient_terms = 0;
        num_quotient_terms += self.degree_2_constraints.len();
        num_quotient_terms += self.degree_1_constraints.len();

        // we need to check some special manual constraints if we process delegation requests
        // and require zeroe-valued timestamps and read values
        if self.memory_layout.delegation_processor_layout.is_some() {
            assert!(self.memory_layout.shuffle_ram_access_sets.len() == 0);
            assert!(
                self.memory_layout.batched_ram_accesses.len() > 0
                    || self.memory_layout.register_and_indirect_accesses.len() > 0
            );

            let num_mem_accesses = self.memory_layout.batched_ram_accesses.len();
            let mut num_writes = 0;
            let mut i = 0;
            let bound = self.memory_layout.batched_ram_accesses.len();
            while i < bound {
                if let BatchedRamAccessColumns::WriteAccess { .. } =
                    self.memory_layout.batched_ram_accesses[i]
                {
                    num_writes += 1;
                }
                i += 1;
            }

            // we do not care about values in the set if we do NOT process,
            // so we do:
            // - multiplicity is 0/1
            num_quotient_terms += 1;
            // - mem abi offset == 0
            num_quotient_terms += 1;
            // - write timestamp == 0
            num_quotient_terms += NUM_TIMESTAMP_COLUMNS_FOR_RAM;

            // Also batch ram specific constraints
            // for every value we check that read timestamp == 0
            num_quotient_terms += NUM_TIMESTAMP_COLUMNS_FOR_RAM * num_mem_accesses;
            // for every read value we check that value == 0
            num_quotient_terms += REGISTER_SIZE * num_mem_accesses;
            // for every written value value we check that value == 0
            num_quotient_terms += REGISTER_SIZE * num_writes;

            // this way our contributions to read/write sets are reads/writes to 0 address at timestamp 0

            // same for register and indirect accesses
            let num_register_accesses = self.memory_layout.register_and_indirect_accesses.len();
            let mut num_indirect_accesses = 0;
            let mut num_booleans_for_indirect_address_derivation = 0;
            let mut num_reg_or_indirect_writes = 0;
            let mut i = 0;
            let bound = self.memory_layout.register_and_indirect_accesses.len();
            while i < bound {
                let access = &self.memory_layout.register_and_indirect_accesses[i];
                if let RegisterAccessColumns::WriteAccess { .. } = access.register_access {
                    num_reg_or_indirect_writes += 1;
                }
                // then indirects
                let indirects_bound = access.indirect_accesses.len();
                num_indirect_accesses += indirects_bound;
                let mut j = 0;
                while j < indirects_bound {
                    if let IndirectAccessColumns::WriteAccess { .. } = access.indirect_accesses[j] {
                        num_reg_or_indirect_writes += 1;
                    }
                    if j > 0 {
                        if access.indirect_accesses[j]
                            .get_address_derivation_carry_bit_column()
                            .num_elements()
                            > 0
                        {
                            num_booleans_for_indirect_address_derivation += 1;
                        }
                    }
                    j += 1;
                }

                i += 1;
            }

            // for every value we check that read timestamp == 0
            num_quotient_terms +=
                NUM_TIMESTAMP_COLUMNS_FOR_RAM * (num_register_accesses + num_indirect_accesses);
            // for every read value we check that value == 0
            num_quotient_terms += REGISTER_SIZE * (num_register_accesses + num_indirect_accesses);
            // for every written value value we check that value == 0
            num_quotient_terms += REGISTER_SIZE * num_reg_or_indirect_writes;
            // for every indirect access we need to put boolean constraint on carry bit in address derivation
            num_quotient_terms += num_booleans_for_indirect_address_derivation;
        }

        // 2 constraints per each optimized width-1 lookup for range check 16 bits
        num_quotient_terms += 2 * self
            .stage_2_layout
            .intermediate_polys_for_range_check_16
            .num_pairs;

        // same for timestamps
        num_quotient_terms += 2 * self
            .stage_2_layout
            .intermediate_polys_for_timestamp_range_checks
            .num_pairs;

        if let Some(shuffle_ram_inits_and_teardowns) =
            self.memory_layout.shuffle_ram_inits_and_teardowns
        {
            // and special case of range check 16 for lazy init columns
            assert!(
                shuffle_ram_inits_and_teardowns
                    .lazy_init_addresses_columns
                    .num_elements()
                    == 1
            );
            num_quotient_terms += 2;

            // 3 * 2 constraints for the case of padding values checks
            num_quotient_terms += 3 * 2;
        }

        // 1 constraint for remainders
        num_quotient_terms += self.stage_2_layout.remainder_for_range_check_16.is_some() as usize;

        if let Some(_remainder_for_range_check_16) =
            self.stage_2_layout.remainder_for_range_check_16.as_ref()
        {
            todo!()
        }

        // 1 constraint per every generic lookup column
        num_quotient_terms += self
            .stage_2_layout
            .intermediate_polys_for_generic_lookup
            .num_elements();

        // 1 constraint per every multiplicity
        num_quotient_terms += self
            .stage_2_layout
            .intermediate_poly_for_range_check_16_multiplicity
            .num_elements();
        num_quotient_terms += self
            .stage_2_layout
            .intermediate_poly_for_timestamp_range_check_multiplicity
            .num_elements();
        num_quotient_terms += self
            .stage_2_layout
            .intermediate_polys_for_generic_multiplicities
            .num_elements();

        // and if we execute delegation argument - then we need to extra helper poly
        if self.memory_layout.delegation_processor_layout.is_some() {
            assert!(self.memory_layout.delegation_request_layout.is_none());

            // 1 constraint for helper sum poly
            num_quotient_terms += 1;
        }

        if self.memory_layout.delegation_request_layout.is_some() {
            assert!(self.memory_layout.delegation_processor_layout.is_none());

            // 1 constraint for helper sum poly
            num_quotient_terms += 1;
        }

        // 1 constraint per every memory column. This includes final column to accumulate grand product
        num_quotient_terms += self
            .stage_2_layout
            .intermediate_polys_for_memory_argument
            .num_elements();

        num_quotient_terms
    }

    pub const fn num_quotient_terms_every_row_except_last_two(&self) -> usize {
        let mut num_quotient_terms = 0;
        // constraints that link state variables, every rows except last two
        num_quotient_terms += self.state_linkage_constraints.len();

        if let Some(_) = self.memory_layout.shuffle_ram_inits_and_teardowns {
            // two constraints from comparison of lazy init addresses (we stop at one before last and output it)
            num_quotient_terms += 2;
        }

        num_quotient_terms
    }

    pub const fn num_quotient_terms_first_row(&self) -> usize {
        let mut num_quotient_terms = 0;
        // first row

        // 1 constraint for memory accumulator initial value == 1
        num_quotient_terms += 1;

        // we need to output lazy init addresses + teardown values/timestamps
        if let Some(_) = self.memory_layout.shuffle_ram_inits_and_teardowns {
            // 2 limbs per each address, final value and final timestamp
            num_quotient_terms += 2 * 3;
        }

        // and public inputs
        let mut i = 0;
        let bound = self.public_inputs.len();
        while i < bound {
            let (location, _column_address) = self.public_inputs[i];
            match location {
                BoundaryConstraintLocation::FirstRow => num_quotient_terms += 1,
                BoundaryConstraintLocation::OneBeforeLastRow => {}
                BoundaryConstraintLocation::LastRow => {
                    panic!("public inputs on the last row are not supported");
                }
            }
            i += 1;
        }

        num_quotient_terms
    }

    pub const fn num_quotient_terms_one_before_last_row(&self) -> usize {
        let mut num_quotient_terms = 0;
        // one before last row

        // we need to output lazy init addresses + teardown values/timestamps
        if let Some(_) = self.memory_layout.shuffle_ram_inits_and_teardowns {
            // 2 limbs per each address, final value and final timestamp
            num_quotient_terms += 2 * 3;
        }

        // and public inputs
        let mut i = 0;
        let bound = self.public_inputs.len();
        while i < bound {
            let (location, _column_address) = self.public_inputs[i];
            match location {
                BoundaryConstraintLocation::FirstRow => {}
                BoundaryConstraintLocation::OneBeforeLastRow => num_quotient_terms += 1,
                BoundaryConstraintLocation::LastRow => {
                    panic!("public inputs on the last row are not supported");
                }
            }
            i += 1;
        }

        num_quotient_terms
    }

    pub const fn num_quotient_terms_last_row(&self) -> usize {
        let mut num_quotient_terms = 0;
        // last row

        // 1 constraint for memory accumulator final value
        num_quotient_terms += 1;

        num_quotient_terms
    }

    pub const fn num_quotient_terms_last_row_and_at_zero(&self) -> usize {
        let mut num_quotient_terms = 0;
        // last row and at 0

        // 1 constraint per every difference for lookup type like (\sum multiplicity_aux - \sum intermediate_aux)

        // range check 16
        num_quotient_terms += (self
            .stage_2_layout
            .intermediate_poly_for_range_check_16_multiplicity
            .num_elements()
            > 0) as usize;

        // timestamp range check
        num_quotient_terms += (self
            .stage_2_layout
            .intermediate_poly_for_timestamp_range_check_multiplicity
            .num_elements()
            > 0) as usize;

        // generic lookup
        num_quotient_terms += (self
            .stage_2_layout
            .intermediate_polys_for_generic_multiplicities
            .num_elements()
            > 0) as usize;

        if self.memory_layout.delegation_processor_layout.is_some() {
            assert!(self.memory_layout.delegation_request_layout.is_none());

            // 1 constraint for set equality values
            num_quotient_terms += 1;
        }

        if self.memory_layout.delegation_request_layout.is_some() {
            assert!(self.memory_layout.delegation_processor_layout.is_none());

            // 1 constraint for set equality values
            num_quotient_terms += 1;
        }

        num_quotient_terms
    }

    pub const fn num_quotient_terms(&self) -> usize {
        let mut num_quotient_terms = 0;

        num_quotient_terms += self.num_quotient_terms_every_row_except_last();
        num_quotient_terms += self.num_quotient_terms_every_row_except_last_two();
        num_quotient_terms += self.num_quotient_terms_first_row();
        num_quotient_terms += self.num_quotient_terms_one_before_last_row();
        num_quotient_terms += self.num_quotient_terms_last_row();
        num_quotient_terms += self.num_quotient_terms_last_row_and_at_zero();

        num_quotient_terms
    }
}
