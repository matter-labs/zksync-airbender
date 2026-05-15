use crate::upstream::GKRAddress;

// Drift guards: every value below is hard-coded native-side. If upstream changes
// the Rust value, the corresponding assertion fails at compile time and the
// native definition must be updated in lockstep.

// Scalar mirrors in `gpu_prover/native/witness/{common,trace}.cuh`.
const _: () = assert!(crate::upstream::NON_DETERMINISM_CSR == 0x7c0);
const _: () = assert!(crate::upstream::REGISTER_SIZE == 2);
const _: () = assert!(crate::upstream::NUM_TIMESTAMP_COLUMNS_FOR_RAM == 2);
const _: () = assert!(crate::upstream::NUM_TIMESTAMP_DATA_LIMBS == 3);
const _: () = assert!(crate::upstream::TIMESTAMP_COLUMNS_NUM_BITS == 19);
const _: () = assert!(crate::upstream::NUM_EMPTY_BITS_FOR_RAM_TIMESTAMP == 2);

// Delegation-circuit ABI mirrors. Each `AbiDescription` in
// `gpu_prover/native/witness/trace_delegation.cuh` hard-codes the six fields of
// `DelegationAbi`; the upstream values (in `common_constants::delegation_types::*`)
// must match. `csr_offset` is taken relative to `NON_DETERMINISM_CSR` to keep the
// per-circuit literal small.
struct DelegationAbi {
    csr_offset: u32,
    reg_accesses: usize,
    indirect_reads: usize,
    indirect_writes: usize,
    variable_offsets: usize,
    base_register: u32,
}

impl DelegationAbi {
    const fn assert_matches(&self, expected: DelegationAbi) {
        assert!(self.csr_offset == expected.csr_offset);
        assert!(self.reg_accesses == expected.reg_accesses);
        assert!(self.indirect_reads == expected.indirect_reads);
        assert!(self.indirect_writes == expected.indirect_writes);
        assert!(self.variable_offsets == expected.variable_offsets);
        assert!(self.base_register == expected.base_register);
    }
}

// BigintWithControl
const _: () = DelegationAbi {
    csr_offset: crate::upstream::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER
        - crate::upstream::NON_DETERMINISM_CSR,
    reg_accesses: crate::upstream::NUM_BIGINT_REGISTER_ACCESSES,
    indirect_reads: crate::upstream::BIGINT_X11_NUM_READS,
    indirect_writes: crate::upstream::BIGINT_X10_NUM_WRITES,
    variable_offsets: crate::upstream::NUM_BIGINT_VARIABLE_OFFSETS,
    base_register: crate::upstream::BIGINT_BASE_ABI_REGISTER,
}
.assert_matches(DelegationAbi {
    csr_offset: 10,
    reg_accesses: 3,
    indirect_reads: 8,
    indirect_writes: 8,
    variable_offsets: 0,
    base_register: 10,
});

// Blake2sRoundFunction (blake2 with extended control)
const _: () = DelegationAbi {
    csr_offset: crate::upstream::BLAKE2S_DELEGATION_CSR_REGISTER
        - crate::upstream::NON_DETERMINISM_CSR,
    reg_accesses: crate::upstream::NUM_BLAKE2S_REGISTER_ACCESSES,
    indirect_reads: crate::upstream::BLAKE2S_X11_NUM_READS,
    indirect_writes: crate::upstream::BLAKE2S_X10_NUM_WRITES,
    variable_offsets: crate::upstream::NUM_BLAKE2S_VARIABLE_OFFSETS,
    base_register: crate::upstream::BLAKE2S_BASE_ABI_REGISTER,
}
.assert_matches(DelegationAbi {
    csr_offset: 7,
    reg_accesses: 3,
    indirect_reads: 16,
    indirect_writes: 24,
    variable_offsets: 0,
    base_register: 10,
});

// KeccakSpecial5
const _: () = DelegationAbi {
    csr_offset: crate::upstream::KECCAK_SPECIAL5_CSR_REGISTER
        - crate::upstream::NON_DETERMINISM_CSR,
    reg_accesses: crate::upstream::NUM_KECCAK_SPECIAL5_REGISTER_ACCESSES,
    indirect_reads: crate::upstream::NUM_KECCAK_SPECIAL5_INDIRECT_READS,
    indirect_writes: crate::upstream::KECCAK_SPECIAL5_X11_NUM_WRITES,
    variable_offsets: crate::upstream::KECCAK_SPECIAL5_NUM_VARIABLE_OFFSETS,
    base_register: crate::upstream::KECCAK_SPECIAL5_BASE_ABI_REGISTER,
}
.assert_matches(DelegationAbi {
    csr_offset: 11,
    reg_accesses: 2,
    indirect_reads: 0,
    indirect_writes: 12,
    variable_offsets: 6,
    base_register: 10,
});

// Blake2sGFunction
const _: () = DelegationAbi {
    csr_offset: crate::upstream::BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER
        - crate::upstream::NON_DETERMINISM_CSR,
    reg_accesses: crate::upstream::NUM_BLAKE2S_G_FUNCTION_REGISTER_ACCESSES,
    indirect_reads: crate::upstream::BLAKE2S_G_FUNCTION_X11_NUM_READS,
    indirect_writes: crate::upstream::BLAKE2S_G_FUNCTION_X10_NUM_WRITES,
    variable_offsets: crate::upstream::NUM_BLAKE2S_G_FUNCTION_VARIABLE_OFFSETS,
    base_register: crate::upstream::BLAKE2S_G_FUNCTION_BASE_ABI_REGISTER,
}
.assert_matches(DelegationAbi {
    csr_offset: 8,
    reg_accesses: 3,
    indirect_reads: 2,
    indirect_writes: 4,
    variable_offsets: 6,
    base_register: 10,
});

// pub mod arg_utils;
pub(crate) mod layout;
pub(crate) mod memory_delegation;
pub(crate) mod memory_unrolled;
pub(crate) mod multiplicities;
mod option;
mod ram_access;
pub(crate) mod trace;
pub(crate) mod trace_delegation;
pub(crate) mod trace_unrolled;
pub(crate) mod witness_delegation;
pub(crate) mod witness_unrolled;

#[repr(C, u32)]
#[derive(Clone, Copy, Debug)]
#[allow(dead_code)]
pub(crate) enum Address {
    BaseLayerWitness(u32),
    BaseLayerMemory(u32),
    InnerLayer { offset: u32, layer: u32 },
    Setup(u32),
    ScratchSpace(u32),
    Cached { offset: u32, layer: u32 },
}

impl Default for Address {
    fn default() -> Self {
        Self::BaseLayerWitness(0)
    }
}

impl From<GKRAddress> for Address {
    fn from(value: GKRAddress) -> Self {
        match value {
            GKRAddress::BaseLayerWitness(x) => Self::BaseLayerWitness(x as u32),
            GKRAddress::BaseLayerMemory(x) => Self::BaseLayerMemory(x as u32),
            GKRAddress::InnerLayer { layer, offset } => Self::InnerLayer {
                offset: offset as u32,
                layer: layer as u32,
            },
            GKRAddress::Setup(x) => Self::Setup(x as u32),
            GKRAddress::VirtualSetup(_) => {
                unreachable!(
                    "GPU witness serialization does not materialize virtual setup addresses"
                )
            }
            GKRAddress::ScratchSpace(x) => Self::ScratchSpace(x as u32),
            GKRAddress::Cached { layer, offset } => Self::Cached {
                offset: offset as u32,
                layer: layer as u32,
            },
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct NoFieldLinearTerm {
    coefficient: u32,
    address: Address,
}

pub(crate) const MAX_LINEAR_TERMS_COUNT: usize = 4;

#[repr(C)]
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct NoFieldLinearRelation {
    linear_terms_count: u32,
    linear_terms: [NoFieldLinearTerm; MAX_LINEAR_TERMS_COUNT],
    constant: u32,
}

impl From<&cs::definitions::gkr::NoFieldLinearRelation> for NoFieldLinearRelation {
    fn from(value: &cs::definitions::gkr::NoFieldLinearRelation) -> Self {
        let terms = &value.linear_terms;
        let len = terms.len();
        assert!(len <= MAX_LINEAR_TERMS_COUNT);
        let mut linear_terms = [NoFieldLinearTerm::default(); MAX_LINEAR_TERMS_COUNT];
        for (&src, dst) in terms.iter().zip(linear_terms.iter_mut()) {
            *dst = NoFieldLinearTerm {
                coefficient: src.0,
                address: src.1.into(),
            };
        }
        Self {
            linear_terms_count: len as u32,
            linear_terms,
            constant: value.constant,
        }
    }
}
