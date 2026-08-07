//! Typed source model and constant, derived-E4, and special-source banks.

use super::isa::LdcSub;
use super::BABYBEAR_NEG_ONE;
use gkr_eval_ir::{
    ChallengeKey, ChallengePower, ChallengeRef, RangeWidth, ReadPlace, ResolutionStrategy,
    VirtualSetupKind,
};

#[derive(Clone, Debug, Default)]
pub struct ConstBank {
    values: Vec<u32>,
}
impl ConstBank {
    pub(crate) fn intern(&mut self, value: u32) -> u16 {
        // Special field elements use dedicated literals or are elided.
        assert!(
            value != 0 && value != 1 && value != BABYBEAR_NEG_ONE,
            "ConstBank must not intern a special field element (0/1/−1); got {value} \
             — missed canonicalization to a Special literal or elision"
        );
        if let Some(index) = self.values.iter().position(|existing| *existing == value) {
            return u16::try_from(index).expect("constant bank exceeds u16 indexing");
        }
        let i = u16::try_from(self.values.len()).expect("constant bank exceeds u16 indexing");
        self.values.push(value);
        i
    }
    pub fn values(&self) -> &[u32] {
        &self.values
    }
}

#[derive(Clone, Debug, Default)]
pub struct DerivedE4Banks {
    uses_lookup_additive: bool,
    arg_refs: Vec<ChallengeRef>,
}
impl DerivedE4Banks {
    pub(crate) fn intern(&mut self, r: &ChallengeRef) -> Option<(LdcSub, u16)> {
        match (&r.key, r.power) {
            (ChallengeKey::LookupAdditive, ChallengePower::One) => {
                self.uses_lookup_additive = true;
                Some((LdcSub::ConstDerivedE4, 0))
            }
            (ChallengeKey::PermutationAdditive | ChallengeKey::PermutationLinearization(_), _) => {
                if let Some(index) = self.arg_refs.iter().position(|existing| existing == r) {
                    return Some((
                        LdcSub::ArgDerivedE4,
                        u16::try_from(index).expect("derived-E4 bank exceeds u16 indexing"),
                    ));
                }
                let idx = u16::try_from(self.arg_refs.len())
                    .expect("derived-E4 bank exceeds u16 indexing");
                self.arg_refs.push(*r);
                Some((LdcSub::ArgDerivedE4, idx))
            }
            _ => None,
        }
    }

    pub fn uses_lookup_additive(&self) -> bool {
        self.uses_lookup_additive
    }

    pub fn arg_refs(&self) -> &[ChallengeRef] {
        &self.arg_refs
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SpecialStrategy {
    PeekSingleColumn {
        set_index: usize,
        width: RangeWidth,
    },
    PeekAggregate {
        set_index: usize,
    },
    PeekSetup,
    PeekDecoder {
        predicate: ReadPlace,
    },
    VirtualSetup {
        kind: VirtualSetupKind,
    },
    /// Runtime-selected global RAM-set prefix, constant across every row.
    InitsAndTeardownsTopBits {
        reference: gkr_eval_ir::InitsAndTeardownsTopBitsRef,
    },
}

/// Kind-to-device-code mapping. The array index is the device code.
pub const KIND_ORDER: [VirtualSetupKind; 4] = {
    use VirtualSetupKind::*;
    [
        RangeCheck16Bits,
        RangeCheckTimestamp,
        InitsAndTeardownsLow,
        InitsAndTeardownsHigh,
    ]
};

pub fn virtual_setup_kind_code(kind: &VirtualSetupKind) -> u32 {
    KIND_ORDER
        .iter()
        .position(|candidate| candidate == kind)
        .expect("virtual setup kind missing from KIND_ORDER") as u32
}

#[derive(Clone, Debug, Default)]
pub struct SpecialTable {
    descs: Vec<SpecialStrategy>,
}
impl SpecialTable {
    pub(crate) fn intern(&mut self, d: SpecialStrategy) -> u16 {
        if let Some(index) = self.descs.iter().position(|existing| existing == &d) {
            return u16::try_from(index).expect("special table exceeds u16 indexing");
        }
        let i = u16::try_from(self.descs.len()).expect("special table exceeds u16 indexing");
        self.descs.push(d);
        i
    }
    pub fn len(&self) -> usize {
        self.descs.len()
    }
    pub fn iter(&self) -> impl Iterator<Item = &SpecialStrategy> {
        self.descs.iter()
    }
}

pub(crate) fn lower_resolution(strategy: &ResolutionStrategy) -> SpecialStrategy {
    match strategy {
        ResolutionStrategy::PeekSingleColumn { set_index, width } => {
            SpecialStrategy::PeekSingleColumn {
                set_index: *set_index,
                width: *width,
            }
        }
        ResolutionStrategy::PeekAggregate { set_index } => SpecialStrategy::PeekAggregate {
            set_index: *set_index,
        },
        ResolutionStrategy::PeekSetup => SpecialStrategy::PeekSetup,
        ResolutionStrategy::PeekDecoder { predicate } => SpecialStrategy::PeekDecoder {
            predicate: *predicate,
        },
    }
}
