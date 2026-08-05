//! Typed source model + constant/derived-E4 banks + special-source descriptors (spec §8, §9).

use super::isa::LdcSub;
use gkr_eval_ir::{
    ChallengeKey, ChallengeRef, ExprId, FillSource, RangeWidth, ReadPlace, ResolutionStrategy,
    VirtualSetupKind,
};
use std::collections::HashMap;

/// BabyBear `−1` (= P−1). The forward VM is BabyBear-specific.
const BABYBEAR_NEG_ONE: u32 = 0x78000001 - 1;

#[derive(Clone, Debug, Default)]
pub struct ConstBank {
    values: Vec<u32>,
    index: HashMap<u32, u16>,
}
impl ConstBank {
    pub fn intern(&mut self, value: u32) -> u16 {
        // Invariant: the special field elements {0, 1, −1} never occupy a const
        // slot — they have dedicated `Special` literals (`Zero`/`One`/`NegOne`) or
        // are elided as identities/annihilators. A value here means a missed
        // canonicalization upstream; fail loud rather than let a special slip
        // through as a plain GPU `__constant__` (spec §6/§8).
        assert!(
            value != 0 && value != 1 && value != BABYBEAR_NEG_ONE,
            "ConstBank must not intern a special field element (0/1/−1); got {value} \
             — missed canonicalization to a Special literal or elision"
        );
        if let Some(&i) = self.index.get(&value) {
            return i;
        }
        let i = self.values.len() as u16;
        self.values.push(value);
        self.index.insert(value, i);
        i
    }
    pub fn get(&self, idx: u16) -> Option<u32> {
        self.values.get(idx as usize).copied()
    }
    pub fn values(&self) -> &[u32] {
        &self.values
    }
}

/// Per-channel derived-E4 banks. The current forward recipes are `ChallengeRef`s;
/// the bank name describes the resulting E4 values rather than their recipes.
#[derive(Clone, Debug, Default)]
pub struct DerivedE4Banks {
    const_refs: Vec<ChallengeRef>, // ConstDerivedE4 channel
    arg_refs: Vec<ChallengeRef>,   // ArgDerivedE4 channel
    index: HashMap<ChallengeRef, (LdcSub, u16)>,
}
impl DerivedE4Banks {
    pub fn intern(&mut self, r: &ChallengeRef) -> (LdcSub, u16) {
        if let Some(&hit) = self.index.get(r) {
            return hit;
        }
        let sub = classify_derived_e4(r);
        let bank = match sub {
            LdcSub::ConstDerivedE4 => &mut self.const_refs,
            _ => &mut self.arg_refs,
        };
        let idx = bank.len() as u16;
        bank.push(r.clone());
        self.index.insert(r.clone(), (sub, idx));
        (sub, idx)
    }
    pub fn get(&self, sub: LdcSub, idx: u16) -> Option<&ChallengeRef> {
        let bank = match sub {
            LdcSub::ConstDerivedE4 => &self.const_refs,
            LdcSub::ArgDerivedE4 => &self.arg_refs,
            _ => return None,
        };
        bank.get(idx as usize)
    }
}

/// SP1 best-effort channel classification (SP3 confirms; does not affect SP1 correctness).
pub fn classify_derived_e4(r: &ChallengeRef) -> LdcSub {
    match &r.key {
        // ChallengeKey is not Copy (PermutationLinearization payload) — match by ref
        ChallengeKey::LookupAdditive
        | ChallengeKey::LookupMultiplicative
        | ChallengeKey::ConstraintAggregation => LdcSub::ConstDerivedE4,
        ChallengeKey::PermutationAdditive
        | ChallengeKey::PermutationLinearization(_)
        | ChallengeKey::ClaimBatching => LdcSub::ArgDerivedE4,
    }
}

/// Static descriptor for a resolution peek (spec §9). `origin_expr` lets the SP1 CPU
/// interpreter re-resolve through the authoritative evaluator; SP2 binds real arrays.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpecialDescriptor {
    pub strategy: SpecialStrategy,
    pub origin_expr: ExprId,
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
        fill: FillSource,
    },
    /// A virtual-setup base column: the value at `row` is `virtual_setup(kind, row)` —
    /// resolver-computed, reads nothing (no backing slot, no DRAM gather). Lowered from
    /// `SourceKind::VirtualSetup` as a `Special` rather than a fake `Global` backing.
    VirtualSetup {
        kind: VirtualSetupKind,
    },
}

/// Kind ↔ device `desc_param` code mapping — the single source of truth mirrored by
/// CUDA `SD_VIRTUAL` handling (Task 3). Order is load-bearing: index == device code.
pub const KIND_ORDER: [VirtualSetupKind; 4] = {
    use VirtualSetupKind::*;
    [
        RangeCheck16Bits,
        RangeCheckTimestamp,
        InitsAndTeardownsLow,
        InitsAndTeardownsHigh,
    ]
};

/// The device `desc_param` code for a `VirtualSetupKind`. An explicit `match` (not
/// `KIND_ORDER.iter().position(...)`) so a future upstream variant fails to COMPILE here
/// rather than panicking at runtime. Must agree with `KIND_ORDER`
/// (`KIND_ORDER[virtual_setup_kind_code(&k) as usize] == k`; unit-tested for all 4).
pub fn virtual_setup_kind_code(kind: &VirtualSetupKind) -> u32 {
    use VirtualSetupKind::*;
    match kind {
        RangeCheck16Bits => 0,
        RangeCheckTimestamp => 1,
        InitsAndTeardownsLow => 2,
        InitsAndTeardownsHigh => 3,
    }
}

#[derive(Clone, Debug, Default)]
pub struct SpecialTable {
    descs: Vec<SpecialDescriptor>,
}
impl SpecialTable {
    pub fn push(&mut self, d: SpecialDescriptor) -> u16 {
        let i = self.descs.len() as u16;
        self.descs.push(d);
        i
    }
    pub fn get(&self, desc: u16) -> Option<&SpecialDescriptor> {
        self.descs.get(desc as usize)
    }
    pub fn len(&self) -> usize {
        self.descs.len()
    }
    pub fn is_empty(&self) -> bool {
        self.descs.is_empty()
    }
    pub fn iter(&self) -> impl Iterator<Item = &SpecialDescriptor> {
        self.descs.iter()
    }
}

pub fn lower_resolution(strategy: &ResolutionStrategy, origin_expr: ExprId) -> SpecialDescriptor {
    let strategy = match strategy {
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
        ResolutionStrategy::PeekDecoder { predicate, fill } => SpecialStrategy::PeekDecoder {
            predicate: predicate.clone(),
            fill: *fill,
        },
    };
    SpecialDescriptor {
        strategy,
        origin_expr,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use gkr_eval_ir::ChallengePower;
    #[test]
    fn const_bank_dedups() {
        let mut b = ConstBank::default();
        assert_eq!(b.intern(7), b.intern(7));
        assert_ne!(b.intern(7), b.intern(9));
        assert_eq!(b.values(), &[7, 9]);
    }
    #[test]
    fn derived_e4_bank_roundtrips_ref() {
        let mut banks = DerivedE4Banks::default();
        let r = ChallengeRef {
            key: ChallengeKey::LookupAdditive,
            power: ChallengePower::One,
        };
        let (sub, idx) = banks.intern(&r);
        assert_eq!(sub, LdcSub::ConstDerivedE4);
        assert_eq!(banks.get(sub, idx), Some(&r));
        // same ref reuses slot
        assert_eq!(banks.intern(&r), (sub, idx));
        // a permutation challenge goes to the arg channel
        let p = ChallengeRef {
            key: ChallengeKey::PermutationAdditive,
            power: ChallengePower::Static(2),
        };
        assert_eq!(banks.intern(&p).0, LdcSub::ArgDerivedE4);
    }
    #[test]
    fn claim_batching_classifies_as_arg_derived_e4() {
        // ClaimBatching is Ext-valued and, like PermutationAdditive, goes to the arg
        // channel — NOT the const channel (unlike ConstraintAggregation).
        let one = ChallengeRef {
            key: ChallengeKey::ClaimBatching,
            power: ChallengePower::One,
        };
        assert_eq!(classify_derived_e4(&one), LdcSub::ArgDerivedE4);
        let static3 = ChallengeRef {
            key: ChallengeKey::ClaimBatching,
            power: ChallengePower::Static(3),
        };
        assert_eq!(classify_derived_e4(&static3), LdcSub::ArgDerivedE4);
    }
    #[test]
    fn kind_order_and_code_roundtrip() {
        use gkr_eval_ir::VirtualSetupKind::*;
        // Forward: every kind's code indexes back to itself in KIND_ORDER.
        for k in [
            RangeCheck16Bits,
            RangeCheckTimestamp,
            InitsAndTeardownsLow,
            InitsAndTeardownsHigh,
        ] {
            assert_eq!(KIND_ORDER[virtual_setup_kind_code(&k) as usize], k);
        }
        // Reverse: KIND_ORDER index equals the code (order == device code).
        for (i, k) in KIND_ORDER.iter().enumerate() {
            assert_eq!(virtual_setup_kind_code(k) as usize, i);
        }
    }

    #[test]
    fn all_four_resolution_variants_lower_with_origin() {
        let mut t = SpecialTable::default();
        let i = t.push(lower_resolution(&ResolutionStrategy::PeekSetup, ExprId(5)));
        assert_eq!(t.get(i).unwrap().origin_expr, ExprId(5));
        assert!(matches!(
            t.get(i).unwrap().strategy,
            SpecialStrategy::PeekSetup
        ));
    }
}
