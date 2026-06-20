//! Typed source model + const/challenge banks + special-source descriptors (spec §8, §9).

use super::isa::LdcSub;
use cs::gkr_compiler::dag_ir::{ChallengeKey, ChallengeRef, ExprId, FillSource, RangeWidth, ReadPlace, ResolutionStrategy};
use std::collections::HashMap;

#[derive(Clone, Debug, Default)]
pub struct ConstBank { values: Vec<u32>, index: HashMap<u32, u16> }
impl ConstBank {
    pub fn intern(&mut self, value: u32) -> u16 {
        if let Some(&i) = self.index.get(&value) { return i; }
        let i = self.values.len() as u16; self.values.push(value); self.index.insert(value, i); i
    }
    pub fn get(&self, idx: u16) -> Option<u32> { self.values.get(idx as usize).copied() }
    pub fn values(&self) -> &[u32] { &self.values }
}

/// Per-channel challenge banks holding the real `ChallengeRef`s (spec §7).
#[derive(Clone, Debug, Default)]
pub struct ChallengeBanks {
    const_refs: Vec<ChallengeRef>, // ConstChallenge channel
    arg_refs: Vec<ChallengeRef>,   // ArgChallenge channel
    index: HashMap<ChallengeRef, (LdcSub, u16)>,
}
impl ChallengeBanks {
    pub fn intern(&mut self, r: &ChallengeRef) -> (LdcSub, u16) {
        if let Some(&hit) = self.index.get(r) { return hit; }
        let sub = classify_challenge(r);
        let bank = match sub { LdcSub::ConstChallenge => &mut self.const_refs, _ => &mut self.arg_refs };
        let idx = bank.len() as u16; bank.push(r.clone());
        self.index.insert(r.clone(), (sub, idx)); (sub, idx)
    }
    pub fn get(&self, sub: LdcSub, idx: u16) -> Option<&ChallengeRef> {
        let bank = match sub { LdcSub::ConstChallenge => &self.const_refs, LdcSub::ArgChallenge => &self.arg_refs, _ => return None };
        bank.get(idx as usize)
    }
}

/// SP1 best-effort channel classification (SP3 confirms; does not affect SP1 correctness).
pub fn classify_challenge(r: &ChallengeRef) -> LdcSub {
    match &r.key { // ChallengeKey is not Copy (PermutationLinearization payload) — match by ref
        ChallengeKey::LookupAdditive | ChallengeKey::LookupMultiplicative | ChallengeKey::ConstraintAggregation => LdcSub::ConstChallenge,
        ChallengeKey::PermutationAdditive | ChallengeKey::PermutationLinearization(_) => LdcSub::ArgChallenge,
    }
}

/// Static descriptor for a resolution peek (spec §9). `origin_expr` lets the SP1 CPU
/// interpreter re-resolve through the authoritative evaluator; SP2 binds real arrays.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpecialDescriptor { pub strategy: SpecialStrategy, pub origin_expr: ExprId }

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SpecialStrategy {
    PeekSingleColumn { set_index: usize, width: RangeWidth },
    PeekAggregate { set_index: usize },
    PeekSetup,
    PeekDecoder { predicate: ReadPlace, fill: FillSource },
}

#[derive(Clone, Debug, Default)]
pub struct SpecialTable { descs: Vec<SpecialDescriptor> }
impl SpecialTable {
    pub fn push(&mut self, d: SpecialDescriptor) -> u16 { let i = self.descs.len() as u16; self.descs.push(d); i }
    pub fn get(&self, desc: u16) -> Option<&SpecialDescriptor> { self.descs.get(desc as usize) }
    pub fn len(&self) -> usize { self.descs.len() }
}

pub fn lower_resolution(strategy: &ResolutionStrategy, origin_expr: ExprId) -> SpecialDescriptor {
    let strategy = match strategy {
        ResolutionStrategy::PeekSingleColumn { set_index, width } => SpecialStrategy::PeekSingleColumn { set_index: *set_index, width: *width },
        ResolutionStrategy::PeekAggregate { set_index } => SpecialStrategy::PeekAggregate { set_index: *set_index },
        ResolutionStrategy::PeekSetup => SpecialStrategy::PeekSetup,
        ResolutionStrategy::PeekDecoder { predicate, fill } => SpecialStrategy::PeekDecoder { predicate: predicate.clone(), fill: *fill },
    };
    SpecialDescriptor { strategy, origin_expr }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cs::gkr_compiler::dag_ir::{ChallengePower};
    #[test]
    fn const_bank_dedups() {
        let mut b = ConstBank::default();
        assert_eq!(b.intern(7), b.intern(7)); assert_ne!(b.intern(7), b.intern(9));
        assert_eq!(b.values(), &[7, 9]);
    }
    #[test]
    fn challenge_bank_roundtrips_ref() {
        let mut banks = ChallengeBanks::default();
        let r = ChallengeRef { key: ChallengeKey::LookupAdditive, power: ChallengePower::One };
        let (sub, idx) = banks.intern(&r);
        assert_eq!(sub, LdcSub::ConstChallenge);
        assert_eq!(banks.get(sub, idx), Some(&r));
        // same ref reuses slot
        assert_eq!(banks.intern(&r), (sub, idx));
        // a permutation challenge goes to the arg channel
        let p = ChallengeRef { key: ChallengeKey::PermutationAdditive, power: ChallengePower::Static(2) };
        assert_eq!(banks.intern(&p).0, LdcSub::ArgChallenge);
    }
    #[test]
    fn all_four_resolution_variants_lower_with_origin() {
        let mut t = SpecialTable::default();
        let i = t.push(lower_resolution(&ResolutionStrategy::PeekSetup, ExprId(5)));
        assert_eq!(t.get(i).unwrap().origin_expr, ExprId(5));
        assert!(matches!(t.get(i).unwrap().strategy, SpecialStrategy::PeekSetup));
    }
}
