use cs::gkr_compiler::dag_ir::{
    ChallengeKey, ChallengePower, DagLayer, Expr, ExprId, LookupValueKind, PermutationSlot,
    ReadPlace, SourceKind, VirtualSetupKind,
};

/// Deterministic, commutativity-insensitive identity for one DAG value.
///
/// This is provenance, not a cryptographic commitment. Persistent schedules must
/// collision-check equal fingerprints against their canonical structural form.
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
pub struct ValueFingerprint(pub [u64; 2]);

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IdentityError {
    ExprOutOfBounds(ExprId),
    SourceOutOfBounds {
        expr: ExprId,
        source: u32,
    },
    Cycle(ExprId),
    FingerprintCollision {
        fingerprint: ValueFingerprint,
        first: ExprId,
        second: ExprId,
    },
}

/// Fingerprint every expression in arena order. `Add` and `Mul` child
/// fingerprints are sorted before hashing, so legal child permutations do not
/// change value identity.
pub fn structural_fingerprints(layer: &DagLayer) -> Result<Vec<ValueFingerprint>, IdentityError> {
    let mut builder = FingerprintBuilder {
        layer,
        state: vec![VisitState::New; layer.exprs.len()],
        values: vec![None; layer.exprs.len()],
    };
    for i in 0..layer.exprs.len() {
        builder.visit(ExprId(i as u32))?;
    }
    Ok(builder.values.into_iter().map(Option::unwrap).collect())
}

/// Prove that the compact fingerprints used by persistent planning artifacts
/// are unambiguous within this layer. The comparison uses a full canonical
/// expression encoding, with commutative children sorted by their encodings.
pub fn validate_structural_identity(layer: &DagLayer) -> Result<(), IdentityError> {
    use std::collections::BTreeMap;

    let fingerprints = structural_fingerprints(layer)?;
    let mut builder = CanonicalBuilder {
        layer,
        state: vec![VisitState::New; layer.exprs.len()],
        values: vec![None; layer.exprs.len()],
    };
    let mut first_by_fingerprint = BTreeMap::<ValueFingerprint, (ExprId, Vec<u8>)>::new();
    for (index, &fingerprint) in fingerprints.iter().enumerate() {
        let expr = ExprId(index as u32);
        let canonical = builder.visit(expr)?;
        if let Some((first, first_canonical)) = first_by_fingerprint.get(&fingerprint) {
            if first_canonical != &canonical {
                return Err(IdentityError::FingerprintCollision {
                    fingerprint,
                    first: *first,
                    second: expr,
                });
            }
        } else {
            first_by_fingerprint.insert(fingerprint, (expr, canonical));
        }
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum VisitState {
    New,
    Active,
    Done,
}

struct FingerprintBuilder<'a> {
    layer: &'a DagLayer,
    state: Vec<VisitState>,
    values: Vec<Option<ValueFingerprint>>,
}

struct CanonicalBuilder<'a> {
    layer: &'a DagLayer,
    state: Vec<VisitState>,
    values: Vec<Option<Vec<u8>>>,
}

impl CanonicalBuilder<'_> {
    fn visit(&mut self, id: ExprId) -> Result<Vec<u8>, IdentityError> {
        let index = id.0 as usize;
        if index >= self.layer.exprs.len() {
            return Err(IdentityError::ExprOutOfBounds(id));
        }
        match self.state[index] {
            VisitState::Done => return Ok(self.values[index].as_ref().unwrap().clone()),
            VisitState::Active => return Err(IdentityError::Cycle(id)),
            VisitState::New => {}
        }
        self.state[index] = VisitState::Active;
        let mut out = Vec::new();
        match &self.layer.exprs[index] {
            Expr::Source(source) => {
                out.push(0x01);
                let Some(info) = self.layer.sources.get(source.0 as usize) else {
                    return Err(IdentityError::SourceOutOfBounds {
                        expr: id,
                        source: source.0,
                    });
                };
                self.encode_source(&mut out, &info.kind)?;
            }
            Expr::Add(children) => self.encode_children(&mut out, 0x02, children)?,
            Expr::Mul(children) => self.encode_children(&mut out, 0x03, children)?,
        }
        self.values[index] = Some(out.clone());
        self.state[index] = VisitState::Done;
        Ok(out)
    }

    fn encode_children(
        &mut self,
        out: &mut Vec<u8>,
        tag: u8,
        children: &[ExprId],
    ) -> Result<(), IdentityError> {
        out.push(tag);
        let mut encoded = children
            .iter()
            .map(|&child| self.visit(child))
            .collect::<Result<Vec<_>, _>>()?;
        encoded.sort_unstable();
        push_usize(out, encoded.len());
        for child in encoded {
            push_usize(out, child.len());
            out.extend_from_slice(&child);
        }
        Ok(())
    }

    fn encode_source(
        &mut self,
        out: &mut Vec<u8>,
        source: &SourceKind,
    ) -> Result<(), IdentityError> {
        match source {
            SourceKind::Read { place } => {
                out.push(0x10);
                encode_read_place(out, place);
            }
            SourceKind::Constant { value } => {
                out.push(0x11);
                out.extend_from_slice(&value.to_le_bytes());
            }
            SourceKind::Challenge { reference } => {
                out.push(0x12);
                encode_challenge_key(out, &reference.key);
                match reference.power {
                    ChallengePower::One => out.push(0),
                    ChallengePower::Static(power) => {
                        out.push(1);
                        out.extend_from_slice(&power.to_le_bytes());
                    }
                }
            }
            SourceKind::VirtualSetup { kind } => {
                out.push(0x13);
                encode_virtual_setup(out, kind);
            }
            SourceKind::LookupValue {
                kind,
                set_index,
                query,
            } => {
                out.push(0x14);
                encode_lookup_kind(out, kind);
                push_usize(out, *set_index);
                let query = self.visit(*query)?;
                push_usize(out, query.len());
                out.extend_from_slice(&query);
            }
        }
        Ok(())
    }
}

fn push_usize(out: &mut Vec<u8>, value: usize) {
    out.extend_from_slice(&(value as u64).to_le_bytes());
}

fn encode_read_place(out: &mut Vec<u8>, place: &ReadPlace) {
    match place {
        ReadPlace::BaseLayerMemory { column } => {
            out.push(0);
            push_usize(out, *column);
        }
        ReadPlace::BaseLayerWitness { column } => {
            out.push(1);
            push_usize(out, *column);
        }
        ReadPlace::Setup { column } => {
            out.push(2);
            push_usize(out, *column);
        }
        ReadPlace::Scratch { slot } => {
            out.push(3);
            push_usize(out, *slot);
        }
        ReadPlace::LayerOutput { layer, offset } => {
            out.push(4);
            push_usize(out, *layer);
            push_usize(out, *offset);
        }
        ReadPlace::CacheOutput { layer, offset } => {
            out.push(5);
            push_usize(out, *layer);
            push_usize(out, *offset);
        }
    }
}

fn encode_challenge_key(out: &mut Vec<u8>, key: &ChallengeKey) {
    match key {
        ChallengeKey::LookupAdditive => out.push(0),
        ChallengeKey::LookupMultiplicative => out.push(1),
        ChallengeKey::PermutationAdditive => out.push(2),
        ChallengeKey::PermutationLinearization(slot) => {
            out.push(3);
            out.push(match slot {
                PermutationSlot::AddressLow => 0,
                PermutationSlot::AddressHigh => 1,
                PermutationSlot::TimestampLow => 2,
                PermutationSlot::TimestampHigh => 3,
                PermutationSlot::ValueLow => 4,
                PermutationSlot::ValueHigh => 5,
            });
        }
        ChallengeKey::ConstraintAggregation => out.push(4),
        ChallengeKey::ClaimBatching => out.push(5),
    }
}

fn encode_virtual_setup(out: &mut Vec<u8>, kind: &VirtualSetupKind) {
    out.push(match kind {
        VirtualSetupKind::RangeCheck16Bits => 0,
        VirtualSetupKind::RangeCheckTimestamp => 1,
        VirtualSetupKind::InitsAndTeardownsLow => 2,
        VirtualSetupKind::InitsAndTeardownsHigh => 3,
    });
}

fn encode_lookup_kind(out: &mut Vec<u8>, kind: &LookupValueKind) {
    match kind {
        LookupValueKind::RangeCheck16Index => out.push(0),
        LookupValueKind::TimestampIndex => out.push(1),
        LookupValueKind::GenericColumn { column } => {
            out.push(2);
            push_usize(out, *column);
        }
        LookupValueKind::DecoderColumn { column } => {
            out.push(3);
            push_usize(out, *column);
        }
    }
}

impl FingerprintBuilder<'_> {
    fn visit(&mut self, id: ExprId) -> Result<ValueFingerprint, IdentityError> {
        let index = id.0 as usize;
        if index >= self.layer.exprs.len() {
            return Err(IdentityError::ExprOutOfBounds(id));
        }
        match self.state[index] {
            VisitState::Done => return Ok(self.values[index].unwrap()),
            VisitState::Active => return Err(IdentityError::Cycle(id)),
            VisitState::New => {}
        }
        self.state[index] = VisitState::Active;

        let mut h = StableHasher::new();
        match &self.layer.exprs[index] {
            Expr::Source(source) => {
                h.tag(0x01);
                let Some(info) = self.layer.sources.get(source.0 as usize) else {
                    return Err(IdentityError::SourceOutOfBounds {
                        expr: id,
                        source: source.0,
                    });
                };
                self.hash_source(&mut h, &info.kind)?;
            }
            Expr::Add(children) => {
                h.tag(0x02);
                self.hash_commutative_children(&mut h, children)?;
            }
            Expr::Mul(children) => {
                h.tag(0x03);
                self.hash_commutative_children(&mut h, children)?;
            }
        }
        let value = h.finish();
        self.values[index] = Some(value);
        self.state[index] = VisitState::Done;
        Ok(value)
    }

    fn hash_commutative_children(
        &mut self,
        h: &mut StableHasher,
        children: &[ExprId],
    ) -> Result<(), IdentityError> {
        let mut values = Vec::with_capacity(children.len());
        for &child in children {
            values.push(self.visit(child)?);
        }
        values.sort_unstable();
        h.usize(values.len());
        for value in values {
            h.fingerprint(value);
        }
        Ok(())
    }

    fn hash_source(
        &mut self,
        h: &mut StableHasher,
        source: &SourceKind,
    ) -> Result<(), IdentityError> {
        match source {
            SourceKind::Read { place } => {
                h.tag(0x10);
                hash_read_place(h, place);
            }
            SourceKind::Constant { value } => {
                h.tag(0x11);
                h.u32(*value);
            }
            SourceKind::Challenge { reference } => {
                h.tag(0x12);
                hash_challenge_key(h, &reference.key);
                match reference.power {
                    ChallengePower::One => h.tag(0),
                    ChallengePower::Static(power) => {
                        h.tag(1);
                        h.u32(power);
                    }
                }
            }
            SourceKind::VirtualSetup { kind } => {
                h.tag(0x13);
                hash_virtual_setup(h, kind);
            }
            SourceKind::LookupValue {
                kind,
                set_index,
                query,
            } => {
                h.tag(0x14);
                hash_lookup_kind(h, kind);
                h.usize(*set_index);
                h.fingerprint(self.visit(*query)?);
            }
        }
        Ok(())
    }
}

fn hash_read_place(h: &mut StableHasher, place: &ReadPlace) {
    match place {
        ReadPlace::BaseLayerMemory { column } => {
            h.tag(0);
            h.usize(*column);
        }
        ReadPlace::BaseLayerWitness { column } => {
            h.tag(1);
            h.usize(*column);
        }
        ReadPlace::Setup { column } => {
            h.tag(2);
            h.usize(*column);
        }
        ReadPlace::Scratch { slot } => {
            h.tag(3);
            h.usize(*slot);
        }
        ReadPlace::LayerOutput { layer, offset } => {
            h.tag(4);
            h.usize(*layer);
            h.usize(*offset);
        }
        ReadPlace::CacheOutput { layer, offset } => {
            h.tag(5);
            h.usize(*layer);
            h.usize(*offset);
        }
    }
}

fn hash_challenge_key(h: &mut StableHasher, key: &ChallengeKey) {
    match key {
        ChallengeKey::LookupAdditive => h.tag(0),
        ChallengeKey::LookupMultiplicative => h.tag(1),
        ChallengeKey::PermutationAdditive => h.tag(2),
        ChallengeKey::PermutationLinearization(slot) => {
            h.tag(3);
            h.tag(match slot {
                PermutationSlot::AddressLow => 0,
                PermutationSlot::AddressHigh => 1,
                PermutationSlot::TimestampLow => 2,
                PermutationSlot::TimestampHigh => 3,
                PermutationSlot::ValueLow => 4,
                PermutationSlot::ValueHigh => 5,
            });
        }
        ChallengeKey::ConstraintAggregation => h.tag(4),
        ChallengeKey::ClaimBatching => h.tag(5),
    }
}

fn hash_virtual_setup(h: &mut StableHasher, kind: &VirtualSetupKind) {
    h.tag(match kind {
        VirtualSetupKind::RangeCheck16Bits => 0,
        VirtualSetupKind::RangeCheckTimestamp => 1,
        VirtualSetupKind::InitsAndTeardownsLow => 2,
        VirtualSetupKind::InitsAndTeardownsHigh => 3,
    });
}

fn hash_lookup_kind(h: &mut StableHasher, kind: &LookupValueKind) {
    match kind {
        LookupValueKind::RangeCheck16Index => h.tag(0),
        LookupValueKind::TimestampIndex => h.tag(1),
        LookupValueKind::GenericColumn { column } => {
            h.tag(2);
            h.usize(*column);
        }
        LookupValueKind::DecoderColumn { column } => {
            h.tag(3);
            h.usize(*column);
        }
    }
}

/// Two independently seeded FNV-1a lanes. Explicit integer byte order makes the
/// result deterministic across hosts and Rust hash-map seeds.
struct StableHasher {
    lanes: [u64; 2],
}

impl StableHasher {
    const PRIME: u64 = 0x0000_0100_0000_01b3;

    fn new() -> Self {
        Self {
            lanes: [0xcbf2_9ce4_8422_2325, 0x8422_2325_cbf2_9ce4],
        }
    }

    fn tag(&mut self, value: u8) {
        self.bytes(&[value]);
    }

    fn u32(&mut self, value: u32) {
        self.bytes(&value.to_le_bytes());
    }

    fn usize(&mut self, value: usize) {
        self.bytes(&(value as u64).to_le_bytes());
    }

    fn fingerprint(&mut self, value: ValueFingerprint) {
        self.bytes(&value.0[0].to_le_bytes());
        self.bytes(&value.0[1].to_le_bytes());
    }

    fn bytes(&mut self, bytes: &[u8]) {
        for &byte in bytes {
            self.lanes[0] ^= u64::from(byte);
            self.lanes[0] = self.lanes[0].wrapping_mul(Self::PRIME);
            self.lanes[1] ^= u64::from(byte).wrapping_add(0x9d);
            self.lanes[1] = self.lanes[1].wrapping_mul(Self::PRIME.rotate_left(17));
        }
    }

    fn finish(self) -> ValueFingerprint {
        ValueFingerprint(self.lanes)
    }
}
