//! Per-layer lean coordinate artifacts (segmented-lean-VM design §4, §6;
//! coefficient-ISA design §13).
//!
//! One [`LeanCoordinateArtifact`] is everything the segmented VM needs to be
//! launched for one `(circuit, layer, regime)`, and nothing else: a
//! `layer` / `regime` / `target_depth` identity plus the three objects the lean
//! pipeline produces —
//!
//! ```text
//! R0:  lower_coeff_layer                     -> order_terms -> encode_program
//! Ext: lower_coeff_layer -> group_coeff_layer -> order_atoms -> encode_program_atoms
//!                                                            \-> flatten_atoms
//!   both: -> bind_lean_sources -> validate_program
//! ```
//!
//! `Ext` coordinates are GROUPED (grouped-coefficient design §4.1-§4.4): the
//! coefficient grouping transform is part of production lowering, so a continuation
//! program is a stream of ATOMS — a group header record plus its member records, or
//! one plain record — while the committed `order` stays a flat `TermId` permutation.
//! R0 has no atoms and takes the term-granular passes verbatim.
//!
//! the committed term order, the fixed-width term program, and the placement-free
//! source binding. There is no budget dimension, no paging plan, no cell file and
//! therefore no paging or liveness certificate: the segmented VM has no resident
//! state for one to be about.
//!
//! # `K`-free by construction
//!
//! The per-warp split is [`split_round_robin`](super::order::split_round_robin), a
//! positional function of `(list, K)` computed at descriptor build time. An
//! artifact stores the committed list and never a `K`, so one artifact serves every
//! launch shape.
//!
//! # What is deliberately NOT here
//!
//! No physical pointer, no stride, no publish backing, no measured selection and no
//! runtime. §13 keeps the artifact a pure function of the DAG, which is what makes
//! the corpus byte-identical across processes — the property
//! `bwd_lean_artifacts_are_byte_identical_across_processes` rests on.

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use cs::gkr_compiler::dag_ir::{BwdRegime, DagLayer, FieldKind, ReadPlace};
use serde::{Deserialize, Serialize};

use super::group::group_coeff_layer;
use super::lean::{
    LeanCodecError, LeanProgram, encode_program, encode_program_atoms, validate_program,
};
use super::lean_bind::{LeanBindError, LeanSourceBinding, bind_lean_sources};
use super::lower::lower_coeff_layer;
use super::model::{CoeffError, CoeffLayer, TermId};
use super::order::{flatten_atoms, order_atoms, order_terms};
use crate::bwd::distill::distill;
use crate::bwd::source::VIRTUAL_SETUP_MATERIALIZE_DEPTH;

// ── Schema ───────────────────────────────────────────────────────────────────

/// The serialized spelling of [`BwdRegime`], which is not `serde`-derived
/// upstream. `R0` / `Ext`, the same two labels every report in this crate uses.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum ArtifactRegime {
    R0,
    Ext,
}

impl ArtifactRegime {
    pub fn of(regime: BwdRegime) -> Self {
        match regime {
            BwdRegime::R0 => ArtifactRegime::R0,
            BwdRegime::Ext => ArtifactRegime::Ext,
        }
    }

    pub fn regime(self) -> BwdRegime {
        match self {
            ArtifactRegime::R0 => BwdRegime::R0,
            ArtifactRegime::Ext => BwdRegime::Ext,
        }
    }

    pub fn label(self) -> &'static str {
        match self {
            ArtifactRegime::R0 => "R0",
            ArtifactRegime::Ext => "Ext",
        }
    }
}

/// One `(layer, regime)` lean coordinate: one program, one binding, one order.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LeanCoordinateArtifact {
    pub layer: usize,
    pub regime: ArtifactRegime,
    /// The fold depth this program is bound for (§10.2). A binding input, not a
    /// physical address: GPU round lowering supplies the round's own depth.
    pub target_depth: u8,
    /// The committed term order, as dense [`TermId`] indices — a permutation of
    /// `0..terms`, which is what makes the program a complete encoding of the layer
    /// rather than a prefix of one.
    pub order: Vec<u32>,
    pub program: LeanProgram,
    pub binding: LeanSourceBinding,
}

/// One circuit's complete lean artifact.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LeanCircuitArtifact {
    /// The committed layout file name — the circuit's identity.
    pub circuit: String,
    /// Ascending by `(layer, regime)`.
    pub coordinates: Vec<LeanCoordinateArtifact>,
}

impl LeanCircuitArtifact {
    /// Assemble one circuit's artifact, sorted into its canonical order.
    pub fn new(circuit: &str, mut coordinates: Vec<LeanCoordinateArtifact>) -> Self {
        coordinates.sort_by_key(|c| (c.layer, c.regime));
        LeanCircuitArtifact { circuit: circuit.to_string(), coordinates }
    }
}

/// The lean artifact file name for one circuit, mirroring the committed-schedule
/// spelling and naming the lineage so it cannot collide with the `c2`-`c16` family.
pub fn lean_artifact_file_name(circuit: &str) -> String {
    format!("{}_bwd_lean.json", circuit.trim_end_matches(".json"))
}

/// Serialize one circuit's lean artifact to its canonical bytes: pretty JSON plus a
/// trailing newline.
///
/// Deterministic by construction — every container in the schema is a `Vec` in a
/// fixed order, so two runs that agree on the programs agree on the bytes.
pub fn lean_artifact_bytes(artifact: &LeanCircuitArtifact) -> Vec<u8> {
    let mut bytes = serde_json::to_vec_pretty(artifact).expect("the schema is plain data");
    bytes.push(b'\n');
    bytes
}

/// Write one circuit's lean artifact ONCE, after its complete chain has succeeded.
pub fn write_lean_circuit_artifact(
    directory: &Path,
    artifact: &LeanCircuitArtifact,
) -> std::io::Result<PathBuf> {
    std::fs::create_dir_all(directory)?;
    let path = directory.join(lean_artifact_file_name(&artifact.circuit));
    std::fs::write(&path, lean_artifact_bytes(artifact))?;
    Ok(path)
}

/// Read back one circuit's lean artifact.
pub fn read_lean_circuit_artifact(path: &Path) -> std::io::Result<LeanCircuitArtifact> {
    let bytes = std::fs::read(path)?;
    serde_json::from_slice(&bytes).map_err(std::io::Error::other)
}

// ── Errors ───────────────────────────────────────────────────────────────────

/// Everything lean coordinate compilation can reject — one variant per stage of
/// the pipeline. Every variant is derivable from the inputs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LeanArtifactError {
    /// The canonical layer does not lower.
    Lower(CoeffError),
    /// The codec, or its validator, rejected the program.
    Codec(LeanCodecError),
    /// The binder rejected the layer's source layout.
    Bind(LeanBindError),
}

impl From<CoeffError> for LeanArtifactError {
    fn from(e: CoeffError) -> Self {
        LeanArtifactError::Lower(e)
    }
}

impl From<LeanCodecError> for LeanArtifactError {
    fn from(e: LeanCodecError) -> Self {
        LeanArtifactError::Codec(e)
    }
}

impl From<LeanBindError> for LeanArtifactError {
    fn from(e: LeanBindError) -> Self {
        LeanArtifactError::Bind(e)
    }
}

// ── Compilation ──────────────────────────────────────────────────────────────

/// The fold depth one regime's lean program is bound at.
///
/// R0 is round zero, so its depth is exactly `0`. A continuation program is ONE
/// artifact per `(circuit, layer, Ext)` and must therefore be bound at a single
/// depth; the published steady state is that depth, since it covers every
/// continuation round but the first
/// [`VIRTUAL_SETUP_MATERIALIZE_DEPTH`] of them.
///
/// The lean pipeline's ONLY target-depth authority since the cell-era scheduler
/// was retired. It reads [`VIRTUAL_SETUP_MATERIALIZE_DEPTH`] directly, the same
/// constant [`limits::PUBLISH_TARGET_DEPTH`](super::limits::PUBLISH_TARGET_DEPTH)
/// names for the publication threshold.
pub const fn lean_target_depth(regime: BwdRegime) -> u8 {
    match regime {
        BwdRegime::R0 => 0,
        BwdRegime::Ext => VIRTUAL_SETUP_MATERIALIZE_DEPTH,
    }
}

/// Whether `order` is a permutation of `0..terms` — i.e. whether it names every
/// term of the layer exactly once.
///
/// The lean codec deliberately does NOT check this: `validate_program` compares the
/// stream against `term_count`, which a partial or repeated order satisfies just as
/// well as a complete one. Coverage is an ARTIFACT-level property — a program that
/// encodes a prefix of its layer is a silently wrong answer, not a malformed
/// stream — so it is checked here, once, before anything is encoded.
pub fn order_covers_layer(order: &[TermId], terms: usize) -> bool {
    if order.len() != terms {
        return false;
    }
    let mut seen = vec![false; terms];
    for id in order {
        match seen.get_mut(id.0 as usize) {
            Some(slot) if !*slot => *slot = true,
            _ => return false,
        }
    }
    true
}

/// Lower one canonical layer in one regime, into the lean IR.
///
/// `Ext` layers come back GROUPED (grouped-coefficient design §4.1): the
/// coefficient grouping transform is part of production lowering, so every
/// consumer of a continuation layer — the interpreter, the descriptor deal, the
/// artifact encoder — sees the same grouped model. R0 layers are returned
/// verbatim; grouping is `Ext`-only, and [`group_coeff_layer`] would pass an R0
/// layer through untouched anyway, so the match here is a statement of intent
/// rather than the only guard.
///
/// Nothing in this pipeline is priced: the per-list work model needs the
/// round-binding dependent source classes, which do not exist at the
/// [`CoeffLayer`] layer.
pub fn lower_lean_layer(
    canonical: &DagLayer,
    cross_fields: &HashMap<ReadPlace, FieldKind>,
    regime: BwdRegime,
) -> Result<(CoeffLayer, u8), LeanArtifactError> {
    let distilled = distill(canonical, regime, cross_fields, None);
    let layer = lower_coeff_layer(canonical, &distilled)?;
    let layer = match regime {
        BwdRegime::R0 => layer,
        BwdRegime::Ext => group_coeff_layer(layer)?,
    };
    Ok((layer, lean_target_depth(regime)))
}

/// Compile one `(circuit, layer, regime)` lean coordinate.
///
/// Fallible as a whole: the chain either succeeds outright or returns its first
/// failure. Nothing is written from here — the caller writes one circuit's
/// artifact once its coordinates have all succeeded.
///
/// The two regimes take different ordering and encoding passes, because only `Ext`
/// has atoms: R0 orders TERMS and encodes one record each, `Ext` orders ATOMS
/// ([`order_atoms`]) and encodes each as a group header plus its members or as one
/// plain record ([`encode_program_atoms`]). The artifact's `order` field is a
/// `TermId` permutation in both cases — [`flatten_atoms`] is what turns the `Ext`
/// atom order back into one — so the coverage check and the source binder are the
/// same call on both paths.
///
/// # Panics
///
/// If the ordering pass does not return a permutation of the layer's terms. That is
/// a compiler bug in the ordering pass, not a property of the input DAG, and it is
/// checked here because it is the one defect the codec's validator cannot see: a
/// partial order encodes a program that is well-formed and wrong.
pub fn compile_lean_coordinate(
    circuit: &str,
    layer_index: usize,
    canonical: &DagLayer,
    cross_fields: &HashMap<ReadPlace, FieldKind>,
    regime: BwdRegime,
) -> Result<LeanCoordinateArtifact, LeanArtifactError> {
    let (layer, target_depth) = lower_lean_layer(canonical, cross_fields, regime)?;
    // The committed order: over TERMS at R0, over ATOMS in `Ext`. `order` is the
    // FLATTENED term permutation either way, and it is checked BEFORE anything is
    // encoded — an encoder handed a malformed order would panic on a term index
    // instead of reporting which coordinate's ordering pass is broken.
    let atoms = match regime {
        BwdRegime::R0 => None,
        BwdRegime::Ext => Some(order_atoms(&layer)),
    };
    let order = match &atoms {
        None => order_terms(&layer),
        Some(atoms) => flatten_atoms(&layer, atoms),
    };
    assert!(
        order_covers_layer(&order, layer.terms.len()),
        "[{circuit} L{layer_index} {regime:?}] the committed order is not a permutation of the \
         layer's {} terms ({} entries)",
        layer.terms.len(),
        order.len(),
    );

    let program = match &atoms {
        None => encode_program(&layer, &order)?,
        Some(atoms) => encode_program_atoms(&layer, atoms)?,
    };
    let binding = bind_lean_sources(&layer, cross_fields, &order, target_depth)?;
    validate_program(&program, &layer)?;

    Ok(LeanCoordinateArtifact {
        layer: layer_index,
        regime: ArtifactRegime::of(regime),
        target_depth,
        order: order.iter().map(|id| id.0).collect(),
        program,
        binding,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bwd::coeff::limits::PUBLISH_TARGET_DEPTH;

    /// R0 is round zero; the continuation depth is the publication threshold, and
    /// the two spellings of that threshold must not drift apart.
    #[test]
    fn lean_target_depth_is_the_publication_threshold() {
        assert_eq!(lean_target_depth(BwdRegime::R0), 0);
        assert_eq!(lean_target_depth(BwdRegime::Ext), 3);
        assert_eq!(lean_target_depth(BwdRegime::Ext), PUBLISH_TARGET_DEPTH);
    }

    /// The check the lean codec deliberately does not make: a partial order, a
    /// repeated one, and one naming a term the layer does not have are all rejected;
    /// only a true permutation passes.
    #[test]
    fn only_a_permutation_covers_the_layer() {
        let ids = |slots: &[u32]| slots.iter().copied().map(TermId).collect::<Vec<_>>();
        assert!(order_covers_layer(&ids(&[0, 1, 2]), 3), "the identity order covers");
        assert!(order_covers_layer(&ids(&[2, 0, 1]), 3), "any permutation covers");
        assert!(order_covers_layer(&[], 0), "an empty layer is covered by an empty order");

        assert!(!order_covers_layer(&ids(&[0, 1]), 3), "a partial order does not cover");
        assert!(!order_covers_layer(&ids(&[0, 1, 1]), 3), "a repeated term does not cover");
        assert!(!order_covers_layer(&ids(&[0, 1, 3]), 3), "an unknown term does not cover");
        assert!(!order_covers_layer(&ids(&[0, 1, 2, 2]), 3), "a long order does not cover");
    }

    #[test]
    fn the_file_name_names_the_lean_lineage() {
        assert_eq!(
            lean_artifact_file_name("shift_binop_layout_gkr.json"),
            "shift_binop_layout_gkr_bwd_lean.json",
        );
        assert_eq!(lean_artifact_file_name("plain"), "plain_bwd_lean.json");
    }

    /// Coordinates are sorted into `(layer, regime)` order regardless of the order
    /// the parallel compile produced them in — the artifact's canonical form.
    #[test]
    fn a_circuit_artifact_is_sorted_by_coordinate() {
        let coordinate = |layer: usize, regime: ArtifactRegime| LeanCoordinateArtifact {
            layer,
            regime,
            target_depth: 0,
            order: Vec::new(),
            program: LeanProgram { words: Vec::new(), term_count: 0 },
            binding: LeanSourceBinding { windows: Vec::new(), source_slots: Vec::new() },
        };
        let artifact = LeanCircuitArtifact::new(
            "c.json",
            vec![
                coordinate(1, ArtifactRegime::R0),
                coordinate(0, ArtifactRegime::Ext),
                coordinate(0, ArtifactRegime::R0),
            ],
        );
        assert_eq!(
            artifact.coordinates.iter().map(|c| (c.layer, c.regime)).collect::<Vec<_>>(),
            vec![(0, ArtifactRegime::R0), (0, ArtifactRegime::Ext), (1, ArtifactRegime::R0),],
        );
    }

    /// The canonical bytes round-trip, and they are stable: serializing what was
    /// read back gives the same bytes.
    #[test]
    fn canonical_bytes_round_trip() {
        let artifact = LeanCircuitArtifact::new(
            "c.json",
            vec![LeanCoordinateArtifact {
                layer: 3,
                regime: ArtifactRegime::Ext,
                target_depth: 3,
                order: vec![1, 0],
                program: LeanProgram { words: vec![0, 1, 2, 0, 3, 4, 5, 0], term_count: 2 },
                binding: LeanSourceBinding { windows: Vec::new(), source_slots: Vec::new() },
            }],
        );
        let bytes = lean_artifact_bytes(&artifact);
        assert_eq!(bytes.last(), Some(&b'\n'), "canonical bytes end in a newline");
        let read: LeanCircuitArtifact =
            serde_json::from_slice(&bytes).expect("the schema round trips");
        assert_eq!(read, artifact);
        assert_eq!(lean_artifact_bytes(&read), bytes);
    }
}
