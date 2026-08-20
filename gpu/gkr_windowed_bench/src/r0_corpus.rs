use std::collections::{BTreeMap, BTreeSet};
use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};

use cs::gkr_compiler::GKRCircuitArtifact;
use field::baby_bear::base::BabyBearField;
use gkr_eval_ir::{DagLayer, Expr, SourceKind};
use gpu_gkr_compiler::backward::{decode_r0_program, LeanAtom, LEAN_MAX_IMMEDIATES, SOURCE_NONE};
use gpu_gkr_compiler::compile_r0;
use serde::{Deserialize, Serialize};

use crate::census;
use crate::r0_artifact::{
    encode_r0_bundle, inspect_r0_bundle, r0_coordinate_payload_sha256, FrozenR0BundleV1,
    FrozenR0Challenge, FrozenR0Coordinate, FrozenR0Product, FrozenR0Recipe, FrozenR0Shape,
    R0ArtifactError, R0CoordinateOffsets, R0LayoutHash, R0_BUNDLE_MAGIC, R0_BUNDLE_VERSION,
    R0_DECLARED_COEFFICIENTS, R0_DECLARED_PROGRAM_WORDS, R0_DECLARED_PROJECTIONS,
    R0_DECLARED_RECORDS, R0_DECLARED_SOURCES, R0_DECLARED_WINDOWS, R0_RECORD_WORDS,
};

pub const R0_CORPUS_SCHEMA_VERSION: u32 = 1;

const EXPECTED_LAYOUT_HASHES: [(&str, &str); 12] = [
    (
        "add_sub_lui_auipc_mop_layout_gkr.json",
        "b421fcb2049bf432ce0551556833be1ae5c35d9e5b344b19372340459ae1315a",
    ),
    (
        "bigint_with_extended_control_layout_gkr.json",
        "7c8d441c144da4ed2199876df586cbc57f6574c8ca00be945349f2224a828b07",
    ),
    (
        "blake2_g_function_layout_gkr.json",
        "23dc94749ffa4a17d64f35f5aeb394f272b56189a1499a720233db67b325de54",
    ),
    (
        "blake2_with_extended_control_layout_gkr.json",
        "dd7d58a56de8e2ee2c096f49d402003dc463ebf7c5ee8246711253cc910c6976",
    ),
    (
        "inits_and_teardowns_layout_gkr.json",
        "3233f9150a98448d9382277a22d0e0e4fad07754ab3164db6a16b1caa99b1277",
    ),
    (
        "jump_branch_slt_layout_gkr.json",
        "e9ee838a338abc7a9901a3d2e852fb74a272f8d796308634203d4b671ab68484",
    ),
    (
        "keccak_special5_layout_gkr.json",
        "a815de1c7657f606a4cc4820340fcb115d4c8dd0cd134f645fd77cdf6e86388b",
    ),
    (
        "mem_subword_only_layout_gkr.json",
        "7bfbe3e956c4baae5344d9d8ce735f9828f8b7983807e436459b06f4015da8c9",
    ),
    (
        "mem_word_only_layout_gkr.json",
        "a91ec0280a06a392da5cf146e54783fd7dd6b1107ada87558d6e32b27f0766eb",
    ),
    (
        "shift_binop_layout_gkr.json",
        "22451436ccabb6d2636482f22f92397b7295d018ccba18882544df70106bc261",
    ),
    (
        "unified_reduced_machine_layout_gkr.json",
        "53331555ffd08dab4dd3f71be8011528a52d3584f435320a8a0b2ffd9121add8",
    ),
    (
        "unsigned_mul_div_layout_gkr.json",
        "efb41b4f3d9f1ebcada31e766390ce6756f7669b66e096cfed0c19b2ae3d824b",
    ),
];

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct R0DeclaredCapacityV1 {
    pub records: u32,
    pub program_words: u32,
    pub program_bytes: u32,
    pub projections: u32,
    pub coefficient_recipes: u32,
    pub immediates: u32,
    pub sources: u32,
    pub windows: u32,
    pub columns_per_window: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct R0CircuitCountV1 {
    pub circuit: String,
    pub layers: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct R0ManifestCoordinateV1 {
    pub circuit: String,
    pub layer: u32,
    pub trace_len: u64,
    pub passes_per_invocation: u32,
    pub canonical_lookup_value_nodes: u32,
    pub materialized_root_sinks: u32,
    pub shape: FrozenR0Shape,
    pub offsets: R0CoordinateOffsets,
    pub program_sha256: String,
    pub binding_sha256: String,
    pub recipes_sha256: String,
    pub payload_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct R0ManifestV1 {
    pub schema_version: u32,
    pub bundle_sha256: String,
    pub layout_hashes: Vec<R0LayoutHash>,
    pub declared: R0DeclaredCapacityV1,
    pub circuit_layer_counts: Vec<R0CircuitCountV1>,
    pub coordinates: Vec<R0ManifestCoordinateV1>,
    pub max_records: u32,
    pub max_projections: u32,
    pub max_bf_atoms: u32,
    pub max_e4_atoms: u32,
    pub max_sources: u32,
    pub max_windows: u16,
    pub max_relative_column: u16,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum R0CorpusError {
    ReadLayout {
        layout: String,
        error: String,
    },
    ParseLayout {
        layout: String,
        error: String,
    },
    LowerLayout {
        layout: String,
        error: String,
    },
    ValidateLayout {
        layout: String,
        error: String,
    },
    CompileLayout {
        layout: String,
        error: String,
    },
    DecodeProgram {
        coordinate: String,
        error: String,
    },
    CanonicalDag {
        coordinate: String,
        error: String,
    },
    GroupHeader {
        coordinate: String,
    },
    ClassAboveR0 {
        coordinate: String,
        class: u8,
    },
    CInitPresent {
        coordinate: String,
    },
    CapacityOverflow {
        coordinate: String,
        resource: &'static str,
        required: usize,
        declared: usize,
    },
    DuplicateCoordinate {
        coordinate: String,
    },
    LayerCoverage {
        layout: String,
        compiled: usize,
        canonical: usize,
    },
    InputLayoutHashDrift {
        layout: String,
        expected: String,
        actual: String,
    },
    MissingExpectedLayoutHash {
        layout: String,
    },
    Artifact(R0ArtifactError),
    CoordinateOffsetMismatch {
        coordinate: String,
    },
    OffsetRange {
        coordinate: String,
        section: &'static str,
    },
    Hash(String),
    LengthOverflow,
}

impl core::fmt::Display for R0CorpusError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for R0CorpusError {}

impl From<R0ArtifactError> for R0CorpusError {
    fn from(error: R0ArtifactError) -> Self {
        Self::Artifact(error)
    }
}

struct BuiltCoordinate {
    coordinate: FrozenR0Coordinate,
    canonical_lookup_value_nodes: u32,
    materialized_root_sinks: u32,
    field_class_bf_atoms: u32,
    field_class_e4_atoms: u32,
}

pub fn generate_r0_bundle() -> Result<(FrozenR0BundleV1, R0ManifestV1), R0CorpusError> {
    let directory = corpus_directory();
    let mut layout_names = census::CORPUS.to_vec();
    layout_names.sort_unstable();

    let mut layout_hashes = Vec::with_capacity(layout_names.len());
    let mut built_coordinates = Vec::new();
    for layout_name in layout_names {
        let path = directory.join(layout_name);
        let bytes = std::fs::read(&path).map_err(|error| R0CorpusError::ReadLayout {
            layout: layout_name.to_owned(),
            error: error.to_string(),
        })?;
        let actual_hash = sha256(&bytes)?;
        let expected_hash = expected_layout_hash(layout_name).ok_or_else(|| {
            R0CorpusError::MissingExpectedLayoutHash {
                layout: layout_name.to_owned(),
            }
        })?;
        if actual_hash != expected_hash {
            return Err(R0CorpusError::InputLayoutHashDrift {
                layout: layout_name.to_owned(),
                expected: expected_hash.to_owned(),
                actual: actual_hash,
            });
        }
        layout_hashes.push(R0LayoutHash {
            path: format!("../../cs/compiled_circuits/{layout_name}"),
            sha256: expected_hash.to_owned(),
        });

        let artifact: GKRCircuitArtifact<BabyBearField> =
            serde_json::from_slice(&bytes).map_err(|error| R0CorpusError::ParseLayout {
                layout: layout_name.to_owned(),
                error: error.to_string(),
            })?;
        let dag =
            gkr_eval_ir::lower_dag(&artifact).map_err(|error| R0CorpusError::LowerLayout {
                layout: layout_name.to_owned(),
                error: error.to_string(),
            })?;
        gkr_eval_ir::validate(&dag).map_err(|error| R0CorpusError::ValidateLayout {
            layout: layout_name.to_owned(),
            error,
        })?;
        let compiled = compile_r0(&dag).map_err(|error| R0CorpusError::CompileLayout {
            layout: layout_name.to_owned(),
            error: error.to_string(),
        })?;
        if compiled.layers.len() != dag.layers.len() {
            return Err(R0CorpusError::LayerCoverage {
                layout: layout_name.to_owned(),
                compiled: compiled.layers.len(),
                canonical: dag.layers.len(),
            });
        }

        let circuit = circuit_name(layout_name);
        for layer in compiled.layers {
            let canonical =
                dag.layers
                    .get(layer.layer)
                    .ok_or_else(|| R0CorpusError::CanonicalDag {
                        coordinate: coordinate_name(&circuit, layer.layer),
                        error: "compiled layer is outside the canonical DAG".to_owned(),
                    })?;
            let canonical_lookup_value_nodes =
                reachable_lookup_value_nodes(canonical).map_err(|error| {
                    R0CorpusError::CanonicalDag {
                        coordinate: coordinate_name(&circuit, layer.layer),
                        error,
                    }
                })?;
            let materialized_root_sinks = u32_len(
                canonical
                    .roots
                    .iter()
                    .filter(|root| root.claim.is_some() && root.materialize.is_some())
                    .count(),
            )?;
            let (coordinate, field_class_bf_atoms, field_class_e4_atoms) =
                frozen_coordinate(&circuit, artifact.trace_len as u64, &layer)?;
            built_coordinates.push(BuiltCoordinate {
                coordinate,
                canonical_lookup_value_nodes,
                materialized_root_sinks,
                field_class_bf_atoms,
                field_class_e4_atoms,
            });
        }
    }

    built_coordinates.sort_by(|left, right| {
        (&left.coordinate.circuit, left.coordinate.layer)
            .cmp(&(&right.coordinate.circuit, right.coordinate.layer))
    });
    let mut coordinates = Vec::with_capacity(built_coordinates.len());
    let mut previous = None;
    for row in &built_coordinates {
        let key = (row.coordinate.circuit.as_str(), row.coordinate.layer);
        if previous == Some(key) {
            return Err(R0CorpusError::DuplicateCoordinate {
                coordinate: coordinate_name(key.0, key.1 as usize),
            });
        }
        previous = Some(key);
        coordinates.push(row.coordinate.clone());
    }
    if coordinates.len() != 57 {
        return Err(R0CorpusError::CanonicalDag {
            coordinate: "corpus".to_owned(),
            error: format!("expected 57 R0 coordinates, found {}", coordinates.len()),
        });
    }

    let bundle = FrozenR0BundleV1 {
        magic: R0_BUNDLE_MAGIC,
        version: R0_BUNDLE_VERSION,
        layout_hashes,
        coordinates,
    };
    let bytes = encode_r0_bundle(&bundle)?;
    let inspected = inspect_r0_bundle(&bytes)?;
    if inspected.bundle != bundle || inspected.offsets.len() != built_coordinates.len() {
        return Err(R0CorpusError::CoordinateOffsetMismatch {
            coordinate: "bundle".to_owned(),
        });
    }

    let mut manifest_coordinates = Vec::with_capacity(bundle.coordinates.len());
    for (row, offsets) in built_coordinates.iter().zip(&inspected.offsets) {
        let coordinate = &row.coordinate;
        if coordinate.circuit != offsets.circuit || coordinate.layer != offsets.layer {
            return Err(R0CorpusError::CoordinateOffsetMismatch {
                coordinate: coordinate_name(&coordinate.circuit, coordinate.layer as usize),
            });
        }
        let coordinate_name = coordinate_name(&coordinate.circuit, coordinate.layer as usize);
        manifest_coordinates.push(R0ManifestCoordinateV1 {
            circuit: coordinate.circuit.clone(),
            layer: coordinate.layer,
            trace_len: coordinate.trace_len,
            passes_per_invocation: coordinate.passes_per_invocation,
            canonical_lookup_value_nodes: row.canonical_lookup_value_nodes,
            materialized_root_sinks: row.materialized_root_sinks,
            shape: coordinate.shape.clone(),
            offsets: offsets.clone(),
            program_sha256: sha256(section_bytes(&bytes, offsets, "program", &coordinate_name)?)?,
            binding_sha256: sha256(section_bytes(&bytes, offsets, "binding", &coordinate_name)?)?,
            recipes_sha256: sha256(section_bytes(&bytes, offsets, "recipes", &coordinate_name)?)?,
            payload_sha256: coordinate.payload_sha256.clone(),
        });
    }

    let mut layer_counts = BTreeMap::<String, u32>::new();
    for coordinate in &bundle.coordinates {
        *layer_counts.entry(coordinate.circuit.clone()).or_default() += 1;
    }
    let circuit_layer_counts = layer_counts
        .into_iter()
        .map(|(circuit, layers)| R0CircuitCountV1 { circuit, layers })
        .collect::<Vec<_>>();
    let manifest = R0ManifestV1 {
        schema_version: R0_CORPUS_SCHEMA_VERSION,
        bundle_sha256: sha256(&bytes)?,
        layout_hashes: bundle.layout_hashes.clone(),
        declared: declared_capacity()?,
        circuit_layer_counts,
        coordinates: manifest_coordinates,
        max_records: bundle
            .coordinates
            .iter()
            .map(|coordinate| coordinate.shape.records)
            .max()
            .unwrap_or(0),
        max_projections: bundle
            .coordinates
            .iter()
            .map(|coordinate| coordinate.shape.projections)
            .max()
            .unwrap_or(0),
        max_bf_atoms: built_coordinates
            .iter()
            .map(|coordinate| coordinate.field_class_bf_atoms)
            .max()
            .unwrap_or(0),
        max_e4_atoms: built_coordinates
            .iter()
            .map(|coordinate| coordinate.field_class_e4_atoms)
            .max()
            .unwrap_or(0),
        max_sources: bundle
            .coordinates
            .iter()
            .map(|coordinate| coordinate.shape.unique_sources)
            .max()
            .unwrap_or(0),
        max_windows: bundle
            .coordinates
            .iter()
            .map(|coordinate| coordinate.shape.windows)
            .max()
            .unwrap_or(0),
        max_relative_column: bundle
            .coordinates
            .iter()
            .map(|coordinate| coordinate.shape.max_relative_column)
            .max()
            .unwrap_or(0),
    };
    Ok((bundle, manifest))
}

pub fn r0_manifest_json(manifest: &R0ManifestV1) -> Result<Vec<u8>, R0CorpusError> {
    let mut bytes =
        serde_json::to_vec(manifest).map_err(|error| R0CorpusError::Hash(error.to_string()))?;
    bytes.push(b'\n');
    Ok(bytes)
}

fn frozen_coordinate(
    circuit: &str,
    trace_len: u64,
    layer: &gpu_gkr_compiler::R0LayerProgram,
) -> Result<(FrozenR0Coordinate, u32, u32), R0CorpusError> {
    let coordinate_name = coordinate_name(circuit, layer.layer);
    if layer.coefficients.c_init.is_some() {
        return Err(R0CorpusError::CInitPresent {
            coordinate: coordinate_name,
        });
    }
    let atoms =
        decode_r0_program(&layer.program).map_err(|error| R0CorpusError::DecodeProgram {
            coordinate: coordinate_name.clone(),
            error: format!("{error:?}"),
        })?;
    let (field_class_bf_atoms, field_class_e4_atoms) =
        field_class_counts(&coordinate_name, &atoms)?;
    let mut program_words = Vec::with_capacity(atoms.len() * R0_RECORD_WORDS);
    for atom in &atoms {
        let LeanAtom::Term(term) = atom else {
            return Err(R0CorpusError::GroupHeader {
                coordinate: coordinate_name.clone(),
            });
        };
        program_words.extend_from_slice(&[
            (u16::from(term.class) << 13) | term.coeff,
            term.source_a,
            term.source_b,
            0,
        ]);
    }
    let shape = frozen_shape(
        &coordinate_name,
        &atoms,
        &layer.binding,
        layer.coefficients.coefficients.len(),
        layer.coefficients.immediates.len(),
    )?;
    let recipes = layer
        .coefficients
        .coefficients
        .iter()
        .map(|recipe| FrozenR0Recipe {
            products: recipe
                .terms
                .iter()
                .map(|product| FrozenR0Product {
                    scalar: product.scalar,
                    challenges: product
                        .challenges
                        .iter()
                        .map(|challenge| FrozenR0Challenge {
                            reference: challenge.0.clone(),
                        })
                        .collect(),
                    inits_and_teardowns_top_bits: product.inits_and_teardowns_top_bits.clone(),
                })
                .collect(),
        })
        .collect();
    let mut coordinate = FrozenR0Coordinate {
        circuit: circuit.to_owned(),
        layer: u32_len(layer.layer)?,
        trace_len,
        passes_per_invocation: 1,
        program_words,
        term_count: u32_len(atoms.len())?,
        binding: layer.binding.clone(),
        recipes,
        immediates: layer.coefficients.immediates.clone(),
        c_init: None,
        shape,
        payload_sha256: "0".repeat(64),
    };
    coordinate.payload_sha256 = r0_coordinate_payload_sha256(&coordinate)?;
    Ok((coordinate, field_class_bf_atoms, field_class_e4_atoms))
}

fn field_class_counts(coordinate: &str, atoms: &[LeanAtom]) -> Result<(u32, u32), R0CorpusError> {
    let mut bf_atoms = 0usize;
    let mut e4_atoms = 0usize;
    for atom in atoms {
        let LeanAtom::Term(term) = atom else {
            return Err(R0CorpusError::GroupHeader {
                coordinate: coordinate.to_owned(),
            });
        };
        match term.class {
            0 | 2 => bf_atoms += 1,
            1 | 3 | 4 => e4_atoms += 1,
            class => {
                return Err(R0CorpusError::ClassAboveR0 {
                    coordinate: coordinate.to_owned(),
                    class,
                });
            }
        }
    }
    Ok((u32_len(bf_atoms)?, u32_len(e4_atoms)?))
}

fn frozen_shape(
    coordinate: &str,
    atoms: &[LeanAtom],
    binding: &gpu_gkr_compiler::backward::LeanSourceBinding,
    recipe_count: usize,
    immediate_count: usize,
) -> Result<FrozenR0Shape, R0CorpusError> {
    let mut projections = BTreeSet::new();
    let mut bf_atoms = 0usize;
    let mut e4_atoms = 0usize;
    let mut source_uses = 0usize;
    for atom in atoms {
        let LeanAtom::Term(term) = atom else {
            return Err(R0CorpusError::GroupHeader {
                coordinate: coordinate.to_owned(),
            });
        };
        let (bf, e4, role) = match term.class {
            0 => (1, 0, 0),
            1 => (0, 1, 0),
            2 => (2, 0, 1),
            3 => (1, 1, 1),
            4 => (0, 2, 1),
            class => {
                return Err(R0CorpusError::ClassAboveR0 {
                    coordinate: coordinate.to_owned(),
                    class,
                });
            }
        };
        bf_atoms += bf;
        e4_atoms += e4;
        for source in [term.source_a, term.source_b] {
            if source == SOURCE_NONE {
                continue;
            }
            if usize::from(source) >= binding.source_slots.len() {
                return Err(R0CorpusError::CanonicalDag {
                    coordinate: coordinate.to_owned(),
                    error: format!("decoded source slot {source} is outside the binding"),
                });
            }
            source_uses += 1;
            projections.insert((source, role));
        }
    }
    check_capacity(coordinate, "records", atoms.len(), R0_DECLARED_RECORDS)?;
    check_capacity(
        coordinate,
        "program_words",
        atoms.len() * R0_RECORD_WORDS,
        R0_DECLARED_PROGRAM_WORDS,
    )?;
    check_capacity(
        coordinate,
        "projections",
        projections.len(),
        R0_DECLARED_PROJECTIONS,
    )?;
    check_capacity(
        coordinate,
        "coefficient_recipes",
        recipe_count,
        R0_DECLARED_COEFFICIENTS,
    )?;
    check_capacity(
        coordinate,
        "immediates",
        immediate_count,
        LEAN_MAX_IMMEDIATES,
    )?;
    check_capacity(
        coordinate,
        "sources",
        binding.source_slots.len(),
        R0_DECLARED_SOURCES,
    )?;
    check_capacity(
        coordinate,
        "windows",
        binding.windows.len(),
        R0_DECLARED_WINDOWS,
    )?;
    let max_relative_column = binding
        .source_slots
        .iter()
        .map(|slot| slot.column)
        .max()
        .unwrap_or(0);
    if max_relative_column >= 128 {
        return Err(R0CorpusError::CapacityOverflow {
            coordinate: coordinate.to_owned(),
            resource: "max_relative_column",
            required: usize::from(max_relative_column),
            declared: 127,
        });
    }
    Ok(FrozenR0Shape {
        records: u32_len(atoms.len())?,
        projections: u32_len(projections.len())?,
        bf_atoms: u32_len(bf_atoms)?,
        e4_atoms: u32_len(e4_atoms)?,
        source_uses: u32_len(source_uses)?,
        unique_sources: u32_len(binding.source_slots.len())?,
        windows: u16_len(binding.windows.len())?,
        max_relative_column,
        coefficient_recipes: u32_len(recipe_count)?,
        immediates: u32_len(immediate_count)?,
    })
}

fn reachable_lookup_value_nodes(layer: &DagLayer) -> Result<u32, String> {
    let mut visited = BTreeSet::<u32>::new();
    let mut lookup_sources = BTreeSet::new();
    let mut stack = layer.roots.iter().map(|root| root.expr).collect::<Vec<_>>();
    while let Some(expr_id) = stack.pop() {
        if !visited.insert(expr_id.0) {
            continue;
        }
        let expr = layer
            .exprs
            .get(expr_id.0 as usize)
            .ok_or_else(|| format!("root-reachable expression {} is missing", expr_id.0))?;
        match expr {
            Expr::Source(source_id) => {
                let source = layer
                    .sources
                    .get(source_id.0 as usize)
                    .ok_or_else(|| format!("root-reachable source {} is missing", source_id.0))?;
                if let SourceKind::LookupValue { query, .. } = source {
                    lookup_sources.insert(source_id.0);
                    stack.push(*query);
                }
            }
            Expr::Add(children) | Expr::Mul(children) => stack.extend(children.iter().copied()),
        }
    }
    u32::try_from(lookup_sources.len()).map_err(|_| "lookup count exceeds u32".to_owned())
}

fn declared_capacity() -> Result<R0DeclaredCapacityV1, R0CorpusError> {
    Ok(R0DeclaredCapacityV1 {
        records: u32_len(R0_DECLARED_RECORDS)?,
        program_words: u32_len(R0_DECLARED_PROGRAM_WORDS)?,
        program_bytes: u32_len(
            R0_DECLARED_PROGRAM_WORDS
                .checked_mul(2)
                .ok_or(R0CorpusError::LengthOverflow)?,
        )?,
        projections: u32_len(R0_DECLARED_PROJECTIONS)?,
        coefficient_recipes: u32_len(R0_DECLARED_COEFFICIENTS)?,
        immediates: u32_len(LEAN_MAX_IMMEDIATES)?,
        sources: u32_len(R0_DECLARED_SOURCES)?,
        windows: u32_len(R0_DECLARED_WINDOWS)?,
        columns_per_window: 128,
    })
}

fn section_bytes<'a>(
    bytes: &'a [u8],
    offsets: &R0CoordinateOffsets,
    section: &'static str,
    coordinate: &str,
) -> Result<&'a [u8], R0CorpusError> {
    let (offset, len) = match section {
        "program" => (offsets.program_offset, offsets.program_len),
        "binding" => (offsets.binding_offset, offsets.binding_len),
        "recipes" => (offsets.recipes_offset, offsets.recipes_len),
        _ => unreachable!("only manifest sections are requested"),
    };
    let start = usize::try_from(offset).map_err(|_| R0CorpusError::OffsetRange {
        coordinate: coordinate.to_owned(),
        section,
    })?;
    let len = usize::try_from(len).map_err(|_| R0CorpusError::OffsetRange {
        coordinate: coordinate.to_owned(),
        section,
    })?;
    let end = start
        .checked_add(len)
        .ok_or_else(|| R0CorpusError::OffsetRange {
            coordinate: coordinate.to_owned(),
            section,
        })?;
    bytes
        .get(start..end)
        .ok_or_else(|| R0CorpusError::OffsetRange {
            coordinate: coordinate.to_owned(),
            section,
        })
}

fn check_capacity(
    coordinate: &str,
    resource: &'static str,
    required: usize,
    declared: usize,
) -> Result<(), R0CorpusError> {
    if required > declared {
        return Err(R0CorpusError::CapacityOverflow {
            coordinate: coordinate.to_owned(),
            resource,
            required,
            declared,
        });
    }
    Ok(())
}

fn corpus_directory() -> PathBuf {
    crate::runtime_paths::compiled_circuits_directory()
}

fn circuit_name(layout: &str) -> String {
    layout
        .strip_suffix("_layout_gkr.json")
        .unwrap_or(layout)
        .to_owned()
}

fn coordinate_name(circuit: &str, layer: usize) -> String {
    format!("{circuit}:{layer}")
}

fn expected_layout_hash(layout: &str) -> Option<&'static str> {
    EXPECTED_LAYOUT_HASHES
        .iter()
        .find_map(|(name, hash)| (*name == layout).then_some(*hash))
}

fn sha256(bytes: &[u8]) -> Result<String, R0CorpusError> {
    let mut child = Command::new("sha256sum")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .map_err(|error| R0CorpusError::Hash(format!("run sha256sum: {error}")))?;
    child
        .stdin
        .as_mut()
        .ok_or_else(|| R0CorpusError::Hash("open sha256sum stdin".to_owned()))?
        .write_all(bytes)
        .map_err(|error| R0CorpusError::Hash(format!("write sha256sum stdin: {error}")))?;
    let output = child
        .wait_with_output()
        .map_err(|error| R0CorpusError::Hash(format!("wait for sha256sum: {error}")))?;
    if !output.status.success() {
        return Err(R0CorpusError::Hash("sha256sum failed".to_owned()));
    }
    let value = String::from_utf8(output.stdout)
        .map_err(|_| R0CorpusError::Hash("sha256sum output was not UTF-8".to_owned()))?;
    let hash = value.split_whitespace().next().unwrap_or_default();
    if hash.len() != 64
        || !hash
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err(R0CorpusError::Hash(
            "sha256sum output was not lowercase SHA-256".to_owned(),
        ));
    }
    Ok(hash.to_owned())
}

fn u32_len(value: usize) -> Result<u32, R0CorpusError> {
    u32::try_from(value).map_err(|_| R0CorpusError::LengthOverflow)
}

fn u16_len(value: usize) -> Result<u16, R0CorpusError> {
    u16::try_from(value).map_err(|_| R0CorpusError::LengthOverflow)
}

#[cfg(test)]
mod tests {
    use gpu_gkr_compiler::backward::{decode_r0_program, LeanAtom, LeanProgram};

    use crate::r0_artifact::{
        encode_r0_bundle, R0_CORPUS_BYTES, R0_DECLARED_PROGRAM_WORDS, R0_DECLARED_SOURCES,
        R0_DECLARED_WINDOWS, R0_RECORD_WORDS,
    };

    use super::*;

    fn expected_named_circuit_layer_counts() -> Vec<R0CircuitCountV1> {
        [
            ("add_sub_lui_auipc_mop", 4),
            ("bigint_with_extended_control", 6),
            ("blake2_g_function", 5),
            ("blake2_with_extended_control", 8),
            ("inits_and_teardowns", 4),
            ("jump_branch_slt", 4),
            ("keccak_special5", 6),
            ("mem_subword_only", 4),
            ("mem_word_only", 4),
            ("shift_binop", 4),
            ("unified_reduced_machine", 4),
            ("unsigned_mul_div", 4),
        ]
        .into_iter()
        .map(|(circuit, layers)| R0CircuitCountV1 {
            circuit: circuit.to_owned(),
            layers,
        })
        .collect()
    }

    #[test]
    fn cpu_r0_corpus_has_exact_identities_and_measured_extrema() {
        let (bundle, manifest) = generate_r0_bundle().unwrap();
        assert_eq!(bundle.coordinates.len(), 57);
        assert_eq!(
            manifest.circuit_layer_counts,
            expected_named_circuit_layer_counts(),
        );
        assert_eq!(manifest.max_records, 1_632);
        assert_eq!(manifest.max_bf_atoms, 1_442);
        assert_eq!(manifest.max_e4_atoms, 490);
        assert_eq!(manifest.max_sources, 1_062);
        assert_eq!(manifest.max_windows, 17);
        assert_eq!(manifest.max_relative_column, 127);
        assert!(bundle
            .coordinates
            .iter()
            .all(|row| row.passes_per_invocation == 1));
        assert!(bundle.coordinates.iter().all(|row| row.c_init.is_none()));
        assert!(manifest.max_projections <= manifest.declared.projections);
    }

    #[test]
    fn cpu_r0_corpus_is_true_r0_and_fits_declared_capacity() {
        let (bundle, _) = generate_r0_bundle().unwrap();
        for row in &bundle.coordinates {
            assert_eq!(
                row.program_words.len(),
                row.term_count as usize * R0_RECORD_WORDS
            );
            assert!(row.program_words.len() <= R0_DECLARED_PROGRAM_WORDS);
            assert!(row.binding.windows.len() <= R0_DECLARED_WINDOWS);
            assert!(row.binding.source_slots.len() <= R0_DECLARED_SOURCES);
            assert!(row
                .program_words
                .chunks_exact(R0_RECORD_WORDS)
                .all(|record| record[0] >> 13 <= 4 && record[3] == 0));
        }
    }

    #[test]
    fn cpu_r0_checked_manifest_pins_every_coordinate_shape() {
        let (bundle, regenerated) = generate_r0_bundle().unwrap();
        let checked: R0ManifestV1 =
            serde_json::from_str(include_str!("../artifacts/windowed_r0_corpus_v1.json")).unwrap();
        assert_eq!(checked, regenerated);
        assert_eq!(R0_CORPUS_BYTES, encode_r0_bundle(&bundle).unwrap());
    }
}
