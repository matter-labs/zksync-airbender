use std::path::Path;

use cs::gkr_compiler::GKRCircuitArtifact;
use field::baby_bear::base::BabyBearField;
use gkr_eval_ir::FieldKind;
use gpu_gkr_compiler::backward::{
    decode_continuation_program, LeanAtom, LeanSourceBinding, LeanTerm, WindowFamily,
};
use gpu_gkr_compiler::{compile_continuations, GpuResourceProfile};

use crate::abi::WindowInstruction;
use crate::artifact::{
    decode_program, decode_source_coordinate, encode_artifact, encode_source_coordinate,
    validate_artifact, ArtifactError, FrozenArtifact, FrozenBoundColumn, FrozenField,
    FrozenSourceSlot, FrozenWindow, FrozenWindowFamily, WindowAtom, WindowClass, WindowTerm,
    ARTIFACT_MAGIC, ARTIFACT_VERSION, GROUP_HAS_PRODUCT, IMMEDIATE_ID_MASK, REDUCE_AFTER,
    SOURCE_NONE,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GeneratorError(String);

impl GeneratorError {
    fn context(context: &str, error: impl core::fmt::Display) -> Self {
        Self(format!("{context}: {error}"))
    }
}

impl core::fmt::Display for GeneratorError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter.write_str(&self.0)
    }
}

impl std::error::Error for GeneratorError {}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum ProgramSchedule {
    #[default]
    Compiler,
    ControlAtoms,
    Control,
    Source,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ScheduleCensus {
    pub atoms: u32,
    pub terms: u32,
    pub bf_atoms: u32,
    pub e4_atoms: u32,
    pub field_transitions: u32,
    pub shape_transitions_within_field: u32,
    pub class_transitions: u32,
    pub group_immediate_transitions: u32,
    pub adjacent_equal_source_a: u32,
    pub adjacent_equal_source_b: u32,
    pub projected_bf_accesses: u64,
    pub projected_procedural_bf_accesses: u64,
    pub lazy_bf_groups: u32,
    pub lazy_bf_products: u32,
    pub reduction_boundaries: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum EncodedAtom {
    Term(WindowInstruction),
    Group {
        class: WindowClass,
        core: u16,
        lazy_product_count: u16,
        members: Vec<WindowInstruction>,
    },
}

impl EncodedAtom {
    fn members(&self) -> &[WindowInstruction] {
        match self {
            Self::Term(term) => core::slice::from_ref(term),
            Self::Group { members, .. } => members,
        }
    }

    fn field(&self) -> u16 {
        self.members()[0].term_class & 1
    }

    fn shape(&self) -> u8 {
        matches!(self, Self::Group { .. }) as u8
    }

    fn core(&self) -> u16 {
        match self {
            Self::Term(term) => term.factor,
            Self::Group { core, .. } => *core,
        }
    }

    fn class_sequence(&self) -> Vec<u16> {
        self.members()
            .iter()
            .map(|member| member.term_class)
            .collect()
    }

    fn source_sequence(&self) -> Vec<(u16, u16)> {
        self.members()
            .iter()
            .map(|member| (member.source_a, member.source_b))
            .collect()
    }

    fn procedural(&self) -> bool {
        self.members().iter().any(|member| {
            matches!(
                record_class(member),
                WindowClass::LinearBfProceduralA | WindowClass::ProductBfBfProceduralB
            )
        })
    }

    fn sort_members_control(&mut self) {
        if let Self::Group { members, .. } = self {
            members.sort_unstable_by_key(|member| {
                (
                    member.term_class,
                    immediate_kind(member.factor),
                    member.source_a,
                    member.source_b,
                    member.factor,
                )
            });
        }
    }

    fn sort_members_source(&mut self) {
        if let Self::Group { members, .. } = self {
            members.sort_unstable_by_key(|member| {
                (
                    member.source_a,
                    member.source_b,
                    member.term_class,
                    immediate_kind(member.factor),
                    member.factor,
                )
            });
        }
    }

    fn prepare_lazy_bf_reduction(&mut self) {
        let Self::Group {
            class,
            lazy_product_count,
            members,
            ..
        } = self
        else {
            return;
        };
        if *class != WindowClass::GroupBf {
            return;
        }
        members.sort_unstable_by_key(|member| {
            (
                match record_class(member) {
                    WindowClass::ProductBfBf => 0,
                    WindowClass::LinearBf => 1,
                    _ => 2,
                },
                immediate_kind(member.factor),
                member.source_a,
                member.source_b,
                member.factor,
            )
        });
        let product_count = members
            .iter()
            .take_while(|member| record_class(member) == WindowClass::ProductBfBf)
            .count();
        if product_count == 0 {
            return;
        }
        *lazy_product_count =
            u16::try_from(product_count).expect("validated BF group arity fits in u16");
        if product_count == 1 {
            return;
        }
        for (product, member) in members[..product_count].iter_mut().enumerate() {
            member.factor &= IMMEDIATE_ID_MASK;
            if (product + 1) % 4 == 0 || product + 1 == product_count {
                member.factor |= REDUCE_AFTER;
            }
        }
    }

    fn append_to(self, program: &mut Vec<WindowInstruction>) {
        match self {
            Self::Term(term) => program.push(term),
            Self::Group {
                class,
                core,
                lazy_product_count,
                members,
            } => {
                let encoded_count = if class == WindowClass::GroupBf {
                    u16::try_from(members.len()).expect("validated BF group arity fits in u16")
                } else {
                    0
                };
                let has_product = members.iter().any(|member| match class {
                    WindowClass::GroupBf => record_class(member) == WindowClass::ProductBfBf,
                    WindowClass::GroupE4 => matches!(
                        record_class(member),
                        WindowClass::ProductBfE4 | WindowClass::ProductE4E4
                    ),
                    _ => unreachable!("encoded group must have a group class"),
                });
                let header_source_b =
                    lazy_product_count | if has_product { GROUP_HAS_PRODUCT } else { 0 };
                program.push(WindowInstruction {
                    term_class: class as u16,
                    factor: core,
                    source_a: encoded_count,
                    source_b: header_source_b,
                });
                program.extend(members);
            }
        }
    }
}

fn immediate_kind(factor: u16) -> u8 {
    match factor {
        0 => 0,
        1 => 1,
        _ => 2,
    }
}

fn apply_schedule(atoms: &mut [EncodedAtom], schedule: ProgramSchedule) {
    match schedule {
        ProgramSchedule::Compiler => {}
        ProgramSchedule::ControlAtoms => atoms.sort_unstable_by_key(|atom| {
            (
                atom.field(),
                atom.shape(),
                atom.class_sequence(),
                atom.source_sequence(),
                atom.members().len(),
                atom.core(),
            )
        }),
        ProgramSchedule::Control => {
            atoms.iter_mut().for_each(EncodedAtom::sort_members_control);
            atoms.sort_unstable_by_key(|atom| {
                (
                    atom.field(),
                    atom.shape(),
                    atom.class_sequence(),
                    atom.source_sequence(),
                    atom.members().len(),
                    atom.core(),
                )
            });
        }
        ProgramSchedule::Source => {
            atoms.iter_mut().for_each(EncodedAtom::sort_members_source);
            atoms.sort_unstable_by_key(|atom| {
                (
                    atom.field(),
                    atom.procedural(),
                    atom.source_sequence(),
                    atom.shape(),
                    atom.class_sequence(),
                    atom.members().len(),
                    atom.core(),
                )
            });
        }
    }
}

fn term_field(class: WindowClass) -> u8 {
    match class {
        WindowClass::LinearBf
        | WindowClass::ProductBfBf
        | WindowClass::LinearBfProceduralA
        | WindowClass::ProductBfBfProceduralB => 0,
        WindowClass::LinearE4 | WindowClass::ProductBfE4 | WindowClass::ProductE4E4 => 1,
        WindowClass::GroupBf | WindowClass::GroupE4 => {
            unreachable!("decoded atoms never contain group headers as terms")
        }
    }
}

fn atom_terms(atom: &WindowAtom) -> &[WindowTerm] {
    match atom {
        WindowAtom::Term(term) => core::slice::from_ref(term),
        WindowAtom::GroupBf { members, .. } | WindowAtom::GroupE4 { members, .. } => members,
    }
}

fn atom_shape(atom: &WindowAtom) -> u8 {
    matches!(
        atom,
        WindowAtom::GroupBf { .. } | WindowAtom::GroupE4 { .. }
    ) as u8
}

fn transitions<T: PartialEq>(values: impl IntoIterator<Item = T>) -> u32 {
    let mut values = values.into_iter();
    let Some(mut previous) = values.next() else {
        return 0;
    };
    values.fold(0, |count, value| {
        let changed = value != previous;
        previous = value;
        count + u32::from(changed)
    })
}

fn source_is_procedural(artifact: &FrozenArtifact, source: u16) -> bool {
    let (window, _) = decode_source_coordinate(source)
        .expect("validated term source must contain a direct coordinate");
    artifact.windows[usize::from(window)].family.is_procedural()
}

fn bf_source_accesses(term: &WindowTerm) -> [(u16, u64, bool); 2] {
    match term.class {
        WindowClass::LinearBf => [(term.source_a, 8, false), (SOURCE_NONE, 0, false)],
        WindowClass::LinearBfProceduralA => [(term.source_a, 8, true), (SOURCE_NONE, 0, false)],
        WindowClass::ProductBfBf => [(term.source_a, 32, false), (term.source_b, 32, false)],
        WindowClass::ProductBfBfProceduralB => {
            [(term.source_a, 32, false), (term.source_b, 32, true)]
        }
        WindowClass::ProductBfE4 => [(term.source_a, 32, false), (SOURCE_NONE, 0, false)],
        WindowClass::LinearE4 | WindowClass::ProductE4E4 => {
            [(SOURCE_NONE, 0, false), (SOURCE_NONE, 0, false)]
        }
        WindowClass::GroupBf | WindowClass::GroupE4 => {
            unreachable!("decoded atoms never contain group headers as terms")
        }
    }
}

pub fn schedule_census(artifact: &FrozenArtifact) -> Result<ScheduleCensus, ArtifactError> {
    let (atoms, stats) = decode_program(artifact)?;
    let flattened = atoms
        .iter()
        .flat_map(atom_terms)
        .collect::<Vec<&WindowTerm>>();
    let fields = atoms
        .iter()
        .map(|atom| term_field(atom_terms(atom)[0].class))
        .collect::<Vec<_>>();
    let field_transitions = transitions(fields.iter().copied());
    let shape_transitions_within_field = atoms
        .windows(2)
        .filter(|pair| {
            let left_field = term_field(atom_terms(&pair[0])[0].class);
            let right_field = term_field(atom_terms(&pair[1])[0].class);
            left_field == right_field && atom_shape(&pair[0]) != atom_shape(&pair[1])
        })
        .count() as u32;
    let class_transitions = transitions(flattened.iter().map(|term| term.class as u8));
    let group_immediate_transitions = transitions(
        atoms
            .iter()
            .flat_map(|atom| match atom {
                WindowAtom::Term(_) => &[][..],
                WindowAtom::GroupBf { members, .. } | WindowAtom::GroupE4 { members, .. } => {
                    members.as_slice()
                }
            })
            .map(|term| immediate_kind(term.coefficient)),
    );
    let adjacent_equal_source_a = flattened
        .windows(2)
        .filter(|pair| pair[0].source_a == pair[1].source_a)
        .count() as u32;
    let adjacent_equal_source_b = flattened
        .windows(2)
        .filter(|pair| {
            pair[0].source_b != SOURCE_NONE
                && pair[1].source_b != SOURCE_NONE
                && pair[0].source_b == pair[1].source_b
        })
        .count() as u32;
    let (projected_bf_accesses, projected_procedural_bf_accesses) = flattened
        .iter()
        .flat_map(|term| bf_source_accesses(term))
        .filter(|(_, accesses, _)| *accesses != 0)
        .fold(
            (0, 0),
            |(total, procedural), (source, accesses, generated)| {
                (
                    total + accesses,
                    procedural
                        + if generated || source_is_procedural(artifact, source) {
                            accesses
                        } else {
                            0
                        },
                )
            },
        );
    let (lazy_bf_groups, lazy_bf_products) =
        atoms
            .iter()
            .fold((0u32, 0u32), |(groups, products), atom| match atom {
                WindowAtom::GroupBf {
                    lazy_product_count, ..
                } if *lazy_product_count != 0 => {
                    (groups + 1, products + u32::from(*lazy_product_count))
                }
                _ => (groups, products),
            });
    let reduction_boundaries = artifact
        .program
        .iter()
        .filter(|instruction| instruction.factor & REDUCE_AFTER != 0)
        .count() as u32;
    let bf_atoms = fields.iter().filter(|field| **field == 0).count() as u32;
    Ok(ScheduleCensus {
        atoms: atoms.len() as u32,
        terms: stats.terms,
        bf_atoms,
        e4_atoms: atoms.len() as u32 - bf_atoms,
        field_transitions,
        shape_transitions_within_field,
        class_transitions,
        group_immediate_transitions,
        adjacent_equal_source_a,
        adjacent_equal_source_b,
        projected_bf_accesses,
        projected_procedural_bf_accesses,
        lazy_bf_groups,
        lazy_bf_products,
        reduction_boundaries,
    })
}

pub fn generate_add_sub_layer0(layout_path: &Path) -> Result<FrozenArtifact, GeneratorError> {
    generate_add_sub_layer0_with_schedule(layout_path, ProgramSchedule::Compiler)
}

pub fn generate_add_sub_layer0_with_schedule(
    layout_path: &Path,
    schedule: ProgramSchedule,
) -> Result<FrozenArtifact, GeneratorError> {
    generate_add_sub_layer0_with_options(layout_path, schedule, false)
}

pub fn generate_add_sub_layer0_with_options(
    layout_path: &Path,
    schedule: ProgramSchedule,
    lazy_bf_reduction: bool,
) -> Result<FrozenArtifact, GeneratorError> {
    let bytes = std::fs::read(layout_path)
        .map_err(|error| GeneratorError::context("read circuit layout", error))?;
    let circuit: GKRCircuitArtifact<BabyBearField> = serde_json::from_slice(&bytes)
        .map_err(|error| GeneratorError::context("parse circuit layout", error))?;
    let dag = gkr_eval_ir::lower_dag(&circuit)
        .map_err(|error| GeneratorError::context("lower circuit DAG", error))?;
    gkr_eval_ir::validate(&dag)
        .map_err(|error| GeneratorError::context("validate circuit DAG", error))?;
    let bundle = compile_continuations(&dag, &GpuResourceProfile::production())
        .map_err(|error| GeneratorError::context("compile full continuation relation", error))?;
    let layer = bundle
        .layers
        .into_iter()
        .find(|layer| layer.layer == 0)
        .ok_or_else(|| GeneratorError("compiled program has no layer 0".to_owned()))?;
    let atoms = decode_continuation_program(&layer.program)
        .map_err(|error| GeneratorError(format!("decode continuation program: {error:?}")))?;

    let mut encoded_atoms = atoms
        .into_iter()
        .map(|atom| match atom {
            LeanAtom::Term(term) => Ok(EncodedAtom::Term(encode_term(&term, &layer.binding)?)),
            LeanAtom::Group {
                core,
                has_c0: _,
                has_c2: _,
                members,
            } => {
                let member_count = u16::try_from(members.len())
                    .map_err(|error| GeneratorError::context("group member count", error))?;
                let encoded_members = members
                    .iter()
                    .map(|member| encode_term(member, &layer.binding))
                    .collect::<Result<Vec<_>, GeneratorError>>()?;
                let all_bf = encoded_members.iter().all(|record| {
                    matches!(
                        record_class(record),
                        WindowClass::LinearBf | WindowClass::ProductBfBf
                    )
                });
                let all_e4 = encoded_members.iter().all(|record| {
                    matches!(
                        record_class(record),
                        WindowClass::LinearE4 | WindowClass::ProductBfE4 | WindowClass::ProductE4E4
                    )
                });
                let group_class = if all_bf && member_count >= 2 {
                    WindowClass::GroupBf
                } else if all_e4
                    && member_count == 2
                    && encoded_members.iter().all(|record| record.factor < 2)
                {
                    WindowClass::GroupE4
                } else {
                    return Err(GeneratorError(format!(
                        "unsupported round-0 group: members={} all_bf={all_bf} all_e4={all_e4}",
                        members.len()
                    )));
                };
                Ok(EncodedAtom::Group {
                    class: group_class,
                    core,
                    lazy_product_count: 0,
                    members: encoded_members,
                })
            }
        })
        .collect::<Result<Vec<_>, GeneratorError>>()?;
    apply_schedule(&mut encoded_atoms, schedule);
    if lazy_bf_reduction {
        encoded_atoms
            .iter_mut()
            .for_each(EncodedAtom::prepare_lazy_bf_reduction);
    }
    let mut program = Vec::with_capacity(layer.program.words.len() / 4);
    encoded_atoms
        .into_iter()
        .for_each(|atom| atom.append_to(&mut program));

    let windows = layer
        .binding
        .windows
        .iter()
        .map(|window| {
            let first_column = u32::try_from(window.first_column)
                .map_err(|error| GeneratorError::context("window first column", error))?;
            let field = match window.backing_field() {
                FieldKind::Base => FrozenField::Base,
                FieldKind::Ext => FrozenField::Ext,
            };
            let columns = window
                .columns
                .iter()
                .map(|column| {
                    Ok(FrozenBoundColumn {
                        column: u32::try_from(column.column).map_err(|error| {
                            GeneratorError::context("bound source column", error)
                        })?,
                        source: column.source,
                    })
                })
                .collect::<Result<Vec<_>, GeneratorError>>()?;
            Ok(FrozenWindow {
                family: convert_family(window.family)?,
                first_column,
                field,
                columns,
            })
        })
        .collect::<Result<Vec<_>, GeneratorError>>()?;
    let source_slots = layer
        .binding
        .source_slots
        .iter()
        .map(|slot| FrozenSourceSlot {
            window: slot.window,
            column: slot.column,
        })
        .collect();
    let coefficient_count = u32::try_from(layer.coefficients.coefficients.len())
        .map_err(|error| GeneratorError::context("coefficient count", error))?
        .checked_add(2)
        .ok_or_else(|| GeneratorError("coefficient count overflow".to_owned()))?;
    let artifact = FrozenArtifact {
        magic: ARTIFACT_MAGIC,
        version: ARTIFACT_VERSION,
        layer: 0,
        term_count: u32::try_from(layer.program.term_count)
            .map_err(|error| GeneratorError::context("term count", error))?,
        record_count: u32::try_from(program.len())
            .map_err(|error| GeneratorError::context("record count", error))?,
        coefficient_count,
        c_init_coeff: layer.coefficients.c_init.map(|coefficient| coefficient.0),
        program,
        immediates: layer.coefficients.immediates,
        windows,
        source_slots,
    };
    validate_artifact(&artifact)
        .map_err(|error| GeneratorError::context("validate frozen artifact", error))?;
    Ok(artifact)
}

pub fn generate_bytes(layout_path: &Path) -> Result<Vec<u8>, GeneratorError> {
    let artifact = generate_add_sub_layer0(layout_path)?;
    encode_artifact(&artifact)
        .map_err(|error| GeneratorError::context("encode frozen artifact", error))
}

fn encode_term(
    term: &LeanTerm,
    binding: &LeanSourceBinding,
) -> Result<WindowInstruction, GeneratorError> {
    let (class, source_a, source_b) = match term.class {
        0 => match source_procedural_kind(binding, term.source_a)? {
            Some(kind) => (
                WindowClass::LinearBfProceduralA,
                u16::from(kind),
                SOURCE_NONE,
            ),
            None => {
                let class = match source_field(binding, term.source_a)? {
                    FrozenField::Base => WindowClass::LinearBf,
                    FrozenField::Ext => WindowClass::LinearE4,
                };
                (
                    class,
                    encode_bound_source(binding, term.source_a)?,
                    SOURCE_NONE,
                )
            }
        },
        1 => {
            let procedural_a = source_procedural_kind(binding, term.source_a)?;
            let procedural_b = source_procedural_kind(binding, term.source_b)?;
            match (procedural_a, procedural_b) {
                (Some(_), Some(_)) => {
                    return Err(GeneratorError(
                        "round-0 product has two procedural operands".to_owned(),
                    ));
                }
                (Some(kind), None) => {
                    if source_field(binding, term.source_b)? != FrozenField::Base {
                        return Err(GeneratorError(
                            "round-0 procedural product has an E4 direct operand".to_owned(),
                        ));
                    }
                    (
                        WindowClass::ProductBfBfProceduralB,
                        encode_bound_source(binding, term.source_b)?,
                        u16::from(kind),
                    )
                }
                (None, Some(kind)) => {
                    if source_field(binding, term.source_a)? != FrozenField::Base {
                        return Err(GeneratorError(
                            "round-0 procedural product has an E4 direct operand".to_owned(),
                        ));
                    }
                    (
                        WindowClass::ProductBfBfProceduralB,
                        encode_bound_source(binding, term.source_a)?,
                        u16::from(kind),
                    )
                }
                (None, None) => {
                    let field_a = source_field(binding, term.source_a)?;
                    let field_b = source_field(binding, term.source_b)?;
                    let (class, source_a, source_b) = match (field_a, field_b) {
                        (FrozenField::Base, FrozenField::Base) => {
                            (WindowClass::ProductBfBf, term.source_a, term.source_b)
                        }
                        (FrozenField::Base, FrozenField::Ext) => {
                            (WindowClass::ProductBfE4, term.source_a, term.source_b)
                        }
                        (FrozenField::Ext, FrozenField::Base) => {
                            (WindowClass::ProductBfE4, term.source_b, term.source_a)
                        }
                        (FrozenField::Ext, FrozenField::Ext) => {
                            (WindowClass::ProductE4E4, term.source_a, term.source_b)
                        }
                    };
                    (
                        class,
                        encode_bound_source(binding, source_a)?,
                        encode_bound_source(binding, source_b)?,
                    )
                }
            }
        }
        class => {
            return Err(GeneratorError(format!(
                "continuation term uses unsupported class {class}"
            )));
        }
    };
    Ok(WindowInstruction {
        term_class: class as u16,
        factor: term.coeff,
        source_a,
        source_b,
    })
}

fn source_procedural_kind(
    binding: &LeanSourceBinding,
    source: u16,
) -> Result<Option<u8>, GeneratorError> {
    if source == SOURCE_NONE {
        return Err(GeneratorError("product source is absent".to_owned()));
    }
    let slot = binding
        .source_slots
        .get(usize::from(source))
        .ok_or_else(|| GeneratorError(format!("source {source} is out of range")))?;
    let window = binding
        .windows
        .get(usize::from(slot.window))
        .ok_or_else(|| GeneratorError(format!("source {source} window is out of range")))?;
    Ok(match window.family {
        WindowFamily::VirtualSetup { kind } => Some(kind),
        _ => None,
    })
}

fn encode_bound_source(binding: &LeanSourceBinding, source: u16) -> Result<u16, GeneratorError> {
    let slot = binding
        .source_slots
        .get(usize::from(source))
        .ok_or_else(|| GeneratorError(format!("source {source} is out of range")))?;
    encode_source_coordinate(slot.window, slot.column)
        .map_err(|error| GeneratorError::context("encode direct source coordinate", error))
}

fn record_class(record: &WindowInstruction) -> WindowClass {
    WindowClass::try_from(record.term_class as u8)
        .expect("encode_term always emits a known term class")
}

fn source_field(binding: &LeanSourceBinding, source: u16) -> Result<FrozenField, GeneratorError> {
    if source == SOURCE_NONE {
        return Err(GeneratorError("product source is absent".to_owned()));
    }
    let slot = binding
        .source_slots
        .get(usize::from(source))
        .ok_or_else(|| GeneratorError(format!("source {source} is out of range")))?;
    let window = binding
        .windows
        .get(usize::from(slot.window))
        .ok_or_else(|| GeneratorError(format!("source {source} window is out of range")))?;
    Ok(match window.backing_field() {
        FieldKind::Base => FrozenField::Base,
        FieldKind::Ext => FrozenField::Ext,
    })
}

fn convert_family(family: WindowFamily) -> Result<FrozenWindowFamily, GeneratorError> {
    Ok(match family {
        WindowFamily::BaseLayerMemory => FrozenWindowFamily::BaseLayerMemory,
        WindowFamily::BaseLayerWitness => FrozenWindowFamily::BaseLayerWitness,
        WindowFamily::Setup => FrozenWindowFamily::Setup,
        WindowFamily::Scratch => FrozenWindowFamily::Scratch,
        WindowFamily::LayerOutput { layer, ext } => FrozenWindowFamily::LayerOutput {
            layer: u32::try_from(layer)
                .map_err(|error| GeneratorError::context("layer output index", error))?,
            ext,
        },
        WindowFamily::CacheOutput { layer, ext } => FrozenWindowFamily::CacheOutput {
            layer: u32::try_from(layer)
                .map_err(|error| GeneratorError::context("cache output index", error))?,
            ext,
        },
        WindowFamily::VirtualSetup { kind } => FrozenWindowFamily::VirtualSetup { kind },
    })
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;
    use std::path::PathBuf;

    use gpu_gkr_compiler::backward::{LeanBoundColumn, LeanBoundWindow, LeanSourceSlot};

    use crate::artifact::{
        decode_program, decode_source_coordinate, encode_artifact, validate_artifact, WindowAtom,
        ADD_SUB_LAYER0_BYTES, GROUP_PRODUCT_PREFIX_COUNT_MASK,
    };

    use super::*;

    fn add_sub_layout() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_gkr.json")
    }

    #[test]
    fn add_sub_layer_zero_generates_a_complete_portable_program() {
        let artifact = generate_add_sub_layer0(&add_sub_layout()).unwrap();
        let stats = validate_artifact(&artifact).unwrap();
        let (atoms, decoded) = decode_program(&artifact).unwrap();

        assert_eq!(artifact.layer, 0);
        assert!(artifact.term_count > 0);
        assert!(artifact.coefficient_count > 2);
        assert!(!artifact.program.is_empty());
        assert!(!artifact.source_slots.is_empty());
        assert!(!artifact.windows.is_empty());
        assert_eq!(stats, decoded);
        assert_eq!(decoded.terms, artifact.term_count);
        assert!(atoms.iter().all(|atom| match atom {
            WindowAtom::Term(_) => true,
            WindowAtom::GroupBf { members, .. } | WindowAtom::GroupE4 { members, .. } => {
                members.len() >= 2
            }
        }));
        assert_eq!(decoded.bf_groups, 23);
        assert_eq!(decoded.e4_groups, 2);
    }

    #[test]
    fn add_sub_layer_zero_generation_is_deterministic() {
        let first = generate_add_sub_layer0(&add_sub_layout()).unwrap();
        let second = generate_add_sub_layer0(&add_sub_layout()).unwrap();
        assert_eq!(first, second);
    }

    #[test]
    fn add_sub_layer_zero_uses_direct_source_coordinates() {
        let artifact =
            generate_add_sub_layer0_with_schedule(&add_sub_layout(), ProgramSchedule::Source)
                .unwrap();
        let bound = artifact
            .source_slots
            .iter()
            .map(|slot| (slot.window, slot.column))
            .collect::<std::collections::BTreeSet<_>>();
        let (atoms, _) = decode_program(&artifact).unwrap();
        let mut procedural_linear = 0;
        let mut procedural_product = 0;

        for term in atoms.iter().flat_map(atom_terms) {
            match term.class {
                WindowClass::LinearBfProceduralA => {
                    procedural_linear += 1;
                    assert!(term.source_a < 4);
                    assert_eq!(term.source_b, SOURCE_NONE);
                }
                WindowClass::ProductBfBfProceduralB => {
                    procedural_product += 1;
                    let source_a = decode_source_coordinate(term.source_a).unwrap();
                    assert!(bound.contains(&source_a), "unbound source A {source_a:?}");
                    assert!(term.source_b < 4);
                }
                _ => {
                    let source_a = decode_source_coordinate(term.source_a).unwrap();
                    assert!(bound.contains(&source_a), "unbound source A {source_a:?}");
                    if term.source_b != SOURCE_NONE {
                        let source_b = decode_source_coordinate(term.source_b).unwrap();
                        assert!(bound.contains(&source_b), "unbound source B {source_b:?}");
                    }
                }
            }
        }
        assert_eq!(procedural_linear, 2);
        assert_eq!(procedural_product, 2);
        let procedural_positions = atoms
            .iter()
            .enumerate()
            .filter_map(|(position, atom)| {
                matches!(
                    atom,
                    WindowAtom::Term(term)
                        if matches!(
                            term.class,
                            WindowClass::LinearBfProceduralA
                                | WindowClass::ProductBfBfProceduralB
                        )
                )
                .then_some(position)
            })
            .collect::<Vec<_>>();
        assert_eq!(procedural_positions.len(), 4);
        let first_e4 = atoms
            .iter()
            .position(|atom| term_field(atom_terms(atom)[0].class) == 1)
            .unwrap();
        assert_eq!(
            procedural_positions,
            (first_e4 - 4..first_e4).collect::<Vec<_>>()
        );
    }

    #[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
    struct SemanticAtomKey {
        shape: u8,
        core: u16,
        members: Vec<(u8, u16, u16, u16)>,
    }

    fn procedural_coordinate(artifact: &FrozenArtifact, kind: u16) -> u16 {
        let window = artifact
            .windows
            .iter()
            .position(|window| {
                window.family == FrozenWindowFamily::VirtualSetup { kind: kind as u8 }
            })
            .unwrap() as u8;
        let slot = artifact
            .source_slots
            .iter()
            .find(|slot| slot.window == window)
            .unwrap();
        encode_source_coordinate(slot.window, slot.column).unwrap()
    }

    fn semantic_term(
        artifact: &FrozenArtifact,
        term: &crate::artifact::WindowTerm,
    ) -> (u8, u16, u16, u16) {
        match term.class {
            WindowClass::LinearBfProceduralA => (
                WindowClass::LinearBf as u8,
                term.coefficient,
                procedural_coordinate(artifact, term.source_a),
                SOURCE_NONE,
            ),
            WindowClass::ProductBfBfProceduralB => (
                WindowClass::ProductBfBf as u8,
                term.coefficient,
                term.source_a,
                procedural_coordinate(artifact, term.source_b),
            ),
            _ => (
                term.class as u8,
                term.coefficient,
                term.source_a,
                term.source_b,
            ),
        }
    }

    fn semantic_members(
        artifact: &FrozenArtifact,
        members: &[crate::artifact::WindowTerm],
    ) -> Vec<(u8, u16, u16, u16)> {
        let mut keys = members
            .iter()
            .map(|term| semantic_term(artifact, term))
            .collect::<Vec<_>>();
        keys.sort_unstable();
        keys
    }

    fn semantic_multiset(
        artifact: &FrozenArtifact,
        atoms: &[WindowAtom],
    ) -> BTreeMap<SemanticAtomKey, usize> {
        atoms.iter().fold(BTreeMap::new(), |mut counts, atom| {
            let key = match atom {
                WindowAtom::Term(term) => SemanticAtomKey {
                    shape: 0,
                    core: term.coefficient,
                    members: vec![semantic_term(artifact, term)],
                },
                WindowAtom::GroupBf { core, members, .. } => SemanticAtomKey {
                    shape: 1,
                    core: *core,
                    members: semantic_members(artifact, members),
                },
                WindowAtom::GroupE4 { core, members } => SemanticAtomKey {
                    shape: 2,
                    core: *core,
                    members: semantic_members(artifact, members),
                },
            };
            *counts.entry(key).or_default() += 1;
            counts
        })
    }

    #[test]
    fn program_schedules_preserve_semantic_multiset() {
        let variants = [
            ProgramSchedule::Compiler,
            ProgramSchedule::ControlAtoms,
            ProgramSchedule::Control,
            ProgramSchedule::Source,
        ]
        .map(|schedule| {
            let artifact =
                generate_add_sub_layer0_with_schedule(&add_sub_layout(), schedule).unwrap();
            let (atoms, stats) = decode_program(&artifact).unwrap();
            assert_eq!(stats.terms, 150);
            assert_eq!(atoms.len(), 72);
            assert_eq!(stats.groups, 25);
            let bf_atoms = atoms
                .iter()
                .filter(|atom| {
                    matches!(
                        atom,
                        WindowAtom::Term(term)
                            if matches!(
                                term.class,
                                WindowClass::LinearBf
                                    | WindowClass::ProductBfBf
                                    | WindowClass::LinearBfProceduralA
                                    | WindowClass::ProductBfBfProceduralB
                            )
                    ) || matches!(atom, WindowAtom::GroupBf { .. })
                })
                .count();
            assert_eq!(bf_atoms, 65);
            (artifact, atoms)
        });
        let expected = semantic_multiset(&variants[0].0, &variants[0].1);
        for (artifact, atoms) in &variants[1..] {
            assert_eq!(semantic_multiset(artifact, atoms), expected);
        }
    }

    #[test]
    fn lazy_bf_reduction_marks_product_prefixes() {
        let artifact =
            generate_add_sub_layer0_with_options(&add_sub_layout(), ProgramSchedule::Source, true)
                .unwrap();
        let (atoms, _) = decode_program(&artifact).unwrap();
        let mut lazy_groups = 0usize;
        let mut lazy_products = 0usize;

        for atom in atoms {
            if let WindowAtom::GroupBf {
                lazy_product_count,
                members,
                ..
            } = atom
            {
                if lazy_product_count == 0 {
                    continue;
                }
                lazy_groups += 1;
                lazy_products += usize::from(lazy_product_count);
                assert!(lazy_product_count >= 2);
                assert!(members[..usize::from(lazy_product_count)]
                    .iter()
                    .all(|member| member.class == WindowClass::ProductBfBf));
                assert!(members[usize::from(lazy_product_count)..]
                    .iter()
                    .all(|member| member.class == WindowClass::LinearBf));
            }
        }

        assert_eq!(lazy_groups, 10);
        assert_eq!(lazy_products, 72);
        assert_eq!(
            artifact
                .program
                .iter()
                .filter(|instruction| instruction.factor & REDUCE_AFTER != 0)
                .count(),
            21
        );
    }

    #[test]
    fn group_product_headers_match_their_members() {
        for schedule in [
            ProgramSchedule::Compiler,
            ProgramSchedule::ControlAtoms,
            ProgramSchedule::Control,
            ProgramSchedule::Source,
        ] {
            let artifact =
                generate_add_sub_layer0_with_options(&add_sub_layout(), schedule, true).unwrap();
            let (atoms, _) = decode_program(&artifact).unwrap();
            let mut record = 0usize;

            for atom in atoms {
                let head = artifact.program[record];
                match atom {
                    WindowAtom::Term(_) => record += 1,
                    WindowAtom::GroupBf {
                        lazy_product_count,
                        members,
                        ..
                    } => {
                        let has_product = head.source_b & GROUP_HAS_PRODUCT != 0;
                        let prefix_count = head.source_b & GROUP_PRODUCT_PREFIX_COUNT_MASK;
                        let product_positions = members
                            .iter()
                            .enumerate()
                            .filter_map(|(position, member)| {
                                (member.class == WindowClass::ProductBfBf).then_some(position)
                            })
                            .collect::<Vec<_>>();
                        assert_eq!(has_product, !product_positions.is_empty());
                        match prefix_count {
                            0 => assert!(product_positions.is_empty()),
                            1 => {
                                assert_eq!(product_positions, vec![0]);
                                assert_eq!(lazy_product_count, 0);
                            }
                            count => {
                                assert_eq!(count, lazy_product_count);
                                assert_eq!(
                                    product_positions,
                                    (0..usize::from(count)).collect::<Vec<_>>()
                                );
                            }
                        }
                        record += members.len() + 1;
                    }
                    WindowAtom::GroupE4 { members, .. } => {
                        assert_eq!(head.source_a, 0);
                        assert_eq!(head.source_b & GROUP_PRODUCT_PREFIX_COUNT_MASK, 0);
                        let has_product = head.source_b & GROUP_HAS_PRODUCT != 0;
                        let products = members.iter().filter(|member| {
                            matches!(
                                member.class,
                                WindowClass::ProductBfE4 | WindowClass::ProductE4E4
                            )
                        });
                        assert_eq!(has_product, products.count() != 0);
                        record += members.len() + 1;
                    }
                }
            }
            assert_eq!(record, artifact.program.len());
        }
    }

    #[test]
    fn lazy_bf_reduction_preserves_semantic_multiset() {
        let ordinary =
            generate_add_sub_layer0_with_options(&add_sub_layout(), ProgramSchedule::Source, false)
                .unwrap();
        let lazy =
            generate_add_sub_layer0_with_options(&add_sub_layout(), ProgramSchedule::Source, true)
                .unwrap();
        let (ordinary_atoms, _) = decode_program(&ordinary).unwrap();
        let (lazy_atoms, _) = decode_program(&lazy).unwrap();

        assert_eq!(
            semantic_multiset(&lazy, &lazy_atoms),
            semantic_multiset(&ordinary, &ordinary_atoms)
        );
    }

    #[test]
    fn source_schedule_with_lazy_reduction_matches_embedded_artifact() {
        let artifact =
            generate_add_sub_layer0_with_options(&add_sub_layout(), ProgramSchedule::Source, true)
                .unwrap();

        assert_eq!(encode_artifact(&artifact).unwrap(), ADD_SUB_LAYER0_BYTES);
    }

    #[test]
    fn schedule_wrapper_keeps_lazy_reduction_disabled() {
        assert_eq!(
            generate_add_sub_layer0_with_schedule(&add_sub_layout(), ProgramSchedule::Source)
                .unwrap(),
            generate_add_sub_layer0_with_options(
                &add_sub_layout(),
                ProgramSchedule::Source,
                false,
            )
            .unwrap()
        );
    }

    #[test]
    fn unsupported_procedural_products_are_rejected() {
        let binding = LeanSourceBinding {
            windows: vec![
                LeanBoundWindow {
                    family: WindowFamily::VirtualSetup { kind: 0 },
                    first_column: 0,
                    columns: vec![LeanBoundColumn {
                        column: 0,
                        source: 0,
                    }],
                },
                LeanBoundWindow {
                    family: WindowFamily::VirtualSetup { kind: 1 },
                    first_column: 0,
                    columns: vec![LeanBoundColumn {
                        column: 0,
                        source: 1,
                    }],
                },
                LeanBoundWindow {
                    family: WindowFamily::CacheOutput {
                        layer: 0,
                        ext: true,
                    },
                    first_column: 0,
                    columns: vec![LeanBoundColumn {
                        column: 0,
                        source: 2,
                    }],
                },
            ],
            source_slots: vec![
                LeanSourceSlot {
                    window: 0,
                    column: 0,
                },
                LeanSourceSlot {
                    window: 1,
                    column: 0,
                },
                LeanSourceSlot {
                    window: 2,
                    column: 0,
                },
            ],
        };
        let product = |source_a, source_b| LeanTerm {
            class: 1,
            coeff: 0,
            source_a,
            source_b,
        };

        let error = encode_term(&product(0, 1), &binding).unwrap_err();
        assert!(error.0.contains("two procedural operands"));
        let error = encode_term(&product(0, 2), &binding).unwrap_err();
        assert!(error.0.contains("E4 direct operand"));
    }

    #[test]
    fn schedule_census_tracks_control_and_source_locality() {
        let census = |schedule| {
            let artifact =
                generate_add_sub_layer0_with_schedule(&add_sub_layout(), schedule).unwrap();
            schedule_census(&artifact).unwrap()
        };
        let compiler = census(ProgramSchedule::Compiler);
        let control_atoms = census(ProgramSchedule::ControlAtoms);
        let control = census(ProgramSchedule::Control);
        let source = census(ProgramSchedule::Source);

        for candidate in [control_atoms, control, source] {
            assert_eq!(candidate.atoms, 72);
            assert_eq!(candidate.terms, 150);
            assert_eq!(candidate.bf_atoms, 65);
            assert_eq!(candidate.e4_atoms, 7);
            assert_eq!(candidate.field_transitions, 1);
        }
        assert_eq!(control.shape_transitions_within_field, 2);
        assert!(control.class_transitions < compiler.class_transitions);
        assert!(
            source.adjacent_equal_source_a + source.adjacent_equal_source_b
                >= compiler.adjacent_equal_source_a + compiler.adjacent_equal_source_b
        );
        assert!(compiler.projected_procedural_bf_accesses <= compiler.projected_bf_accesses);
        assert_eq!(source.projected_bf_accesses, 6_904);
        assert_eq!(source.projected_procedural_bf_accesses, 80);
    }
}
