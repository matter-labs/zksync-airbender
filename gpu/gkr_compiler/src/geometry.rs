use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use cs::definitions::GKRAddress;
use cs::gkr_compiler::{GKRCircuitArtifact, GKRRelation};
use field::proth120::Proth120;
use gkr_eval_ir::{DagCircuit, ReadPlace, SinkKind};

use crate::backward::window::WINDOW_PROGRAM_WORD_CAP;
use crate::forward::isa::{DstLine, Instr, LdcSub, OperandField, OperandLine};
use crate::{
    encode_forward_runtime_program, ContinuationProgramBundle, ElementModel, ForwardProgramBundle,
    ForwardSpecialStrategy, MainContinuationWindowProgram, MainTailProgram,
    NormalizedCoefficientRecipe, R0WindowProgram, WindowCoefficientPlan, LEAN_MAX_IMMEDIATES,
    MAIN_CONTINUATION_WINDOW_COEFFICIENT_BANK_CAPACITY,
    MAIN_CONTINUATION_WINDOW_IMMEDIATE_CAPACITY, MAIN_CONTINUATION_WINDOW_PROGRAM_WORD_CAPACITY,
    MAIN_CONTINUATION_WINDOW_SOURCE_CAPACITY, MAX_BACKWARD_COEFFICIENT_RECIPES,
    MAX_BACKWARD_SOURCES, PR_MAIN_CONTINUATION_MASKS, WINDOW_MAX_COEFFICIENT_PLANS,
};

pub const PR_FWD_VM_CONST_CAP: usize = 64;

#[derive(Clone, Debug, Default, serde::Serialize)]
pub struct ForwardLayerGeometry {
    pub program_lanes: usize,
    pub constants: usize,
    pub specials: usize,
    pub argument_derived: usize,
    pub constant_derived: usize,
    pub logical_source_windows: usize,
    pub logical_slots: usize,
    pub source_windows: usize,
    pub destination_slots: usize,
}

#[derive(Clone, Debug, Default, serde::Serialize)]
pub struct ForwardBackingGeometry {
    pub matrix: String,
    pub base: usize,
    pub columns: usize,
    pub stride_bytes: u32,
}

#[derive(Clone, Debug, Default, serde::Serialize)]
pub struct BackwardLayerGeometry {
    pub layer: usize,
    pub r0_kernel: String,
    pub r0_shape: u16,
    pub r0_words: usize,
    pub r0_sections: [u32; 4],
    pub r0_coefficient_plans: usize,
    pub r0_monomials: usize,
    pub r0_immediates: usize,
    pub r0_partition_plans: usize,
    pub continuation_words: usize,
    pub continuation_recipes: usize,
    pub continuation_monomials: usize,
    pub continuation_sources: usize,
    pub continuation_terms: usize,
    pub continuation_groups: usize,
    pub continuation_immediates: usize,
    pub continuation_mask: u16,
    pub main_tail_words: usize,
    pub main_tail_immediates: usize,
}

pub struct BackwardPrograms<'a> {
    pub r0: &'a [R0WindowProgram],
    pub continuations: &'a ContinuationProgramBundle,
    pub main_continuation_window: &'a [MainContinuationWindowProgram],
    pub main_tail: &'a [MainTailProgram],
}

#[derive(Clone, Debug, Default, serde::Serialize)]
pub struct GeometryReport {
    pub backings: Vec<ForwardBackingGeometry>,
    pub forward_layers: Vec<ForwardLayerGeometry>,
    pub backward_layers: Vec<BackwardLayerGeometry>,
    pub program_lanes: usize,
    pub constants: usize,
    pub constant_capacity: usize,
    pub specials: usize,
    pub argument_derived: usize,
    pub constant_derived: usize,
    pub layers: usize,
    pub source_windows: usize,
    pub destination_slots: usize,
    pub stride_bytes: u32,
    pub canonical_dynamic_columns: usize,
    pub aliases: usize,
}

#[derive(Clone, Debug)]
pub struct GeometryError {
    pub message: String,
    pub report: Option<GeometryReport>,
}

impl fmt::Display for GeometryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for GeometryError {}

fn error(message: impl Into<String>) -> GeometryError {
    GeometryError {
        message: message.into(),
        report: None,
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Matrix {
    Raw,
    Setup,
    Scratch,
    Inner(usize, OperandField),
    Cached(usize, OperandField),
}

fn address(place: ReadPlace) -> GKRAddress {
    match place {
        ReadPlace::BaseLayerMemory { column } => GKRAddress::BaseLayerMemory(column),
        ReadPlace::BaseLayerWitness { column } => GKRAddress::BaseLayerWitness(column),
        ReadPlace::Setup { column } => GKRAddress::Setup(column),
        ReadPlace::Scratch { slot } => GKRAddress::ScratchSpace(slot),
        ReadPlace::LayerOutput { layer, offset } => GKRAddress::InnerLayer { layer, offset },
        ReadPlace::CacheOutput { layer, offset } => GKRAddress::Cached { layer, offset },
    }
}

fn normalize(address: GKRAddress, layout: &GKRCircuitArtifact<Proth120>) -> GKRAddress {
    layout
        .scratch_space_mapping
        .get(&address)
        .map_or(address, |&slot| GKRAddress::ScratchSpace(slot))
}

fn canonical(
    mut address: GKRAddress,
    aliases: &BTreeMap<GKRAddress, GKRAddress>,
) -> Result<GKRAddress, GeometryError> {
    for _ in 0..=aliases.len() {
        match aliases.get(&address) {
            Some(&next) if next != address => address = next,
            _ => return Ok(address),
        }
    }
    Err(error(format!(
        "forward geometry: alias cycle at {address:?}"
    )))
}

fn matrix(address: GKRAddress, field: OperandField) -> Result<Matrix, GeometryError> {
    match address {
        GKRAddress::BaseLayerMemory(_) | GKRAddress::BaseLayerWitness(_) => Ok(Matrix::Raw),
        GKRAddress::Setup(_) => Ok(Matrix::Setup),
        GKRAddress::ScratchSpace(_) => Ok(Matrix::Scratch),
        GKRAddress::InnerLayer { layer, .. } => Ok(Matrix::Inner(layer, field)),
        GKRAddress::Cached { layer, .. } => Ok(Matrix::Cached(layer, field)),
        GKRAddress::VirtualSetup(_) => Err(error("forward geometry: virtual setup has no matrix")),
    }
}

fn visit_operands(
    program: &mut crate::ForwardProgram,
    mut visit: impl FnMut(&mut OperandLine, OperandField) -> Result<(), GeometryError>,
) -> Result<(), GeometryError> {
    for instruction in &mut program.instrs {
        match instruction {
            Instr::Add {
                field, operands, ..
            }
            | Instr::Mul {
                field, operands, ..
            } => {
                for operand in operands {
                    visit(operand, *field)?;
                }
            }
            Instr::Fma {
                field_lhs,
                field_rhs,
                pairs,
                ..
            } => {
                for (lhs, rhs) in pairs {
                    visit(lhs, *field_lhs)?;
                    visit(rhs, *field_rhs)?;
                }
            }
            Instr::Mov { field, src, .. } => {
                if let Some(src) = src {
                    visit(src, *field)?;
                }
            }
        }
    }
    Ok(())
}

pub fn validate_forward_proth120(
    dag: &DagCircuit,
    forward: &ForwardProgramBundle,
    layout: &GKRCircuitArtifact<Proth120>,
) -> Result<GeometryReport, GeometryError> {
    if ElementModel::for_dag(dag) != ElementModel::PROTH120 {
        return Err(error("forward geometry: expected Proth120 DAG"));
    }
    if forward.layers.is_empty() {
        return Err(error("forward geometry: at least one layer is required"));
    }
    if forward.layers.len() != dag.layers.len() || dag.layers.len() != layout.layers.len() {
        return Err(error(
            "forward geometry: DAG, program and layout layer counts differ",
        ));
    }
    if !layout.trace_len.is_power_of_two() {
        return Err(error(
            "forward geometry: trace_len must be a positive power of two",
        ));
    }
    let stride_bytes = layout
        .trace_len
        .checked_mul(16)
        .and_then(|n| u32::try_from(n).ok())
        .ok_or_else(|| error("forward geometry: stride_bytes exceeds u32"))?;
    let mut aliases = BTreeMap::new();
    for layer in &layout.layers {
        for gate in layer
            .gates
            .iter()
            .chain(&layer.gates_with_external_connections)
        {
            if let GKRRelation::CopyInBaseField { input, output }
            | GKRRelation::CopyInExtensionField { input, output } = gate.enforced_relation
            {
                let input = canonical(normalize(input, layout), &aliases)?;
                aliases.insert(normalize(output, layout), input);
            }
        }
    }
    let mut columns: BTreeMap<Matrix, BTreeSet<GKRAddress>> = BTreeMap::new();
    let mut fields = BTreeMap::new();
    for layer in &dag.layers {
        for root in &layer.roots {
            if let Some(sink) = root.materialize {
                let place = match sink.kind {
                    SinkKind::Scratch { slot } => ReadPlace::Scratch { slot },
                    _ => sink
                        .kind
                        .read_place()
                        .expect("forward geometry: materialized sink has a place"),
                };
                let addr = normalize(address(place), layout);
                if aliases.contains_key(&addr) {
                    continue;
                }
                let field = OperandField::from(sink.field);
                if let Some(previous) = fields.insert(addr, field) {
                    if previous != field {
                        return Err(error(format!(
                            "forward geometry: conflicting fields for {addr:?}"
                        )));
                    }
                }
                let backing = matrix(addr, field)?;
                if matches!(backing, Matrix::Inner(..) | Matrix::Cached(..)) {
                    columns.entry(backing).or_default().insert(addr);
                }
            }
        }
    }
    let dynamic: BTreeMap<_, _> = columns
        .iter()
        .flat_map(|(&backing, addresses)| {
            addresses
                .iter()
                .enumerate()
                .map(move |(column, &addr)| (addr, (backing, column)))
        })
        .collect();
    let mut capacities: BTreeMap<Matrix, usize> = columns
        .iter()
        .map(|(&key, values)| (key, values.len()))
        .collect();
    capacities.insert(
        Matrix::Raw,
        layout
            .memory_layout
            .total_width
            .checked_add(layout.witness_layout.total_width)
            .ok_or_else(|| error("forward geometry: raw width overflow"))?,
    );
    capacities.insert(
        Matrix::Setup,
        layout
            .generic_lookup_tables_width
            .max(layout.decode_table_columns_mask.len()),
    );
    capacities.insert(Matrix::Scratch, layout.scratch_space_size);
    let mut backings = Vec::new();
    let mut bases = BTreeMap::new();
    let mut next_base = 0x100000usize;
    for (&backing, &count) in &capacities {
        bases.insert(backing, next_base);
        backings.push(ForwardBackingGeometry {
            matrix: format!("{backing:?}"),
            base: next_base,
            columns: count,
            stride_bytes,
        });
        next_base = count
            .checked_add(1)
            .and_then(|n| n.checked_mul(stride_bytes as usize))
            .and_then(|bytes| next_base.checked_add(bytes))
            .ok_or_else(|| error("forward geometry: synthetic backing address overflow"))?;
    }
    let resolve = |place: ReadPlace,
                   expect: OperandField|
     -> Result<(OperandField, usize, usize), GeometryError> {
        let addr = canonical(normalize(address(place), layout), &aliases)?;
        let (field, backing, column) = match addr {
            GKRAddress::BaseLayerMemory(column) => {
                if column >= layout.memory_layout.total_width {
                    return Err(error("forward geometry: memory column out of range"));
                }
                (OperandField::Base, Matrix::Raw, column)
            }
            GKRAddress::BaseLayerWitness(column) => {
                if column >= layout.witness_layout.total_width {
                    return Err(error("forward geometry: witness column out of range"));
                }
                (
                    OperandField::Base,
                    Matrix::Raw,
                    layout
                        .memory_layout
                        .total_width
                        .checked_add(column)
                        .ok_or_else(|| error("forward geometry: raw column overflow"))?,
                )
            }
            GKRAddress::Setup(column) => (OperandField::Base, Matrix::Setup, column),
            GKRAddress::ScratchSpace(column) => {
                if column >= layout.scratch_space_size {
                    return Err(error("forward geometry: scratch column out of range"));
                }
                (OperandField::Base, Matrix::Scratch, column)
            }
            _ => {
                let &(backing, column) = dynamic.get(&addr).ok_or_else(|| {
                    error(format!(
                        "forward geometry: unresolved canonical column {addr:?}"
                    ))
                })?;
                (fields[&addr], backing, column)
            }
        };
        if field != expect {
            return Err(error(format!(
                "forward geometry: {addr:?} has field {field:?}, expected {expect:?}"
            )));
        }
        if column >= capacities[&backing] {
            return Err(error(format!(
                "forward geometry: {backing:?} column {column} exceeds backing width {}",
                capacities[&backing]
            )));
        }
        let base = bases[&backing];
        let ptr = column
            .checked_mul(stride_bytes as usize)
            .and_then(|offset| base.checked_add(offset))
            .ok_or_else(|| error("forward geometry: synthetic column address overflow"))?;
        let offset = ptr
            .checked_sub(base)
            .filter(|offset| offset.is_multiple_of(stride_bytes as usize))
            .ok_or_else(|| error("forward geometry: column off stride"))?;
        Ok((field, base, offset / stride_bytes as usize))
    };
    type Key = (usize, u8, u16);
    let mut sources = BTreeMap::new();
    let mut destinations = BTreeMap::new();
    for (index, layer) in forward.layers.iter().enumerate() {
        let mut program = layer.program.clone();
        visit_operands(&mut program, |operand, field| {
            if let OperandLine::Source { window, column } = *operand {
                if layer.source_windows.source_field(window) != Some(field) {
                    return Err(error("forward geometry: source window field mismatch"));
                }
                let place = layer
                    .source_windows
                    .resolve_read_place(window, column)
                    .ok_or_else(|| error("forward geometry: unmapped source"))?;
                let physical = resolve(place, field)?;
                if let Some(previous) = sources.insert((index, window, column), physical) {
                    if previous != physical {
                        return Err(error("forward geometry: source resolved two ways"));
                    }
                }
            }
            Ok(())
        })?;
        for instruction in &program.instrs {
            if let Instr::Mov {
                field,
                dst: Some(DstLine::GlobalMaterialize { slot, col }),
                ..
            } = *instruction
            {
                let place = layer
                    .backings
                    .slot_col_to_read_place(slot, col)
                    .ok_or_else(|| error("forward geometry: unmapped destination"))?;
                destinations.insert((index, slot, col), resolve(place, field)?);
            }
        }
    }
    let mut sorted: Vec<_> = sources
        .iter()
        .map(|(&key, &physical)| (physical, key))
        .collect();
    sorted.sort_unstable();
    let mut source_remap: BTreeMap<Key, (u8, u16)> = BTreeMap::new();
    let mut windows = Vec::new();
    for ((field, backing, column), key) in sorted {
        let reuse = windows
            .last()
            .is_some_and(|&(f, b, first)| f == field && b == backing && column < first + 512);
        if !reuse {
            windows.push((field, backing, column));
        }
        let window = windows.len() - 1;
        let window = u8::try_from(window)
            .map_err(|_| error("forward geometry: source window index exceeds u8"))?;
        source_remap.insert(key, (window, (column - windows.last().unwrap().2) as u16));
    }
    let destination_groups: BTreeSet<_> = destinations
        .values()
        .map(|&(field, backing, _)| (field, backing))
        .collect();
    let destination_slots: BTreeMap<_, _> = destination_groups
        .iter()
        .enumerate()
        .map(|(slot, &group)| (group, slot))
        .collect();
    let mut destination_remap = BTreeMap::new();
    for (&key, &(field, backing, column)) in &destinations {
        if column >= crate::FORWARD_MAX_COLS as usize {
            return Err(error(format!(
                "forward geometry: destination column {column} exceeds {}",
                crate::FORWARD_MAX_COLS
            )));
        }
        let slot = u8::try_from(destination_slots[&(field, backing)])
            .map_err(|_| error("forward geometry: destination slot exceeds u8"))?;
        destination_remap.insert(key, (slot, column as u16));
    }
    let mut report = GeometryReport {
        backings,
        constant_capacity: PR_FWD_VM_CONST_CAP,
        layers: forward.layers.len(),
        source_windows: windows.len(),
        destination_slots: destination_slots.len(),
        stride_bytes,
        canonical_dynamic_columns: dynamic.len(),
        aliases: aliases.len(),
        ..GeometryReport::default()
    };
    let lookup = forward
        .layers
        .iter()
        .any(|layer| layer.derived_e4.uses_lookup_additive());
    let decoder = forward.layers.iter().any(|layer| {
        layer
            .specials
            .iter()
            .any(|special| matches!(special, ForwardSpecialStrategy::PeekDecoder { .. }))
    });
    report.constant_derived = usize::from(lookup) + usize::from(decoder);
    for (index, layer) in forward.layers.iter().enumerate() {
        let used_windows: BTreeSet<_> = source_remap
            .iter()
            .filter(|(key, _)| key.0 == index)
            .map(|(_, coordinate)| coordinate.0)
            .collect();
        let used_slots: BTreeSet<_> = destination_remap
            .iter()
            .filter(|(key, _)| key.0 == index)
            .map(|(_, coordinate)| coordinate.0)
            .collect();
        let logical_slots = (0..16)
            .filter(|&slot| layer.backings.slot_field(slot).is_some())
            .count();
        let lanes = crate::encode_forward_program(&layer.program)
            .map_err(|failure| {
                error(format!(
                    "forward geometry: logical encoding failed: {failure:?}"
                ))
            })?
            .len();
        report.forward_layers.push(ForwardLayerGeometry {
            program_lanes: lanes,
            constants: layer.consts.values().len()
                + layer
                    .specials
                    .iter()
                    .filter(|special| {
                        matches!(
                            special,
                            ForwardSpecialStrategy::InitsAndTeardownsTopBits { .. }
                        )
                    })
                    .count(),
            specials: layer.specials.len(),
            argument_derived: layer.derived_e4.arg_refs().len(),
            constant_derived: usize::from(layer.derived_e4.uses_lookup_additive())
                + usize::from(
                    layer.specials.iter().any(|special| {
                        matches!(special, ForwardSpecialStrategy::PeekDecoder { .. })
                    }),
                ),
            logical_source_windows: layer.source_windows.len(),
            logical_slots,
            source_windows: used_windows.len(),
            destination_slots: used_slots.len(),
        });
        report.program_lanes += lanes;
        report.constants += report.forward_layers.last().unwrap().constants;
        report.specials += layer.specials.len();
        report.argument_derived += layer.derived_e4.arg_refs().len();
    }
    for (name, count, cap) in [
        ("program lanes", report.program_lanes, 12_288),
        ("constants", report.constants, PR_FWD_VM_CONST_CAP),
        ("specials", report.specials, 370),
        ("argument-derived", report.argument_derived, 12),
        ("constant-derived", report.constant_derived, 8),
        ("layers", report.layers, 8),
        ("source windows", report.source_windows, 16),
        ("destination slots", report.destination_slots, 16),
    ] {
        if count > cap {
            return Err(GeometryError {
                message: format!("forward geometry: {name} {count} exceeds cap {cap}"),
                report: Some(report),
            });
        }
    }
    let mut constants = 0;
    let mut argument_derived = 0;
    let mut specials = 0;
    for (index, layer) in forward.layers.iter().enumerate() {
        let mut program = layer.program.clone();
        visit_operands(&mut program, |operand, _| {
            match operand {
                OperandLine::Source { window, column } => {
                    let coordinate = source_remap[&(index, *window, *column)];
                    *window = coordinate.0;
                    *column = coordinate.1;
                }
                OperandLine::Ldc {
                    sub: LdcSub::Const,
                    idx,
                } => {
                    *idx = u16::try_from(*idx as usize + constants)
                        .map_err(|_| error("forward geometry: constant index overflow"))?
                }
                OperandLine::Ldc {
                    sub: LdcSub::ArgDerivedE4,
                    idx,
                } => {
                    *idx = u16::try_from(*idx as usize + argument_derived)
                        .map_err(|_| error("forward geometry: argument index overflow"))?
                }
                OperandLine::Special { desc } => {
                    *desc = u16::try_from(*desc as usize + specials)
                        .map_err(|_| error("forward geometry: descriptor index overflow"))?
                }
                _ => {}
            }
            Ok(())
        })?;
        for instruction in &mut program.instrs {
            if let Instr::Mov {
                dst: Some(DstLine::GlobalMaterialize { slot, col }),
                ..
            } = instruction
            {
                let coordinate = destination_remap[&(index, *slot, *col)];
                *slot = coordinate.0;
                *col = coordinate.1;
            }
        }
        let lanes = encode_forward_runtime_program(&program)
            .map_err(|failure| {
                error(format!(
                    "forward geometry: runtime encoding failed: {failure:?}"
                ))
            })?
            .len();
        if lanes != report.forward_layers[index].program_lanes {
            return Err(error("forward geometry: rebinding changed program length"));
        }
        constants += report.forward_layers[index].constants;
        argument_derived += layer.derived_e4.arg_refs().len();
        specials += layer.specials.len();
    }
    Ok(report)
}

fn monomials(recipes: impl IntoIterator<Item = usize>) -> usize {
    recipes.into_iter().sum()
}

fn recipe_monomials(recipe: &NormalizedCoefficientRecipe) -> usize {
    recipe.terms.len()
}

fn plan_monomials(plan: &WindowCoefficientPlan) -> usize {
    match plan {
        WindowCoefficientPlan::Direct(recipe)
        | WindowCoefficientPlan::Scaled { recipe, .. }
        | WindowCoefficientPlan::LinearBasis { recipe, .. } => recipe_monomials(recipe),
    }
}

pub fn validate_proth120(
    dag: &DagCircuit,
    forward: &ForwardProgramBundle,
    programs: &BackwardPrograms<'_>,
    layout: &GKRCircuitArtifact<Proth120>,
) -> Result<GeometryReport, GeometryError> {
    let mut report = validate_forward_proth120(dag, forward, layout)?;
    let layers = dag.layers.len();
    if programs.r0.len() != layers
        || programs.continuations.layers.len() != layers
        || programs.main_continuation_window.len() != layers
        || programs.main_tail.len() != layers
    {
        return Err(error(
            "backward geometry: R0, continuation, window and tail layer counts differ from the DAG",
        ));
    }
    for layer in 0..layers {
        let r0 = &programs.r0[layer];
        let continuation = &programs.continuations.layers[layer];
        let window = &programs.main_continuation_window[layer];
        let tail = &programs.main_tail[layer];
        let coefficients = &continuation.coefficients;
        let geometry = BackwardLayerGeometry {
            layer,
            r0_kernel: format!("{:?}", r0.kernel),
            r0_shape: r0.window.shape.bits(),
            r0_words: r0.window.words.len(),
            r0_sections: r0.window.sections,
            r0_coefficient_plans: r0.window.coefficient_plans.len(),
            r0_monomials: monomials(r0.window.coefficient_plans.iter().map(plan_monomials)),
            r0_immediates: r0.window.immediates.len(),
            r0_partition_plans: r0.partition_candidates.plans.len(),
            continuation_words: continuation.program.words.len(),
            continuation_recipes: coefficients.coefficients.len(),
            continuation_monomials: monomials(
                coefficients.coefficients.iter().map(recipe_monomials),
            ),
            continuation_sources: coefficients.sources.len(),
            continuation_terms: coefficients.terms.len(),
            continuation_groups: coefficients.groups.len(),
            continuation_immediates: coefficients.immediates.len(),
            continuation_mask: window.shape.bits(),
            main_tail_words: tail.program_words.len(),
            main_tail_immediates: tail.immediates.len(),
        };
        let checks = [
            (
                "R0 program words",
                geometry.r0_words,
                WINDOW_PROGRAM_WORD_CAP,
            ),
            (
                "R0 coefficient plans",
                geometry.r0_coefficient_plans,
                WINDOW_MAX_COEFFICIENT_PLANS,
            ),
            ("R0 immediates", geometry.r0_immediates, LEAN_MAX_IMMEDIATES),
            (
                "continuation program words",
                geometry.continuation_words,
                MAIN_CONTINUATION_WINDOW_PROGRAM_WORD_CAPACITY,
            ),
            (
                "continuation recipes",
                geometry.continuation_recipes,
                MAX_BACKWARD_COEFFICIENT_RECIPES
                    .min(MAIN_CONTINUATION_WINDOW_COEFFICIENT_BANK_CAPACITY),
            ),
            (
                "continuation sources",
                geometry.continuation_sources,
                MAX_BACKWARD_SOURCES.min(MAIN_CONTINUATION_WINDOW_SOURCE_CAPACITY),
            ),
            (
                "continuation immediates",
                geometry.continuation_immediates,
                MAIN_CONTINUATION_WINDOW_IMMEDIATE_CAPACITY,
            ),
            (
                "main tail immediates",
                geometry.main_tail_immediates,
                LEAN_MAX_IMMEDIATES,
            ),
        ];
        report.backward_layers.push(geometry);
        for (name, count, cap) in checks {
            if count > cap {
                return Err(GeometryError {
                    message: format!(
                        "backward geometry: layer {layer} {name} {count} exceeds cap {cap}"
                    ),
                    report: Some(report),
                });
            }
        }
        let geometry = report.backward_layers.last().unwrap();
        if geometry.r0_shape & !r0.kernel.shape_mask() != 0 {
            return Err(GeometryError {
                message: format!(
                    "backward geometry: layer {layer} R0 shape {:#x} exceeds {} kernel mask {:#x}",
                    geometry.r0_shape,
                    geometry.r0_kernel,
                    r0.kernel.shape_mask()
                ),
                report: Some(report),
            });
        }
        let mask = u8::try_from(geometry.continuation_mask).ok();
        if !mask.is_some_and(|mask| PR_MAIN_CONTINUATION_MASKS.contains(&mask)) {
            return Err(GeometryError {
                message: format!(
                    "backward geometry: layer {layer} continuation mask {:#04x} is not in PR_MAIN_CONTINUATION_MASKS",
                    geometry.continuation_mask
                ),
                report: Some(report),
            });
        }
    }
    Ok(report)
}
