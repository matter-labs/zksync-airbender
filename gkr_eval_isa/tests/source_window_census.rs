//! Test-local census for the fixed source-window descriptor encoding.
//!
//! Each logical DRAM matrix gets its own freely assigned source windows.  In
//! particular, `LayerOutput` and `CacheOutput` keep their backing storage field
//! in the family key, mirroring `BackingKey`: base and extension columns of one
//! logical output cannot share an encoded source window.

mod common;

use std::collections::{BTreeMap, BTreeSet};

use common::load_dag_sched;
use cs::gkr_compiler::dag_ir::{bwd_roots, lower_dag, validate, BwdRegime, FieldKind, ReadPlace};
use gkr_eval_isa::bwd::distill::distill;
use gkr_eval_isa::bwd::source::{BwdSpecial, OriginLeaf};
use gkr_eval_isa::eval_plan::compile_backward_fragments_uncached;
use gkr_eval_isa::fwd::binding::{BackingKey, BackingTable};
use gkr_eval_isa::fwd::compile::{build_cross_layer_field_map, compile_circuit};
use gkr_eval_isa::fwd::isa::{Instr, OperandField, OperandLine, Program};

const WINDOW_COLUMNS: usize = 128;
const MAX_WINDOWS: usize = 64;

/// The field component is needed only for logical output/cache matrices; the
/// four base-only backing families never have an extension-field matrix.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum SourceField {
    Base,
    Ext,
}

impl From<OperandField> for SourceField {
    fn from(field: OperandField) -> Self {
        match field {
            OperandField::Base => Self::Base,
            OperandField::Ext => Self::Ext,
        }
    }
}

impl From<FieldKind> for SourceField {
    fn from(field: FieldKind) -> Self {
        match field {
            FieldKind::Base => Self::Base,
            FieldKind::Ext => Self::Ext,
        }
    }
}

/// Logical DRAM matrix identity, deliberately matching `BackingKey`'s field
/// qualification for cross-layer and cache outputs.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum SourceFamily {
    BaseLayerMemory,
    BaseLayerWitness,
    Setup,
    Scratch,
    LayerOutput { layer: usize, field: SourceField },
    CacheOutput { layer: usize, field: SourceField },
}

fn family_from_backing(key: &BackingKey) -> SourceFamily {
    match key {
        BackingKey::BaseLayerMemory => SourceFamily::BaseLayerMemory,
        BackingKey::BaseLayerWitness => SourceFamily::BaseLayerWitness,
        BackingKey::Setup => SourceFamily::Setup,
        BackingKey::Scratch => SourceFamily::Scratch,
        BackingKey::LayerOutput { layer, field } => SourceFamily::LayerOutput {
            layer: *layer,
            field: (*field).into(),
        },
        BackingKey::CacheOutput { layer, field } => SourceFamily::CacheOutput {
            layer: *layer,
            field: (*field).into(),
        },
    }
}

fn family_from_read(
    place: &ReadPlace,
    cross_fields: &std::collections::HashMap<ReadPlace, FieldKind>,
) -> SourceFamily {
    match *place {
        ReadPlace::BaseLayerMemory { .. } => SourceFamily::BaseLayerMemory,
        ReadPlace::BaseLayerWitness { .. } => SourceFamily::BaseLayerWitness,
        ReadPlace::Setup { .. } => SourceFamily::Setup,
        ReadPlace::Scratch { .. } => SourceFamily::Scratch,
        ReadPlace::LayerOutput { layer, .. } => SourceFamily::LayerOutput {
            layer,
            field: cross_fields
                .get(place)
                .copied()
                .unwrap_or_else(|| panic!("missing cross-layer field for {place:?}"))
                .into(),
        },
        ReadPlace::CacheOutput { layer, .. } => SourceFamily::CacheOutput {
            layer,
            field: cross_fields
                .get(place)
                .copied()
                .unwrap_or_else(|| panic!("missing cross-layer field for {place:?}"))
                .into(),
        },
    }
}

fn read_column(place: &ReadPlace) -> usize {
    match *place {
        ReadPlace::BaseLayerMemory { column }
        | ReadPlace::BaseLayerWitness { column }
        | ReadPlace::Setup { column } => column,
        ReadPlace::Scratch { slot } => slot,
        ReadPlace::LayerOutput { offset, .. } | ReadPlace::CacheOutput { offset, .. } => offset,
    }
}

fn visit_operands(program: &Program, mut visit: impl FnMut(&OperandLine)) {
    for instr in &program.instrs {
        match instr {
            Instr::Mov {
                src: Some(operand), ..
            } => visit(operand),
            Instr::Mov { src: None, .. } => {}
            Instr::Add { operands, .. } | Instr::Mul { operands, .. } => {
                operands.iter().for_each(&mut visit);
            }
            Instr::Fma { pairs, .. } => {
                for (left, right) in pairs {
                    visit(left);
                    visit(right);
                }
            }
        }
    }
}

/// Reverse-map every `Global` operand actually used by this program.  The
/// reverse map supplies original (rather than dense slot-local) columns.
fn referenced_columns(
    program: &Program,
    backings: &BackingTable,
) -> BTreeMap<SourceFamily, BTreeSet<usize>> {
    let mut columns = BTreeMap::new();
    visit_operands(program, |operand| {
        let OperandLine::Global { slot, col } = operand else {
            return;
        };
        let place = backings
            .slot_col_to_read_place(*slot, *col)
            .unwrap_or_else(|| panic!("unknown Global source slot={slot} col={col}"));
        let family = family_from_backing(
            backings
                .backing(*slot)
                .unwrap_or_else(|| panic!("unknown Global source slot={slot}")),
        );
        columns
            .entry(family)
            .or_insert_with(BTreeSet::new)
            .insert(read_column(&place));
    });
    columns
}

fn record_read_origin(
    columns: &mut BTreeMap<SourceFamily, BTreeSet<usize>>,
    place: &ReadPlace,
    cross_fields: &std::collections::HashMap<ReadPlace, FieldKind>,
) {
    columns
        .entry(family_from_read(place, cross_fields))
        .or_insert_with(BTreeSet::new)
        .insert(read_column(place));
}

/// Minimum number of freely positioned contiguous source windows required for
/// the sorted columns.  A window starts at the first uncovered column and
/// spans that column through `WINDOW_COLUMNS - 1` following columns.
fn window_count(columns: impl IntoIterator<Item = usize>) -> usize {
    let mut columns: Vec<_> = columns.into_iter().collect();
    columns.sort_unstable();
    columns.dedup();

    let mut windows = 0;
    let mut next_uncovered = None;
    for column in columns {
        if next_uncovered.is_none_or(|end| column > end) {
            windows += 1;
            next_uncovered = Some(column + WINDOW_COLUMNS - 1);
        }
    }
    windows
}

fn source_windows(columns: &BTreeMap<SourceFamily, BTreeSet<usize>>) -> usize {
    columns
        .values()
        .map(|family_columns| window_count(family_columns.iter().copied()))
        .sum()
}

/// The committed forward corpus: 11 scheduled layouts, each compiled at its
/// committed b16 (= four extension-field cells) program budget.
const FORWARD_FIXTURES: &[&str] = &[
    "add_sub_lui_auipc_mop_layout_gkr.json",
    "bigint_with_extended_control_layout_gkr.json",
    "blake2_g_function_layout_gkr.json",
    "blake2_with_extended_control_layout_gkr.json",
    "inits_and_teardowns_preprocessed_layout_gkr.json",
    "jump_branch_slt_layout_gkr.json",
    "keccak_special5_layout_gkr.json",
    "mem_subword_only_layout_gkr.json",
    "mem_word_only_layout_gkr.json",
    "shift_binop_layout_gkr.json",
    "unsigned_mul_div_layout_gkr.json",
];

/// Every fixture used by the backward compiler corpus; the final unified
/// machine has no committed forward schedule and is therefore backward-only.
const BACKWARD_FIXTURES: &[&str] = &[
    "add_sub_lui_auipc_mop_layout_gkr.json",
    "bigint_with_extended_control_layout_gkr.json",
    "blake2_g_function_layout_gkr.json",
    "blake2_with_extended_control_layout_gkr.json",
    "inits_and_teardowns_preprocessed_layout_gkr.json",
    "jump_branch_slt_layout_gkr.json",
    "keccak_special5_layout_gkr.json",
    "mem_subword_only_layout_gkr.json",
    "mem_word_only_layout_gkr.json",
    "shift_binop_layout_gkr.json",
    "unsigned_mul_div_layout_gkr.json",
    "unified_reduced_machine_layout_gkr.json",
];

#[test]
fn source_window_cover_cases() {
    assert_eq!(window_count([0]), 1);
    assert_eq!(window_count([0, 127]), 1);
    assert_eq!(window_count([1, 128]), 1); // freely based window, not 128-aligned
    assert_eq!(window_count([0, 128]), 2);
    assert_eq!(window_count([0, 127, 128, 255]), 2);
}

#[test]
fn source_window_corpus_census() {
    let mut maximum = 0usize;
    let mut forward_programs = 0usize;
    let mut backward_programs = 0usize;
    let mut backward_fixture_entries = 0usize;
    let mut backward_bearing_layers = 0usize;
    let mut backward_rootless_layers = 0usize;

    println!("{:<62} {:>7}", "program", "windows");
    for name in FORWARD_FIXTURES {
        let (dag, schedule, artifact) = load_dag_sched(name);
        let compiled = compile_circuit(&dag, &schedule, &artifact)
            .unwrap_or_else(|error| panic!("{name}: forward compile: {error:?}"));
        assert_eq!(
            compiled.budget, 16,
            "{name}: expected committed four-cell budget"
        );
        for (layer, program) in compiled.layers.iter().enumerate() {
            let windows =
                source_windows(&referenced_columns(&program.program, &program.ctx.backings));
            println!("{name} L{layer:<3} forward {:>7}", windows);
            maximum = maximum.max(windows);
            forward_programs += 1;
            assert!(
                windows <= MAX_WINDOWS,
                "{name} L{layer} forward: {windows} windows > {MAX_WINDOWS}"
            );
        }
    }

    for name in BACKWARD_FIXTURES {
        backward_fixture_entries += 1;
        let artifact = common::load_fixture(name);
        let dag = lower_dag(&artifact).unwrap_or_else(|error| panic!("{name}: lower_dag: {error}"));
        validate(&dag).unwrap_or_else(|error| panic!("{name}: validate: {error}"));
        let cross = build_cross_layer_field_map(&dag);
        let mut fixture_bearing_layers = 0usize;
        let mut fixture_rootless_layers = 0usize;
        for (layer, canonical) in dag.layers.iter().enumerate() {
            if bwd_roots(canonical).is_empty() {
                fixture_rootless_layers += 1;
                backward_rootless_layers += 1;
                println!("{name} L{layer:<3} rootless");
                continue;
            }
            fixture_bearing_layers += 1;
            backward_bearing_layers += 1;
            for regime in [BwdRegime::R0, BwdRegime::Ext] {
                let distilled = distill(canonical, regime, &cross, None);
                assert!(
                    !distilled.skipped_decoder,
                    "{name} L{layer} {regime:?}: decoder-bearing backward layer"
                );
                let compiled = compile_backward_fragments_uncached(&distilled, None, 4, false)
                    .unwrap_or_else(|error| {
                        panic!("{name} L{layer} {regime:?}: four-cell no-cache compile: {error:?}")
                    });
                let mut columns =
                    referenced_columns(&compiled.compiled.program, &compiled.compiled.backings);
                visit_operands(&compiled.compiled.program, |operand| {
                    let OperandLine::Special { desc } = operand else {
                        return;
                    };
                    let Some(BwdSpecial::FoldSource {
                        origin: OriginLeaf::Read(place),
                    }) = compiled.compiled.specials.get(*desc)
                    else {
                        return;
                    };
                    record_read_origin(&mut columns, place, &distilled.cross_fields);
                });
                let windows = source_windows(&columns);
                println!("{name} L{layer:<3} {regime:?} {:>7}", windows);
                maximum = maximum.max(windows);
                backward_programs += 1;
                assert!(
                    windows <= MAX_WINDOWS,
                    "{name} L{layer} {regime:?}: {windows} windows > {MAX_WINDOWS}"
                );
            }
        }
        println!(
            "{name}: backward-bearing layers={fixture_bearing_layers}, rootless layers={fixture_rootless_layers}"
        );
        assert_eq!(
            fixture_bearing_layers + fixture_rootless_layers,
            dag.layers.len(),
            "{name}: every layer must be explicitly classified for backward coverage"
        );
        assert!(
            fixture_bearing_layers > 0,
            "{name}: fixture unexpectedly contains no backward-bearing layers"
        );
    }

    println!("corpus maximum: {maximum} source windows (cap {MAX_WINDOWS})");
    println!(
        "backward coverage: {backward_fixture_entries} fixtures, {backward_bearing_layers} bearing layers, {backward_rootless_layers} rootless layers, {backward_programs} programs"
    );
    assert!(forward_programs > 0, "forward corpus contained no programs");
    assert!(
        backward_programs > 0,
        "backward corpus contained no programs"
    );
    assert_eq!(BACKWARD_FIXTURES.len(), 12, "backward fixture list drifted");
    assert_eq!(
        backward_fixture_entries,
        BACKWARD_FIXTURES.len(),
        "every pinned backward fixture must be processed"
    );
    assert_eq!(
        backward_bearing_layers, 57,
        "backward-bearing layer census drifted"
    );
    assert_eq!(
        backward_programs, 114,
        "every backward-bearing layer must compile in R0 and Ext"
    );
}
