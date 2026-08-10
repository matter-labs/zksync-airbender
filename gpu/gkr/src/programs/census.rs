use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::path::Path;
use std::sync::Arc;

use gkr_eval_ir::ReadPlace;
use gpu_core::primitives::field::BF;
use gpu_gkr_compiler::{
    encode_forward_program, parse_forward_artifact, CompiledLayer, ForwardDstLine, ForwardInstr,
    ForwardOperandField, ForwardOperandLine, ForwardSpecialStrategy,
};
use gpu_trace::witness::circuit_type::{
    CircuitType, DelegationCircuitType, UnrolledCircuitType, UnrolledMemoryCircuitType,
    UnrolledNonMemoryCircuitType,
};

use super::{forward_artifact, GkrPrograms};

#[derive(Clone, Copy)]
struct CircuitCase {
    name: &'static str,
    layout: &'static str,
    circuit_type: CircuitType,
}

fn circuit_cases() -> [CircuitCase; 12] {
    use DelegationCircuitType::*;
    use UnrolledCircuitType::*;
    use UnrolledMemoryCircuitType::*;
    use UnrolledNonMemoryCircuitType::*;

    [
        CircuitCase {
            name: "add_sub_lui_auipc_mop",
            layout: "add_sub_lui_auipc_mop_layout_gkr.json",
            circuit_type: CircuitType::Unrolled(NonMemory(AddSubLuiAuipcMop)),
        },
        CircuitCase {
            name: "jump_branch_slt",
            layout: "jump_branch_slt_layout_gkr.json",
            circuit_type: CircuitType::Unrolled(NonMemory(JumpBranchSlt)),
        },
        CircuitCase {
            name: "unsigned_mul_div",
            layout: "unsigned_mul_div_layout_gkr.json",
            circuit_type: CircuitType::Unrolled(NonMemory(MulDivUnsigned)),
        },
        CircuitCase {
            name: "shift_binop",
            layout: "shift_binop_layout_gkr.json",
            circuit_type: CircuitType::Unrolled(NonMemory(ShiftBinary)),
        },
        CircuitCase {
            name: "mem_word_only",
            layout: "mem_word_only_layout_gkr.json",
            circuit_type: CircuitType::Unrolled(Memory(LoadStoreWordOnly)),
        },
        CircuitCase {
            name: "mem_subword_only",
            layout: "mem_subword_only_layout_gkr.json",
            circuit_type: CircuitType::Unrolled(Memory(LoadStoreSubwordOnly)),
        },
        CircuitCase {
            name: "inits_and_teardowns",
            layout: "inits_and_teardowns_layout_gkr.json",
            circuit_type: CircuitType::Unrolled(InitsAndTeardowns),
        },
        CircuitCase {
            name: "unified_reduced_machine",
            layout: "unified_reduced_machine_layout_gkr.json",
            circuit_type: CircuitType::Unrolled(Unified),
        },
        CircuitCase {
            name: "bigint_with_extended_control",
            layout: "bigint_with_extended_control_layout_gkr.json",
            circuit_type: CircuitType::Delegation(BigIntWithControl),
        },
        CircuitCase {
            name: "keccak_special5",
            layout: "keccak_special5_layout_gkr.json",
            circuit_type: CircuitType::Delegation(KeccakSpecial5),
        },
        CircuitCase {
            name: "blake2_with_extended_control",
            layout: "blake2_with_extended_control_layout_gkr.json",
            circuit_type: CircuitType::Delegation(Blake2WithCompression),
        },
        CircuitCase {
            name: "blake2_g_function",
            layout: "blake2_g_function_layout_gkr.json",
            circuit_type: CircuitType::Delegation(Blake2GFunction),
        },
    ]
}

fn compile_case(case: CircuitCase) -> GkrPrograms {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../cs/compiled_circuits")
        .join(case.layout);
    let bytes = std::fs::read(&path)
        .unwrap_or_else(|error| panic!("failed to read {}: {error}", path.display()));
    let artifact: crate::upstream::GKRCircuitArtifact<BF> = serde_json::from_slice(&bytes)
        .unwrap_or_else(|error| panic!("failed to parse {}: {error}", path.display()));
    GkrPrograms::compile(case.circuit_type, Arc::new(artifact))
        .unwrap_or_else(|error| panic!("failed to compile {}: {error}", case.name))
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum LogicalBacking {
    BaseLayerMemory,
    BaseLayerWitness,
    Setup,
    Scratch,
    LayerOutput {
        layer: usize,
        field: ForwardOperandField,
    },
    CacheOutput {
        layer: usize,
        field: ForwardOperandField,
    },
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct LogicalSource {
    backing: LogicalBacking,
    column: usize,
}

fn required_windows(sources: &BTreeSet<LogicalSource>, column_bits: u8) -> usize {
    assert!((1..13).contains(&column_bits));
    let columns_per_window = 1usize << column_bits;
    let mut windows = 0usize;
    let mut active = None::<(LogicalBacking, usize)>;

    for source in sources {
        match active {
            Some((backing, first))
                if backing == source.backing
                    && source.column < first.saturating_add(columns_per_window) => {}
            _ => {
                windows += 1;
                active = Some((source.backing, source.column));
            }
        }
    }
    windows
}

fn logical_source(place: ReadPlace, field: ForwardOperandField) -> LogicalSource {
    let (backing, column) = match place {
        ReadPlace::BaseLayerMemory { column } => (LogicalBacking::BaseLayerMemory, column),
        ReadPlace::BaseLayerWitness { column } => (LogicalBacking::BaseLayerWitness, column),
        ReadPlace::Setup { column } => (LogicalBacking::Setup, column),
        ReadPlace::Scratch { slot } => (LogicalBacking::Scratch, slot),
        ReadPlace::LayerOutput { layer, offset } => {
            (LogicalBacking::LayerOutput { layer, field }, offset)
        }
        ReadPlace::CacheOutput { layer, offset } => {
            (LogicalBacking::CacheOutput { layer, field }, offset)
        }
    };
    LogicalSource { backing, column }
}

fn record_operand(
    layer: &CompiledLayer,
    operand: &ForwardOperandLine,
    sources: &mut BTreeSet<LogicalSource>,
) {
    let ForwardOperandLine::Source { window, column } = *operand else {
        return;
    };
    let field = layer
        .source_windows
        .source_field(window)
        .expect("compiled source window must have a field");
    let place = layer
        .source_windows
        .resolve_read_place(window, column)
        .expect("compiled source coordinate must resolve");
    sources.insert(logical_source(place, field));
}

fn collect_layer_sources(layer: &CompiledLayer) -> BTreeSet<LogicalSource> {
    let mut sources = BTreeSet::new();
    for instruction in &layer.program.instrs {
        match instruction {
            ForwardInstr::Add { operands, .. } | ForwardInstr::Mul { operands, .. } => {
                for operand in operands {
                    record_operand(layer, operand, &mut sources);
                }
            }
            ForwardInstr::Fma { pairs, .. } => {
                for (lhs, rhs) in pairs {
                    record_operand(layer, lhs, &mut sources);
                    record_operand(layer, rhs, &mut sources);
                }
            }
            ForwardInstr::Mov { src, .. } => {
                if let Some(source) = src {
                    record_operand(layer, source, &mut sources);
                }
            }
        }
    }
    sources
}

#[derive(Debug)]
struct LayerMetrics {
    instructions: usize,
    encoded_lanes: usize,
    sources: BTreeSet<LogicalSource>,
    compiler_windows: usize,
    destination_slots: usize,
    global_materializations: usize,
    base_materializations: usize,
    ext_materializations: usize,
    constants: usize,
    special_kinds: [usize; 6],
    arg_derived_e4: usize,
    const_derived_e4: usize,
    predicted_traffic: usize,
}

fn layer_metrics(layer: &CompiledLayer, predicted_traffic: usize) -> LayerMetrics {
    let mut destination_slots = BTreeSet::new();
    let mut global_materializations = 0;
    let mut base_materializations = 0;
    let mut ext_materializations = 0;
    for instruction in &layer.program.instrs {
        if let ForwardInstr::Mov {
            field,
            dst: Some(ForwardDstLine::GlobalMaterialize { slot, .. }),
            ..
        } = instruction
        {
            destination_slots.insert(*slot);
            global_materializations += 1;
            match field {
                ForwardOperandField::Base => base_materializations += 1,
                ForwardOperandField::Ext => ext_materializations += 1,
            }
        }
    }

    let mut special_kinds = [0usize; 6];
    for special in layer.specials.iter() {
        let kind = match special {
            ForwardSpecialStrategy::PeekSingleColumn { .. } => 0,
            ForwardSpecialStrategy::PeekAggregate { .. } => 1,
            ForwardSpecialStrategy::PeekSetup => 2,
            ForwardSpecialStrategy::PeekDecoder { .. } => 3,
            ForwardSpecialStrategy::VirtualSetup { .. } => 4,
            ForwardSpecialStrategy::InitsAndTeardownsTopBits { .. } => 5,
        };
        special_kinds[kind] += 1;
    }
    let const_derived_e4 =
        usize::from(layer.derived_e4.uses_lookup_additive()) + usize::from(special_kinds[3] != 0);

    LayerMetrics {
        instructions: layer.program.instrs.len(),
        encoded_lanes: encode_forward_program(&layer.program)
            .expect("compiled forward program must encode")
            .len(),
        sources: collect_layer_sources(layer),
        compiler_windows: layer.source_windows.len(),
        destination_slots: destination_slots.len(),
        global_materializations,
        base_materializations,
        ext_materializations,
        constants: layer.consts.values().len(),
        special_kinds,
        arg_derived_e4: layer.derived_e4.arg_refs().len(),
        const_derived_e4,
        predicted_traffic,
    }
}

fn split_field(sources: &BTreeSet<LogicalSource>, window_bits: u8) -> String {
    let column_bits = 13 - window_bits;
    let required = required_windows(sources, column_bits);
    let capacity = 1usize << window_bits;
    format!(
        "{window_bits}/{column_bits}:{required}/{capacity}:{}/{}",
        required * 12,
        capacity * 12,
    )
}

fn special_kinds_field(counts: [usize; 6]) -> String {
    format!(
        "single={},aggregate={},setup={},decoder={},virtual={},inits={}",
        counts[0], counts[1], counts[2], counts[3], counts[4], counts[5]
    )
}

fn render_interval_row(
    out: &mut String,
    kind: &str,
    circuit: &str,
    start: usize,
    layers: &[LayerMetrics],
) {
    let end = start + layers.len();
    let mut sources = BTreeSet::new();
    let mut instructions = 0;
    let mut lanes = 0;
    let mut compiler_windows = 0;
    let mut destination_slots = 0;
    let mut materializations = 0;
    let mut base_materializations = 0;
    let mut ext_materializations = 0;
    let mut constants = 0;
    let mut special_kinds = [0usize; 6];
    let mut arg_derived_e4 = 0;
    let mut const_derived_e4 = 0;
    let mut predicted_traffic = 0;
    for layer in layers {
        sources.extend(layer.sources.iter().copied());
        instructions += layer.instructions;
        lanes += layer.encoded_lanes;
        compiler_windows += layer.compiler_windows;
        destination_slots += layer.destination_slots;
        materializations += layer.global_materializations;
        base_materializations += layer.base_materializations;
        ext_materializations += layer.ext_materializations;
        constants += layer.constants;
        for (total, count) in special_kinds.iter_mut().zip(layer.special_kinds) {
            *total += count;
        }
        arg_derived_e4 += layer.arg_derived_e4;
        const_derived_e4 += layer.const_derived_e4;
        predicted_traffic += layer.predicted_traffic;
    }

    let all_splits = (1..=12)
        .map(|window_bits| split_field(&sources, window_bits))
        .collect::<Vec<_>>()
        .join(";");
    writeln!(
        out,
        "{kind}\t{circuit}\t{start}\t{end}\t{}\t{instructions}\t{lanes}\t{}\t{compiler_windows}\t{}\t{destination_slots}\t{materializations}\t{base_materializations}\t{ext_materializations}\t{constants}\t{}\t{arg_derived_e4}\t{const_derived_e4}\t{predicted_traffic}\t{}\t{}\t{}\t{}\t{all_splits}",
        layers.len(),
        lanes * 2,
        sources.len(),
        special_kinds_field(special_kinds),
        split_field(&sources, 5),
        split_field(&sources, 6),
        split_field(&sources, 7),
        split_field(&sources, 8),
    )
    .unwrap();
}

fn render_all_circuit_census() -> String {
    let mut out = String::from(
        "kind\tcircuit\tstart\tend\tlayers\tinstructions\tencoded_lanes\tprogram_bytes\tcompiler_windows_sum\tunique_sources\tdestination_slots_sum\tmaterializations\tbase_materializations\text_materializations\tconstants\tspecial_kinds\targ_derived_e4\tconst_derived_e4\tpredicted_traffic\tw5c8\tw6c7\tw7c6\tw8c5\tall_splits\n",
    );
    for case in circuit_cases() {
        let programs = compile_case(case);
        let (artifact, _) = forward_artifact(case.circuit_type);
        let retained = parse_forward_artifact(artifact, "embedded census schedule")
            .expect("embedded forward schedule must parse");
        assert_eq!(programs.forward.layers.len(), retained.layers.len());
        let metrics = programs
            .forward
            .layers
            .iter()
            .zip(&retained.layers)
            .map(|(layer, schedule)| layer_metrics(layer, schedule.predicted_traffic))
            .collect::<Vec<_>>();

        for (layer_index, layer) in metrics.iter().enumerate() {
            render_interval_row(
                &mut out,
                "LAYER",
                case.name,
                layer_index,
                std::slice::from_ref(layer),
            );
        }
        for start in 0..metrics.len() {
            for end in start + 1..=metrics.len() {
                render_interval_row(&mut out, "INTERVAL", case.name, start, &metrics[start..end]);
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn split_evaluator_deduplicates_sources_and_repacks_each_backing() {
        let a = LogicalBacking::Setup;
        let b = LogicalBacking::BaseLayerMemory;
        let sources = BTreeSet::from([
            LogicalSource {
                backing: a,
                column: 0,
            },
            LogicalSource {
                backing: a,
                column: 31,
            },
            LogicalSource {
                backing: a,
                column: 32,
            },
            LogicalSource {
                backing: a,
                column: 63,
            },
            LogicalSource {
                backing: a,
                column: 64,
            },
            LogicalSource {
                backing: b,
                column: 0,
            },
            LogicalSource {
                backing: b,
                column: 0,
            },
        ]);

        assert_eq!(required_windows(&sources, 5), 4);
        assert_eq!(required_windows(&sources, 6), 3);
    }

    #[test]
    fn circuit_case_table_covers_every_embedded_forward_artifact() {
        let cases = circuit_cases();
        assert_eq!(cases.len(), 12);
        let names = cases.iter().map(|case| case.name).collect::<BTreeSet<_>>();
        assert_eq!(names.len(), 12);
    }

    #[test]
    #[ignore = "audit census compiles every embedded forward circuit"]
    fn current_split_reproduces_every_compiler_layer() {
        for case in circuit_cases() {
            let programs = compile_case(case);
            for (layer_index, layer) in programs.forward.layers.iter().enumerate() {
                let sources = collect_layer_sources(layer);
                assert_eq!(
                    required_windows(&sources, 7),
                    layer.source_windows.len(),
                    "{} layer {} does not reproduce the compiler 6/7 binding",
                    case.name,
                    layer_index,
                );
            }
        }
    }

    #[test]
    #[ignore = "prints the all-circuit audit census"]
    fn all_embedded_forward_circuits_emit_group_census() {
        let report = render_all_circuit_census();
        assert!(report.starts_with("kind\tcircuit\t"));
        assert_eq!(
            report
                .lines()
                .filter(|line| line.starts_with("INTERVAL\t"))
                .count(),
            173,
        );
        assert!(report.lines().count() < 500);
        print!("{report}");
    }
}
