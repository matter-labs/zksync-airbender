use std::{collections::HashSet, path::PathBuf};

use gpu_gkr_compiler::WINDOW_COEFFICIENT_BANK_BIAS;

use super::*;
use crate::{
    baby_bear::backward::window::coefficient_bank::{
        build_window_coefficient_bank, CoefficientBankChunks,
    },
    backward::window::{bank::family_read_place, binding::BWD_WINDOW_PROGRAM_WORD_CAP},
    upstream::GKRCircuitArtifact,
};

const CORPUS: &[&str] = &[
    "circuit_defs/unrolled_circuits/add_sub_lui_auipc_mop/generated/layout.json",
    "circuit_defs/bigint_with_control/generated/layout.json",
    "circuit_defs/blake2_g_function/generated/layout.json",
    "circuit_defs/blake2_with_compression/generated/layout.json",
    "circuit_defs/unrolled_circuits/inits_and_teardowns/generated/layout.json",
    "circuit_defs/unrolled_circuits/jump_branch_slt/generated/layout.json",
    "circuit_defs/keccak_special5/generated/layout.json",
    "circuit_defs/unrolled_circuits/load_store_subword_only/generated/layout.json",
    "circuit_defs/unrolled_circuits/load_store_word_only/generated/layout.json",
    "circuit_defs/unrolled_circuits/shift_binary/generated/layout.json",
    "circuit_defs/unrolled_circuits/unified_reduced_machine/generated/layout.json",
    "circuit_defs/unrolled_circuits/mul_div_unsigned/generated/layout.json",
];

#[test]
fn cpu_selected_r0_programs_and_banks_cover_corpus() {
    let directory = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut layers = 0;
    let mut expected_layers = 0;
    let mut families = [0; 3];
    for layout in CORPUS {
        let artifact: GKRCircuitArtifact<BF> =
            serde_json::from_slice(&std::fs::read(directory.join(layout)).unwrap()).unwrap();
        let dag = gkr_eval_ir::lower_dag(&artifact).unwrap();
        let selected = gpu_gkr_compiler::backward::compile_r0(&dag)
            .unwrap_or_else(|error| panic!("{layout}: {error}"));
        assert_eq!(selected.len(), dag.layers.len());
        expected_layers += dag.layers.len();
        for (layer, program) in selected.iter().enumerate() {
            let window = &program.window;
            check_partition_bindings(program);
            assert_eq!(window.layer, layer);
            assert_eq!(window.shape.bits() & !program.kernel.shape_mask(), 0);
            assert!(window.words.len() <= BWD_WINDOW_PROGRAM_WORD_CAP);
            if let Some(seed) = program.scalar_seed {
                assert!(seed >= WINDOW_COEFFICIENT_BANK_BIAS);
                assert!(
                    usize::from(seed - WINDOW_COEFFICIENT_BANK_BIAS)
                        < window.coefficient_plans.len()
                );
            }
            // Sources are canonical expression inputs, including the non-claim
            // cache roots at which claim-cone traversal stops. InnerLayer storage
            // uses the destination layer number; it is not the DAG's layer index.
            let mut inputs: HashSet<_> = dag.layers[layer]
                .sources
                .iter()
                .filter_map(|source| match source {
                    gkr_eval_ir::SourceKind::Read { place } => Some(*place),
                    _ => None,
                })
                .collect();
            for root in &dag.layers[layer].roots {
                if root.claim.is_none() {
                    if let Some(gkr_eval_ir::SinkInfo {
                        kind: gkr_eval_ir::SinkKind::Cache { layer, offset },
                        ..
                    }) = &root.materialize
                    {
                        inputs.insert(gkr_eval_ir::ReadPlace::CacheOutput {
                            layer: *layer,
                            offset: *offset,
                        });
                    }
                }
            }
            let used: HashSet<_> = window
                .source_lanes
                .iter()
                .map(|lane| u32::from(lane.source))
                .collect();
            let mut covered = HashSet::new();
            for source in &window.windows {
                for column in &source.columns {
                    if used.contains(&column.source) {
                        covered.insert(column.source);
                        if let Some(place) = family_read_place(source.family, column.column) {
                            assert!(
                                inputs.contains(&place),
                                "{layout} L{layer} reads a non-input {place:?}"
                            );
                        }
                    }
                }
            }
            assert_eq!(covered, used);
            let blob = build_window_coefficient_bank(&window.coefficient_plans, &[1; 64])
                .unwrap_or_else(|error| panic!("{layout} L{layer}: {error:?}"));
            let chunks = CoefficientBankChunks::build(&blob);
            chunks.assert_covers_bank();
            assert_eq!(
                chunks.num_coefficients() as usize,
                window.coefficient_plans.len() + usize::from(WINDOW_COEFFICIENT_BANK_BIAS)
            );
            let family = match program.kernel {
                Kernel::General3 => 0,
                Kernel::Unit4 => 1,
                Kernel::Tails4 => 2,
            };
            families[family] += 1;

            layers += 1;
        }
    }
    assert!(expected_layers > 0);
    assert_eq!(layers, expected_layers);
    assert!(
        families.iter().all(|count| *count > 0),
        "corpus must cover general, unit and tails bodies"
    );
}

fn check_partition_bindings(program: &R0WindowProgram) {
    use gpu_gkr_compiler::window::partition::policy::REQUESTED_PARTS;

    use crate::backward::window::binding::WindowAddressing;
    // A bijective synthetic lane map checks relocation, including non-identity
    // source words. No pointer in this CPU descriptor is dereferenced.
    let addressing = WindowAddressing {
        slots: (0..64)
            .map(|i| crate::backward::window::common::BwdSourceWindow {
                base: (0x1000usize + (i << 12)) as *const u8,
                log2_stride: 8,
                origin: if i % 2 == 0 { 0 } else { 1 },
                procedural_kind: 0xff,
                reserved: 0,
                r0_stride_bytes: if i % 2 == 0 { 1024 } else { 4096 },
            })
            .collect(),
        lanes: (0..program.window.source_slots.len())
            .map(|i| {
                assert!(i < 8192);
                Some((((i % 64) << 7) | (i / 64)) as u16)
            })
            .collect(),
    };
    let scratch = WindowRuntimeScratch {
        eq_low: std::ptr::null(),
        partials: std::ptr::null_mut(),
        partials_capacity: 27 * (REQUESTED_PARTS[REQUESTED_PARTS.len() - 1] * 65536 + 1),
    };
    for plan in &program.partition_candidates.plans {
        let (bound, bounds) =
            partition::bind_addressed(&program.window, plan, &addressing, 24, scratch).unwrap();
        assert_eq!(bound.sections, program.window.sections);
        for (actual, expected) in bound.slot.iter().zip(&addressing.slots) {
            assert_eq!(actual.base, expected.base);
            assert_eq!(actual.log2_stride, expected.log2_stride);
            assert_eq!(actual.origin, expected.origin);
            assert_eq!(actual.procedural_kind, expected.procedural_kind);
            assert_eq!(actual.r0_stride_bytes, expected.r0_stride_bytes);
        }
        let mut at = 0;
        for (part_index, part) in plan.parts.iter().enumerate() {
            let mut expected = part.words.clone();
            for lane in &part.source_lanes {
                expected[lane.word as usize] = addressing.lanes[lane.source as usize].unwrap();
            }
            assert_eq!(&bound.program[at..at + expected.len()], expected);
            if let Some(bounds) = bounds {
                for section in 0..4 {
                    assert_eq!(
                        bounds.ends[part_index][section],
                        (at / 4) as u32 + part.sections[section]
                    );
                }
                assert_eq!(bounds.parts as usize, plan.parts.len());
            } else {
                assert_eq!(plan.parts.len(), 1);
            }
            at += expected.len();
            assert_eq!(part.coefficient_plans, program.window.coefficient_plans);
        }
        assert_eq!(at, program.window.words.len());
        assert!(bound.program[at..].iter().all(|&word| word == 0));
    }
}
