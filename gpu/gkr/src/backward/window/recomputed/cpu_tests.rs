use super::*;
use crate::backward::window::bank::family_read_place;
use crate::backward::window::binding::BWD_WINDOW_PROGRAM_WORD_CAP;
use crate::backward::window::coefficient_bank::{
    build_window_coefficient_bank, CoefficientBankChunks,
};
use crate::upstream::GKRCircuitArtifact;
use gpu_gkr_compiler::WINDOW_COEFFICIENT_BANK_BIAS;
use std::collections::HashSet;
use std::path::PathBuf;

const CORPUS: &[&str] = &[
    "add_sub_lui_auipc_mop_layout_gkr.json",
    "bigint_with_extended_control_layout_gkr.json",
    "blake2_g_function_layout_gkr.json",
    "blake2_with_extended_control_layout_gkr.json",
    "inits_and_teardowns_layout_gkr.json",
    "jump_branch_slt_layout_gkr.json",
    "keccak_special5_layout_gkr.json",
    "mem_subword_only_layout_gkr.json",
    "mem_word_only_layout_gkr.json",
    "shift_binop_layout_gkr.json",
    "unified_reduced_machine_layout_gkr.json",
    "unsigned_mul_div_layout_gkr.json",
];

#[test]
fn cpu_selected_recomputed_programs_and_banks_cover_corpus() {
    let directory = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../cs/compiled_circuits");
    let mut layers = 0;
    let mut expected_layers = 0;
    let mut families = [0; 3];
    for layout in CORPUS {
        let artifact: GKRCircuitArtifact<BF> =
            serde_json::from_slice(&std::fs::read(directory.join(layout)).unwrap()).unwrap();
        let dag = gkr_eval_ir::lower_dag(&artifact).unwrap();
        let selected = gpu_gkr_compiler::backward::recomputed_r0::compile_recomputed_r0(&dag)
            .unwrap_or_else(|error| panic!("{layout}: {error}"));
        assert_eq!(selected.len(), dag.layers.len());
        expected_layers += dag.layers.len();
        for (layer, program) in selected.iter().enumerate() {
            let window = &program.window;
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
                Kernel::Recomputed3 => 0,
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
