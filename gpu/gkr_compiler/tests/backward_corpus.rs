use std::collections::BTreeMap;
use std::path::PathBuf;

use cs::definitions::{GKRAddress, OutputType};
use cs::gkr_compiler::GKRCircuitArtifact;
use field::proth120::Proth120;
use gkr_eval_ir::lower_dag;
use gpu_gkr_compiler::geometry::{validate_proth120, BackwardPrograms};
use gpu_gkr_compiler::{
    compile_continuations_with_model, compile_forward_with_model, compile_r0_with_model,
    lower_dr_window_program, lower_main_continuation_window_program, lower_main_tail_program,
    parse_forward_artifact, ElementModel, WindowCoefficientPlan, PR_MAIN_CONTINUATION_MASKS,
};

#[test]
fn proth120_unified_backward_programs_compile() {
    let directory = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../cs/compiled_circuits");
    let layout: GKRCircuitArtifact<Proth120> = serde_json::from_slice(
        &std::fs::read(directory.join("unified_reduced_machine_layout_gkr_proth120_2p21.json"))
            .unwrap(),
    )
    .unwrap();
    let dag = lower_dag(&layout).unwrap();
    let model = ElementModel::PROTH120;
    let name = "unified_reduced_machine_schedule_b4_gkr_proth120.json";
    let artifact =
        parse_forward_artifact(&std::fs::read(directory.join(name)).unwrap(), name).unwrap();
    let forward = compile_forward_with_model(&dag, &artifact, model).unwrap();
    let r0 = compile_r0_with_model(&dag, model).unwrap();
    let continuations = compile_continuations_with_model(&dag, model).unwrap();
    let windows: Vec<_> = continuations
        .layers
        .iter()
        .map(|layer| lower_main_continuation_window_program(layer).unwrap())
        .collect();
    let tails: Vec<_> = continuations
        .layers
        .iter()
        .map(lower_main_tail_program)
        .collect();
    let programs = BackwardPrograms {
        r0: &r0,
        continuations: &continuations,
        main_continuation_window: &windows,
        main_tail: &tails,
    };
    let report = validate_proth120(&dag, &forward, &programs, &layout)
        .unwrap_or_else(|failure| panic!("{failure}"));
    println!(
        "GKR_BACKWARD_GEOMETRY {}",
        serde_json::to_string(&report.backward_layers).unwrap()
    );
    assert_eq!(report.backward_layers.len(), 5);
    for program in &r0 {
        let sections = program.window.sections;
        assert!(sections.iter().all(|&end| end == sections[0]));
        assert!(program
            .window
            .coefficient_plans
            .iter()
            .all(|plan| !matches!(plan, WindowCoefficientPlan::LinearBasis { .. })));
    }
    let masks: std::collections::BTreeSet<u8> = windows
        .iter()
        .map(|window| u8::try_from(window.shape.bits()).unwrap())
        .collect();
    assert!(masks
        .iter()
        .all(|mask| PR_MAIN_CONTINUATION_MASKS.contains(mask)));
    assert!(continuations
        .layers
        .iter()
        .flat_map(|layer| &layer.coefficients.coefficients)
        .flat_map(|recipe| &recipe.terms)
        .any(|product| product.scalar > u128::from(u32::MAX)));

    let mut rows: BTreeMap<OutputType, [GKRAddress; 2]> = layout
        .global_output_map
        .iter()
        .map(|(output, inputs)| (*output, inputs.as_slice().try_into().unwrap()))
        .collect();
    let initial_layer = dag.layers.len();
    let dr_layers = layout.trace_len.trailing_zeros() as usize - 4;
    for offset in 0..dr_layers {
        let program = lower_dr_window_program(&rows).unwrap();
        assert_eq!(program.enabled_mask(), 0x1f);
        assert_eq!(program.source_count(), 10);
        let output_layer = initial_layer + offset + 1;
        rows = rows
            .keys()
            .enumerate()
            .map(|(index, output)| {
                (
                    *output,
                    [
                        GKRAddress::InnerLayer {
                            layer: output_layer,
                            offset: 2 * index,
                        },
                        GKRAddress::InnerLayer {
                            layer: output_layer,
                            offset: 2 * index + 1,
                        },
                    ],
                )
            })
            .collect();
    }
    assert_eq!(dr_layers, 17);
}
