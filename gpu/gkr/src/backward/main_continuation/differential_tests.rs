//! CPU-only production-corpus contract for the standalone continuation harness.
//!
//! GPU observations live in `tests.rs`, which drives the continuation binding,
//! launch, publication, and tail components directly. Nothing in this module is
//! reachable from `prove()` or the production backward scheduler.

use std::collections::BTreeSet;

use gpu_core::primitives::field::E4;

use crate::backward::{compile_corpus_layout, CONTINUATION_GOLDEN_CORPUS};
use crate::main_layer_execution_plan::{
    try_derive_main_layer_execution_plan, MainTailRoundBudget, LEGACY_MAIN_TAIL_MIN_ROUNDS,
};
use crate::{BackwardExecutionStrategy, GkrBackwardOptions};

#[derive(Clone, Debug, PartialEq, Eq)]
struct CorpusCensus {
    layouts: usize,
    layers: usize,
    coordinates: usize,
    topology_coordinates: usize,
    non_identity_coordinates: usize,
    folding_steps: Vec<usize>,
    start_rounds: Vec<usize>,
    masks: Vec<u16>,
    max_sources: usize,
    max_legacy_displacement: usize,
    publication_over_2gib: usize,
}

fn build_corpus_census() -> CorpusCensus {
    let mut folding_steps_seen = BTreeSet::new();
    let mut start_rounds_seen = BTreeSet::new();
    let mut masks_seen = BTreeSet::new();
    let mut layers = 0usize;
    let mut max_sources = 0usize;
    let mut max_legacy_displacement = 0usize;
    let mut non_identity_coordinates = 0usize;
    let mut publication_over_2gib = 0usize;

    for (layout, _) in CONTINUATION_GOLDEN_CORPUS {
        let (programs, layout_layers) = compile_corpus_layout(layout);
        let bundle = programs
            .resolve_main_continuation_window_programs()
            .expect("the retained Task 8 corpus must lower");
        let folding_steps = programs.runtime_circuit().trace_len.trailing_zeros() as usize;
        folding_steps_seen.insert(folding_steps);
        let plan = try_derive_main_layer_execution_plan(
            GkrBackwardOptions {
                windowed_r0: true,
                windowed_main_continuations: true,
                ..GkrBackwardOptions::default()
            },
            BackwardExecutionStrategy::WindowedR0,
            folding_steps,
            MainTailRoundBudget::AtLeast {
                min_tail_rounds: LEGACY_MAIN_TAIL_MIN_ROUNDS,
            },
        )
        .expect("the retained Task 8 corpus must have a continuation plan");
        start_rounds_seen
            .extend((0..usize::from(plan.window_count())).map(|index| 3 * (index + 1)));

        assert_eq!(bundle.layers.len(), layout_layers, "{layout}");
        for (layer, program) in bundle.layers.iter().enumerate() {
            layers += 1;
            masks_seen.insert(program.shape.bits());
            max_sources = max_sources.max(program.sources.len());
            let publication_bytes = program
                .sources
                .len()
                .checked_mul(1usize << (folding_steps - 3))
                .and_then(|elements| elements.checked_mul(std::mem::size_of::<E4>()))
                .expect("Task 8 publication bytes must fit usize");
            publication_over_2gib += usize::from(publication_bytes > 2usize << 30);

            let source_program = programs.continuation_layer(layer);
            let mut seen = vec![false; source_program.coefficients.sources.len()];
            let mut displaced = 0usize;
            for (published, column) in source_program
                .binding
                .windows
                .iter()
                .flat_map(|window| &window.columns)
                .enumerate()
            {
                let source = column.source as usize;
                assert!(source < seen.len(), "{layout} layer {layer}");
                assert!(!seen[source], "{layout} layer {layer} source {source}");
                seen[source] = true;
                displaced += usize::from(published != source);
            }
            assert!(seen.into_iter().all(|seen| seen), "{layout} layer {layer}");
            max_legacy_displacement = max_legacy_displacement.max(displaced);
            non_identity_coordinates += usize::from(displaced > 0);
        }
    }

    let start_rounds: Vec<_> = start_rounds_seen.into_iter().collect();
    CorpusCensus {
        layouts: CONTINUATION_GOLDEN_CORPUS.len(),
        layers,
        coordinates: layers,
        topology_coordinates: layers * start_rounds.len(),
        non_identity_coordinates,
        folding_steps: folding_steps_seen.into_iter().collect(),
        start_rounds,
        masks: masks_seen.into_iter().collect(),
        max_sources,
        max_legacy_displacement,
        publication_over_2gib,
    }
}

#[test]
fn cpu_standalone_differential_corpus_census_is_exact() {
    assert_eq!(
        build_corpus_census(),
        CorpusCensus {
            layouts: 12,
            layers: 57,
            coordinates: 57,
            topology_coordinates: 342,
            non_identity_coordinates: 23,
            folding_steps: vec![20, 22, 23, 24],
            start_rounds: vec![3, 6, 9, 12, 15, 18],
            masks: vec![0x00, 0x01, 0x03, 0x07, 0x13, 0x17, 0x1f],
            max_sources: 1_012,
            max_legacy_displacement: 174,
            publication_over_2gib: 4,
        }
    );
}
