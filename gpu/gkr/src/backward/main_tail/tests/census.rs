use std::collections::BTreeMap;

use gkr_eval_ir::FieldKind;
use gpu_gkr_compiler::{CoefficientRecipeId, LEAN_MAX_IMMEDIATES, SOURCE_WINDOW_COLUMNS};

use super::super::{
    lower_main_tail_program, MainTailProgramError, MAIN_TAIL_BLOB_ALIGNMENT, MAIN_TAIL_BLOB_BYTES,
    MAIN_TAIL_IMMEDIATE_CAPACITY, MAIN_TAIL_IMMEDIATE_OFFSET, MAIN_TAIL_K, MAIN_TAIL_LIST_OFFSETS,
    MAIN_TAIL_LIST_OFFSETS_OFFSET, MAIN_TAIL_PROGRAM_OFFSET, MAIN_TAIL_PROGRAM_WORD_CAPACITY,
    MAIN_TAIL_SOURCE_CAPACITY,
};
use crate::backward::vm::continuation_golden::ContinuationRoundDto;
use crate::backward::{
    compile_corpus_layout, continuation_golden_path, decode_golden, CONTINUATION_GOLDEN_CORPUS,
};
use crate::main_layer_execution_plan::{try_derive_main_layer_execution_plan, MainTailRoundBudget};
use crate::{BackwardExecutionStrategy, GkrBackwardOptions, MainLayerExecutionPlanError};

fn enabled_options() -> GkrBackwardOptions {
    GkrBackwardOptions {
        windowed_main_continuations: true,
        ..GkrBackwardOptions::default()
    }
}

fn dense_publication_cardinality(round: &ContinuationRoundDto) -> Result<usize, String> {
    let source_count = round.sources.len();
    if round.folding_buffer_columns as usize != source_count
        || usize::from(round.num_foldable) != source_count
    {
        return Err("publication cardinalities disagree".to_owned());
    }
    let column_bytes = (round.folding_buffer_column_elems as usize)
        .checked_mul(size_of::<gpu_core::primitives::field::E4>())
        .ok_or_else(|| "publication column byte count overflowed".to_owned())?;
    let mut columns = Vec::with_capacity(source_count);
    for source in &round.sources {
        let patch = round
            .folding_buffer_patches
            .iter()
            .find(|patch| {
                patch.slot == source.publish_slot && patch.buffer_round == round.absolute_round
            })
            .ok_or_else(|| "published source has no current-round slot patch".to_owned())?;
        let byte_offset = patch.byte_offset as usize;
        if !byte_offset.is_multiple_of(column_bytes * SOURCE_WINDOW_COLUMNS) {
            return Err("publication slot patch is not chunk-aligned".to_owned());
        }
        let first_column = byte_offset / column_bytes;
        columns.push(first_column + source.publish_column as usize);
    }
    columns.sort_unstable();
    if columns != (0..source_count).collect::<Vec<_>>() {
        return Err("publication columns are not a dense permutation".to_owned());
    }
    Ok(source_count)
}

#[test]
fn cpu_main_tail_entry_census_matches_golden() {
    let bytes = std::fs::read(continuation_golden_path()).unwrap();
    let entries = decode_golden(&bytes).unwrap();
    assert_eq!(entries.len(), 57);

    let mut folding_steps_distribution = BTreeMap::new();
    let mut start_distribution = BTreeMap::new();
    let mut maximum_entry_bytes = 0usize;
    let mut maximum_sources = 0usize;

    for entry in &entries {
        let folding_steps = entry.dto.folding_steps as usize;
        *folding_steps_distribution
            .entry(folding_steps)
            .or_insert(0usize) += 1;
        let plan = try_derive_main_layer_execution_plan(
            enabled_options(),
            BackwardExecutionStrategy::WindowedR0,
            folding_steps,
            MainTailRoundBudget::AtMost { max_tail_rounds: 6 },
        )
        .unwrap();
        let tail_start = usize::from(plan.tail_start_round());
        *start_distribution.entry(tail_start).or_insert(0usize) += 1;
        assert_eq!(
            (
                folding_steps,
                usize::from(plan.window_count()),
                tail_start,
                folding_steps - tail_start
            ),
            match folding_steps {
                20 => (20, 4, 15, 5),
                22 => (22, 5, 18, 4),
                23 => (23, 5, 18, 5),
                24 => (24, 5, 18, 6),
                other => panic!("unruled folding-step count {other}"),
            }
        );

        let publication_round = entry
            .dto
            .rounds
            .iter()
            .find(|round| usize::from(round.absolute_round) == tail_start - 3)
            .expect("golden must carry the window that publishes the tail entry");
        let source_count = dense_publication_cardinality(publication_round).unwrap();
        let entry_bytes = source_count
            .checked_mul(publication_round.folding_buffer_column_elems as usize)
            .and_then(|elements| elements.checked_mul(size_of::<gpu_core::primitives::field::E4>()))
            .unwrap();
        maximum_entry_bytes = maximum_entry_bytes.max(entry_bytes);
        maximum_sources = maximum_sources.max(source_count);
    }

    assert_eq!(
        folding_steps_distribution,
        BTreeMap::from([(20, 8), (22, 17), (23, 4), (24, 28)])
    );
    assert_eq!(start_distribution, BTreeMap::from([(15, 8), (18, 49)]));
    assert_eq!(maximum_sources, 1_012);
    assert_eq!(maximum_entry_bytes, 4_145_152);

    let mut mutated = entries[0]
        .dto
        .rounds
        .iter()
        .find(|round| round.absolute_round == 15)
        .expect("the selected corpus entry publishes at round 15")
        .clone();
    assert!(mutated.sources.len() > 1);
    let (first, duplicate) = mutated
        .sources
        .iter()
        .enumerate()
        .find_map(|(first, source)| {
            mutated
                .sources
                .iter()
                .enumerate()
                .find(|(second, candidate)| {
                    *second != first && candidate.publish_slot == source.publish_slot
                })
                .map(|(second, _)| (first, second))
        })
        .expect("the publication uses at least two columns of one slot");
    mutated.sources[first].publish_column = mutated.sources[duplicate].publish_column;
    assert!(dense_publication_cardinality(&mutated).is_err());
}

#[test]
fn cpu_main_tail_program_has_fixed_blob_layout_and_dealt_k8_program() {
    assert_eq!(MAIN_TAIL_K, 8);
    assert_eq!(MAIN_TAIL_LIST_OFFSETS, 9);
    assert_eq!(MAIN_TAIL_LIST_OFFSETS_OFFSET, 0);
    assert_eq!(MAIN_TAIL_PROGRAM_OFFSET, 18);
    assert_eq!(MAIN_TAIL_PROGRAM_WORD_CAPACITY, 6_472);
    assert_eq!(MAIN_TAIL_IMMEDIATE_OFFSET, 12_964);
    assert_eq!(MAIN_TAIL_IMMEDIATE_CAPACITY, 512);
    assert_eq!(MAIN_TAIL_BLOB_BYTES, 15_024);
    assert_eq!(MAIN_TAIL_BLOB_BYTES % MAIN_TAIL_BLOB_ALIGNMENT, 0);
    assert_eq!(MAIN_TAIL_IMMEDIATE_CAPACITY, LEAN_MAX_IMMEDIATES);
    assert_eq!(MAIN_TAIL_SOURCE_CAPACITY, 1_072);

    let (programs, _) = compile_corpus_layout("add_sub_lui_auipc_mop_layout_gkr.json");
    let source = programs.continuation_layer(0);
    let lowered = lower_main_tail_program(source).unwrap();
    assert_eq!(lowered.layer, source.layer);
    assert_eq!(lowered.k, MAIN_TAIL_K as u8);
    assert_eq!(lowered.list_offsets[0], 0);
    assert_eq!(
        usize::from(lowered.list_offsets[MAIN_TAIL_K]),
        lowered.program_words.len()
    );
    assert!(lowered
        .list_offsets
        .windows(2)
        .all(|pair| pair[0] <= pair[1]));
    assert_eq!(
        lowered.source_count as usize,
        source.coefficients.sources.len()
    );
    assert_eq!(
        lowered.coefficient_count as usize,
        CoefficientRecipeId::RESERVED as usize + source.coefficient_recipes.len()
    );
    assert_eq!(lowered.immediates, source.immediates);
}

#[test]
fn cpu_main_tail_program_capacity_failures_are_typed() {
    let (programs, _) = compile_corpus_layout("add_sub_lui_auipc_mop_layout_gkr.json");
    let template = programs.continuation_layer(0);

    let mut words = template.clone();
    words
        .program
        .words
        .resize(MAIN_TAIL_PROGRAM_WORD_CAPACITY + 1, 0);
    assert_eq!(
        lower_main_tail_program(&words),
        Err(MainTailProgramError::ProgramWordsCapacity {
            required: MAIN_TAIL_PROGRAM_WORD_CAPACITY + 1,
            maximum: MAIN_TAIL_PROGRAM_WORD_CAPACITY,
        })
    );

    let mut immediates = template.clone();
    immediates
        .immediates
        .resize(MAIN_TAIL_IMMEDIATE_CAPACITY, 0);
    assert!(lower_main_tail_program(&immediates).is_ok());
    immediates.immediates.push(0);
    assert_eq!(
        lower_main_tail_program(&immediates),
        Err(MainTailProgramError::ImmediateCapacity {
            required: MAIN_TAIL_IMMEDIATE_CAPACITY + 1,
            maximum: MAIN_TAIL_IMMEDIATE_CAPACITY,
        })
    );

    let mut sources = template.clone();
    let slot = sources.binding.source_slots[0].clone();
    sources
        .binding
        .source_slots
        .resize(MAIN_TAIL_SOURCE_CAPACITY + 1, slot);
    assert_eq!(
        lower_main_tail_program(&sources),
        Err(MainTailProgramError::SourceCapacity {
            required: MAIN_TAIL_SOURCE_CAPACITY + 1,
            maximum: MAIN_TAIL_SOURCE_CAPACITY,
        })
    );
}

#[test]
fn cpu_main_tail_program_rejects_undefined_noncanonical_and_non_e4_sources() {
    let (programs, _) = compile_corpus_layout("add_sub_lui_auipc_mop_layout_gkr.json");
    let template = programs.continuation_layer(0);
    assert!(template.binding.source_slots.len() > 1);

    let mut undefined = template.clone();
    undefined.binding.source_slots[0].window = u8::MAX;
    assert!(matches!(
        lower_main_tail_program(&undefined),
        Err(MainTailProgramError::UndefinedSource { source: 0, .. })
    ));

    let mut noncanonical = template.clone();
    noncanonical.binding.source_slots.swap(0, 1);
    assert!(matches!(
        lower_main_tail_program(&noncanonical),
        Err(MainTailProgramError::NonCanonicalSource {
            expected: 0,
            found: 1
        })
    ));

    let mut wrong_field = template.clone();
    wrong_field.coefficients.sources[0].field = FieldKind::Base;
    assert_eq!(
        lower_main_tail_program(&wrong_field),
        Err(MainTailProgramError::NonExtensionSource { source: 0 })
    );

    let mut zero_windows = template.clone();
    zero_windows.binding.windows.clear();
    assert_eq!(
        lower_main_tail_program(&zero_windows),
        Err(MainTailProgramError::ZeroSourceWindows)
    );

    let mut bad_c_init = template.clone();
    bad_c_init.c_init = Some(CoefficientRecipeId(u32::MAX));
    assert!(matches!(
        lower_main_tail_program(&bad_c_init),
        Err(MainTailProgramError::InvalidCInit { .. })
    ));
}

#[test]
fn cpu_main_tail_program_policy_negative_paths_are_typed() {
    assert!(matches!(
        try_derive_main_layer_execution_plan(
            enabled_options(),
            BackwardExecutionStrategy::WindowedR0,
            6,
            MainTailRoundBudget::AtMost { max_tail_rounds: 6 },
        ),
        Err(MainLayerExecutionPlanError::TailBudgetCannotBeSatisfied { .. })
    ));
    assert_eq!(
        try_derive_main_layer_execution_plan(
            enabled_options(),
            BackwardExecutionStrategy::WindowedR0,
            24,
            MainTailRoundBudget::AtMost { max_tail_rounds: 0 },
        ),
        Err(MainLayerExecutionPlanError::ZeroTailRoundBudget)
    );
}

#[test]
fn cpu_main_tail_program_bundle_caches_success_and_typed_rejection() {
    let (programs, layers) = compile_corpus_layout("add_sub_lui_auipc_mop_layout_gkr.json");
    assert!(!programs.main_tail_programs_ready());
    let first = programs.resolve_main_tail_programs().unwrap();
    let second = programs.resolve_main_tail_programs().unwrap();
    assert!(std::ptr::eq(first, second));
    assert_eq!(first.layers.len(), layers);
    assert!(programs.main_tail_programs_ready());

    let (mut rejected, _) = compile_corpus_layout("add_sub_lui_auipc_mop_layout_gkr.json");
    rejected.continuations.layers[0].binding.windows.clear();
    assert!(!rejected.main_tail_programs_ready());
    let first = rejected.resolve_main_tail_programs().unwrap_err();
    let second = rejected.resolve_main_tail_programs().unwrap_err();
    assert!(std::ptr::eq(first, second));
    assert_eq!(first.layer, 0);
    assert!(first.resource.contains("source windows"));
    assert!(!rejected.main_tail_programs_ready());
}

/// D2 proof for the canonical repoint gate: on the full corpus, every layer's
/// SourceId-ordered addresses — reads and virtual-setup sources alike — are
/// exactly the layer's final-evaluation inputs, every source owns its dense
/// publication column, and the map is duplicate-free. Both sides are compared
/// raw; production logicalizes both through the same map, which preserves set
/// equality.
#[test]
fn cpu_main_tail_canonical_final_addresses_cover_corpus() {
    use crate::backward::vm::production_bind::virtual_setup_poly_address;
    use crate::forward::vm::lower::read_place_to_gkr_address;
    use crate::upstream::GKRAddress;
    use gpu_gkr_compiler::CanonicalSourceIdentity;
    use std::collections::BTreeSet;

    let mut layers_checked = 0usize;
    let mut virtual_sources_seen = 0usize;
    for (layout, _) in CONTINUATION_GOLDEN_CORPUS {
        let (programs, layers) = compile_corpus_layout(layout);
        let bundle = programs
            .resolve_main_continuation_window_programs()
            .unwrap();
        assert_eq!(bundle.layers.len(), layers);
        for (layer_idx, window_program) in bundle.layers.iter().enumerate() {
            let identities = window_program.canonical_source_identities();
            assert_eq!(identities.len(), window_program.sources.len());
            let entries: Vec<(usize, GKRAddress)> = identities
                .into_iter()
                .enumerate()
                .map(|(column, identity)| {
                    let address = match identity {
                        CanonicalSourceIdentity::Read(place) => read_place_to_gkr_address(&place),
                        CanonicalSourceIdentity::VirtualSetup { kind } => {
                            virtual_sources_seen += 1;
                            virtual_setup_poly_address(kind)
                        }
                    };
                    (column, address)
                })
                .collect();
            assert!(!entries.is_empty(), "{layout}/{layer_idx}: no sources");
            let columns: Vec<usize> = entries.iter().map(|(column, _)| *column).collect();
            assert_eq!(
                columns,
                (0..entries.len()).collect::<Vec<_>>(),
                "{layout}/{layer_idx}: every source must own its dense column"
            );
            let canonical: BTreeSet<GKRAddress> =
                entries.iter().map(|(_, address)| *address).collect();
            assert_eq!(
                canonical.len(),
                entries.len(),
                "{layout}/{layer_idx}: duplicate canonical address"
            );

            let inputs: BTreeSet<GKRAddress> = programs.backward_layers[layer_idx]
                .inputs
                .iter()
                .copied()
                .filter(|address| *address != GKRAddress::placeholder())
                .collect();
            assert_eq!(
                canonical, inputs,
                "{layout}/{layer_idx}: canonical source set must equal the final-evaluation inputs"
            );
            layers_checked += 1;
        }
    }
    assert_eq!(layers_checked, 57);
    assert!(
        virtual_sources_seen > 0,
        "the corpus must exercise virtual-setup columns in the canonical map"
    );
}

#[test]
fn cpu_main_tail_program_bundle_covers_the_full_corpus_and_source_maximum() {
    let mut coordinates = 0usize;
    let mut maximum_sources = 0usize;
    for (layout, _) in CONTINUATION_GOLDEN_CORPUS {
        let (programs, layers) = compile_corpus_layout(layout);
        let bundle = programs.resolve_main_tail_programs().unwrap();
        assert_eq!(bundle.layers.len(), layers);
        coordinates += layers;
        maximum_sources = maximum_sources.max(
            bundle
                .layers
                .iter()
                .map(|program| usize::from(program.source_count))
                .max()
                .unwrap(),
        );
    }
    assert_eq!(coordinates, 57);
    assert_eq!(maximum_sources, 1_012);
}
