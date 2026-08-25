use std::collections::{BTreeMap, BTreeSet};
use std::sync::OnceLock;

use crate::storage_layout::GpuGKRStorageLayout;
use crate::upstream::GKRAddress;

use super::super::main_layer::blueprints::build_dimension_reducing_slots_static;
use super::super::{
    compile_corpus_layout, derive_dimension_reducing_inputs, CONTINUATION_GOLDEN_CORPUS,
};
use super::capacity::{
    portable_entry, DrTailCapacityDecision, DrTailCapacityRejection, DrTailCapacityRequest,
};

const FINAL_TRACE_LOG: usize = 4;
const PLANNING_STATIC_SMEM_BYTES: usize = 8_192;
const PLANNING_DEVICE_CAP_BYTES: usize = 101_376;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct DrTailAddressOrder {
    pub(super) sorted_canonical: Vec<GKRAddress>,
    pub(super) sorted_canonical_publication: Vec<usize>,
    pub(super) raw_sorted: Vec<GKRAddress>,
    pub(super) raw_address_canonical_lookup: Vec<usize>,
    pub(super) rewritten_occurrences: usize,
    pub(super) canonical_merges: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct DrTailCensusRow {
    pub(super) layout_name: &'static str,
    pub(super) layer_idx: usize,
    pub(super) folding_steps: usize,
    pub(super) enabled_mask: u32,
    pub(super) capacity: DrTailCapacityDecision,
    pub(super) legal_capacities: Vec<(
        usize,
        Result<DrTailCapacityDecision, DrTailCapacityRejection>,
    )>,
    pub(super) order: DrTailAddressOrder,
}

#[derive(Clone, Debug)]
pub(super) struct DrTailCorpusCensus {
    pub(super) rows: Vec<DrTailCensusRow>,
    pub(super) mask_counts: BTreeMap<u32, usize>,
    pub(super) source_counts: BTreeMap<usize, usize>,
    pub(super) rewritten_occurrences: usize,
    pub(super) mismatch_layers: usize,
    pub(super) merge_layers: usize,
}

/// One production DR layer, resolved from the artifact tower.
///
/// This is the single producer of DR-tail per-layer planning inputs. Production
/// resource preflight and the 229-row corpus census both consume it, so the
/// census is a regression gate on the production selection rather than a
/// parallel derivation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct DrTailLayerInput {
    pub(super) layer_idx: usize,
    pub(super) folding_steps: usize,
    pub(super) entry_round: usize,
    pub(super) canonical_sources: usize,
    pub(super) enabled_mask: u32,
    pub(super) order: DrTailAddressOrder,
}

/// Resolve every production DR layer of `artifact` down to `final_trace_log_2`.
pub(super) fn dr_tail_layer_inputs<F: crate::upstream::PrimeField>(
    artifact: &crate::upstream::GKRCircuitArtifact<F>,
    final_trace_log_2: usize,
) -> Result<Vec<DrTailLayerInput>, DrTailCapacityRejection> {
    let trace_log = artifact.trace_len.trailing_zeros() as usize;
    let layout = GpuGKRStorageLayout::from_artifact_with_tower(artifact, final_trace_log_2);
    let tower = derive_dimension_reducing_inputs(
        artifact.layers.len(),
        &artifact.global_output_map,
        trace_log as u32,
        final_trace_log_2 as u32,
    );
    let mut inputs = Vec::with_capacity(tower.len());
    for (layer_idx, layer) in tower {
        let layer_offset = layer_idx - artifact.layers.len();
        let folding_steps = trace_log
            .checked_sub(layer_offset)
            .and_then(|value| value.checked_sub(1))
            .ok_or(DrTailCapacityRejection::ArithmeticOverflow)?;
        let slots = build_dimension_reducing_slots_static(&layer);
        let order = address_order(slots.input_addresses(), &layout.aliases);
        let entry_round = portable_entry(folding_steps)?;
        inputs.push(DrTailLayerInput {
            layer_idx,
            folding_steps,
            entry_round,
            canonical_sources: order.sorted_canonical.len(),
            enabled_mask: slots.enabled_mask(),
            order,
        });
    }
    Ok(inputs)
}

pub(super) fn address_order(
    raw_occurrences: impl IntoIterator<Item = GKRAddress>,
    aliases: &BTreeMap<GKRAddress, GKRAddress>,
) -> DrTailAddressOrder {
    let raw_occurrences: Vec<_> = raw_occurrences.into_iter().collect();
    let rewritten_occurrences = raw_occurrences
        .iter()
        .filter(|address| {
            aliases
                .get(address)
                .is_some_and(|canonical| canonical != *address)
        })
        .count();
    let raw_sorted: Vec<_> = raw_occurrences
        .iter()
        .copied()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    let sorted_canonical: Vec<_> = raw_sorted
        .iter()
        .map(|address| aliases.get(address).copied().unwrap_or(*address))
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    let raw_address_canonical_lookup = raw_sorted
        .iter()
        .map(|address| {
            let canonical = aliases.get(address).copied().unwrap_or(*address);
            sorted_canonical
                .binary_search(&canonical)
                .expect("canonical DR input must be present in the publication arena")
        })
        .collect();
    let sorted_canonical_publication = (0..sorted_canonical.len()).collect();
    let canonical_merges = raw_sorted.len() - sorted_canonical.len();

    DrTailAddressOrder {
        sorted_canonical,
        sorted_canonical_publication,
        raw_sorted,
        raw_address_canonical_lookup,
        rewritten_occurrences,
        canonical_merges,
    }
}

fn build_census() -> DrTailCorpusCensus {
    let mut rows = Vec::new();
    for (layout_name, _) in CONTINUATION_GOLDEN_CORPUS {
        let (programs, _) = compile_corpus_layout(layout_name);
        let artifact = programs.runtime_circuit();
        let inputs = dr_tail_layer_inputs(artifact.as_ref(), FINAL_TRACE_LOG)
            .unwrap_or_else(|error| panic!("{layout_name}: {error}"));
        for input in inputs {
            let DrTailLayerInput {
                layer_idx,
                folding_steps,
                entry_round,
                canonical_sources,
                enabled_mask,
                order,
            } = input;
            let legal_capacities = (3..folding_steps)
                .step_by(3)
                .map(|candidate| {
                    (
                        candidate,
                        DrTailCapacityRequest {
                            folding_steps,
                            entry_round: candidate,
                            canonical_sources,
                            static_smem_bytes: PLANNING_STATIC_SMEM_BYTES,
                            device_cap_bytes: PLANNING_DEVICE_CAP_BYTES,
                        }
                        .decide(),
                    )
                })
                .collect::<Vec<_>>();
            let capacity = DrTailCapacityRequest {
                folding_steps,
                entry_round,
                canonical_sources,
                static_smem_bytes: PLANNING_STATIC_SMEM_BYTES,
                device_cap_bytes: PLANNING_DEVICE_CAP_BYTES,
            }
            .decide()
            .unwrap_or_else(|error| panic!("{layout_name} layer {layer_idx}: {error}"));
            rows.push(DrTailCensusRow {
                layout_name,
                layer_idx,
                folding_steps,
                enabled_mask,
                capacity,
                legal_capacities,
                order,
            });
        }
    }
    rows.sort_by_key(|row| (row.layout_name, row.layer_idx));

    let mut mask_counts = BTreeMap::new();
    let mut source_counts = BTreeMap::new();
    let mut rewritten_occurrences = 0;
    let mut mismatch_layers = 0;
    let mut merge_layers = 0;
    for row in &rows {
        *mask_counts.entry(row.enabled_mask).or_default() += 1;
        *source_counts
            .entry(row.order.sorted_canonical.len())
            .or_default() += 1;
        rewritten_occurrences += row.order.rewritten_occurrences;
        mismatch_layers += usize::from(
            row.order.sorted_canonical_publication != row.order.raw_address_canonical_lookup,
        );
        merge_layers += usize::from(row.order.canonical_merges != 0);
    }

    let census = DrTailCorpusCensus {
        rows,
        mask_counts,
        source_counts,
        rewritten_occurrences,
        mismatch_layers,
        merge_layers,
    };
    assert_corpus_contract(&census);
    census
}

fn assert_corpus_contract(census: &DrTailCorpusCensus) {
    assert_eq!(census.rows.len(), 229, "DR-tail corpus layer count drifted");
    assert_eq!(
        census.mask_counts,
        BTreeMap::from([(0x01, 20), (0x0d, 52), (0x0f, 138), (0x1f, 19)]),
        "DR-tail enabled-mask census drifted",
    );
    assert_eq!(
        census.source_counts,
        BTreeMap::from([(2, 20), (6, 52), (8, 138), (10, 19)]),
        "DR-tail canonical-source census drifted",
    );
    assert_eq!(
        census.rewritten_occurrences, 42,
        "DR-tail alias rewrite census drifted"
    );
    assert_eq!(
        census.mismatch_layers, 9,
        "DR-tail publication/emission order census drifted"
    );
    assert_eq!(
        census.merge_layers, 0,
        "DR-tail canonical merge census drifted"
    );
}

pub(super) fn corpus_census() -> &'static DrTailCorpusCensus {
    static CENSUS: OnceLock<DrTailCorpusCensus> = OnceLock::new();
    CENSUS.get_or_init(build_census)
}

/// Returns the single source of truth for the first production layer whose
/// sorted-canonical publication order differs from the unchanged epilogue's
/// raw-address sort plus canonical lookup.
#[doc(hidden)]
pub fn dr_tail_first_order_mismatch() -> (&'static str, usize, Vec<usize>, Vec<usize>) {
    let row = corpus_census()
        .rows
        .iter()
        .find(|row| {
            row.order.sorted_canonical_publication != row.order.raw_address_canonical_lookup
        })
        .expect("the production DR corpus must retain an order-mismatch fixture");
    (
        row.layout_name,
        row.layer_idx,
        row.order.sorted_canonical_publication.clone(),
        row.order.raw_address_canonical_lookup.clone(),
    )
}
