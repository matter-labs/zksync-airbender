use std::collections::BTreeMap;
use std::sync::Arc;

use crate::storage_layout::{FieldType, GpuGKRLayerLayout, GpuGKRStorageLayout, StorageSlot};
use crate::upstream::{DimensionReducingInputOutput, Field, GKRAddress, OutputType, PrimeField};
use crate::{GpuExtensionFieldPoly, GpuGKRStorage};
use era_cudart::memory::memory_copy_async;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::field::{BF, E4};
use gpu_prover_context::ProverContext;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

pub(super) fn sample_ext(seed: u32) -> E4 {
    E4::from_array_of_base([
        BF::new(seed),
        BF::new(seed + 1),
        BF::new(seed + 2),
        BF::new(seed + 3),
    ])
}

pub(super) fn upload_ext_poly(values: &[E4], context: &ProverContext) -> GpuExtensionFieldPoly<E4> {
    let mut device = context
        .alloc(values.len(), AllocationPlacement::Top)
        .unwrap();
    memory_copy_async(&mut device, values, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    GpuExtensionFieldPoly::new(device)
}

pub(super) fn read_ext_poly(poly: &GpuExtensionFieldPoly<E4>, context: &ProverContext) -> Vec<E4> {
    let mut host = vec![E4::ZERO; poly.len()];
    memory_copy_async(&mut host, poly.as_device_slice(), context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    host
}

pub(super) fn attach_test_dim_reducing_tower_layout(
    storage: &mut GpuGKRStorage<BF, E4>,
    initial_layer_idx: usize,
    initial_output_map: &BTreeMap<OutputType, Vec<GKRAddress>>,
    initial_trace_log_2: u32,
    final_trace_log_2: u32,
) {
    use crate::gkr_address_audit::AddressClass;

    let trace_len = 1usize << initial_trace_log_2;
    let total_rounds = initial_trace_log_2.saturating_sub(final_trace_log_2);
    let total_layers = initial_layer_idx + total_rounds as usize + 1;
    let mut layers = vec![GpuGKRLayerLayout::default(); total_layers];

    let mut initial_layer_layout = GpuGKRLayerLayout {
        log2_stride: initial_trace_log_2,
        ..GpuGKRLayerLayout::default()
    };
    let mut initial_poly_count = 0u32;
    for input in initial_output_map.values().flatten() {
        initial_layer_layout.index.insert(
            *input,
            (
                AddressClass::ThisLayerInnerLayerWrite,
                FieldType::Ext,
                initial_poly_count,
            ),
        );
        initial_poly_count += 1;
    }
    initial_layer_layout.slot_poly_counts.insert(
        StorageSlot {
            class: AddressClass::ThisLayerInnerLayerWrite,
            field: FieldType::Ext,
        },
        initial_poly_count,
    );
    layers[initial_layer_idx] = initial_layer_layout;

    let mut layer_inputs = initial_output_map.clone();
    for (layer_offset, round) in (0..total_rounds).enumerate() {
        let output_layer = initial_layer_idx + layer_offset + 1;
        let mut layout = GpuGKRLayerLayout {
            log2_stride: initial_trace_log_2 - round - 1,
            ..GpuGKRLayerLayout::default()
        };
        let mut output_idx = 0u32;
        let mut next_inputs = BTreeMap::new();
        for (argument, inputs) in &layer_inputs {
            assert_eq!(inputs.len(), 2);
            let outputs = [
                GKRAddress::InnerLayer {
                    layer: output_layer,
                    offset: output_idx as usize,
                },
                GKRAddress::InnerLayer {
                    layer: output_layer,
                    offset: output_idx as usize + 1,
                },
            ];
            for output in outputs {
                layout.index.insert(
                    output,
                    (
                        AddressClass::ThisLayerInnerLayerWrite,
                        FieldType::Ext,
                        output_idx,
                    ),
                );
                output_idx += 1;
            }
            next_inputs.insert(*argument, outputs.to_vec());
        }
        layout.slot_poly_counts.insert(
            StorageSlot {
                class: AddressClass::ThisLayerInnerLayerWrite,
                field: FieldType::Ext,
            },
            output_idx,
        );
        layers[output_layer] = layout;
        layer_inputs = next_inputs;
    }

    storage.set_layout(Arc::new(GpuGKRStorageLayout {
        trace_len,
        artifact_log2_stride: initial_trace_log_2,
        layers,
        aliases: BTreeMap::new(),
        scratch_space_mapping_rev: BTreeMap::new(),
    }));
}

pub(super) fn expected_pairwise_reduction(values: &[E4]) -> Vec<E4> {
    values
        .as_chunks::<2>()
        .0
        .iter()
        .map(|chunk| {
            let mut value = chunk[0];
            value.mul_assign(&chunk[1]);
            value
        })
        .collect()
}

/// Every reduction slot a probe drives, in `OutputType` order. Five types fill
/// all `REDUCTION_PAIR_CAP` descriptor pairs, so the forward VM's second
/// per-warp pair is exercised too.
pub(super) const PROBE_OUTPUT_TYPES: [OutputType; 5] = [
    OutputType::PermutationProduct,
    OutputType::Lookup16Bits,
    OutputType::LookupTimestamps,
    OutputType::GenericLookup,
    OutputType::InitsAndTeardownsProduct,
];

/// Per-`OutputType` column pair, in `OutputType` order: `[a, b]` for the
/// pairwise types, `[num, den]` for the lookup types.
pub(super) type ProbeColumns = Vec<(OutputType, [Vec<E4>; 2])>;

/// A probe with one distinguished hypercube coordinate.
pub(super) struct DistinguishedCellProbe {
    pub(super) columns: ProbeColumns,
    pub(super) index: usize,
    /// `(fill, distinguished)` for each channel that carries the single
    /// distinguished cell; `None` for the channels that stay constant.
    pub(super) marks: Vec<[Option<(E4, E4)>; 2]>,
}

fn is_pairwise(kind: OutputType) -> bool {
    matches!(
        kind,
        OutputType::PermutationProduct | OutputType::InitsAndTeardownsProduct
    )
}

/// Product-chain probe: `ONE` everywhere except `index`, which carries `marker`.
fn marked_product_column(len: usize, index: usize, marker: E4) -> Vec<E4> {
    let mut column = vec![E4::ONE; len];
    column[index] = marker;
    column
}

/// Multilinear basis vector: `ONE` at `index`, `ZERO` elsewhere.
fn basis_column(len: usize, index: usize) -> Vec<E4> {
    let mut column = vec![E4::ZERO; len];
    column[index] = E4::ONE;
    column
}

/// Builds a probe whose distinguished cell must land at `index >> (round + 1)`
/// when a round binds adjacent pairs. Product chains use `ONE` with one marker
/// cell; lookup chains use the basis vector over an all-`ONE` denominator,
/// where a round sums the pair's numerators.
pub(super) fn distinguished_cell_probe(len: usize, index: usize) -> DistinguishedCellProbe {
    let mut columns = ProbeColumns::new();
    let mut marks = Vec::new();
    for (slot, kind) in PROBE_OUTPUT_TYPES.into_iter().enumerate() {
        if is_pairwise(kind) {
            let markers = [
                sample_ext(1_000 + slot as u32 * 16),
                sample_ext(2_000 + slot as u32 * 16),
            ];
            columns.push((
                kind,
                markers.map(|marker| marked_product_column(len, index, marker)),
            ));
            marks.push(markers.map(|marker| Some((E4::ONE, marker))));
        } else {
            columns.push((kind, [basis_column(len, index), vec![E4::ONE; len]]));
            marks.push([Some((E4::ZERO, E4::ONE)), None]);
        }
    }
    DistinguishedCellProbe {
        columns,
        index,
        marks,
    }
}

/// Probe with pseudorandom columns: every reduction output is a distinct
/// function of the exact pair of inputs the round consumed.
pub(super) fn random_probe(len: usize, seed: u64) -> ProbeColumns {
    let mut rng = StdRng::seed_from_u64(seed);
    let mut column = || {
        (0..len)
            .map(|_| {
                E4::from_array_of_base(std::array::from_fn(|_| {
                    BF::from_u32_with_reduction(rng.random())
                }))
            })
            .collect::<Vec<_>>()
    };
    PROBE_OUTPUT_TYPES
        .into_iter()
        .map(|kind| (kind, [column(), column()]))
        .collect()
}

/// Uploads a probe's columns as this layer's reduction inputs and returns the
/// output map that drives the reduction.
pub(super) fn install_probe_columns(
    storage: &mut GpuGKRStorage<BF, E4>,
    layer_idx: usize,
    columns: &ProbeColumns,
    context: &ProverContext,
) -> BTreeMap<OutputType, Vec<GKRAddress>> {
    let mut output_map = BTreeMap::new();
    let mut offset = 0usize;
    for (kind, pair) in columns {
        let mut addresses = Vec::with_capacity(2);
        for values in pair {
            let address = GKRAddress::InnerLayer {
                layer: layer_idx,
                offset,
            };
            offset += 1;
            storage.insert_extension_at_layer(layer_idx, address, upload_ext_poly(values, context));
            addresses.push(address);
        }
        output_map.insert(*kind, addresses);
    }
    output_map
}

/// CPU reference for one reduction round: every output cell is a function of the
/// adjacent input pair `(2 * j, 2 * j + 1)`.
pub(super) fn expected_round_reduction(columns: &ProbeColumns) -> ProbeColumns {
    columns
        .iter()
        .map(|(kind, [first, second])| {
            let reduced = if is_pairwise(*kind) {
                [
                    expected_pairwise_reduction(first),
                    expected_pairwise_reduction(second),
                ]
            } else {
                let (num, den) = expected_lookup_pair_reduction(first, second);
                [num, den]
            };
            (*kind, reduced)
        })
        .collect()
}

/// Reads one round's outputs and pins the storage layout backward consumes: two
/// outputs per `OutputType` in `OutputType` order, at ascending `InnerLayer`
/// offsets of the round's output layer, packed contiguously at `slot *
/// round_len` inside one per-layer backing.
pub(super) fn read_and_pin_round_outputs(
    storage: &GpuGKRStorage<BF, E4>,
    description: &BTreeMap<usize, BTreeMap<OutputType, DimensionReducingInputOutput>>,
    layer_idx: usize,
    round_len: usize,
    context: &ProverContext,
    label: &str,
) -> ProbeColumns {
    let layer_description = description
        .get(&layer_idx)
        .unwrap_or_else(|| panic!("{label}: no reduction description for layer {layer_idx}"));
    let output_layer = layer_idx + 1;
    let mut slot = 0usize;
    let mut backing = None;
    let mut outputs = ProbeColumns::new();
    for (kind, io) in layer_description {
        let addresses: [GKRAddress; 2] = io
            .output
            .clone()
            .try_into()
            .unwrap_or_else(|_| panic!("{label}: {kind:?} must emit exactly two outputs"));
        let mut values = [Vec::new(), Vec::new()];
        for (channel, address) in addresses.into_iter().enumerate() {
            assert_eq!(
                address,
                GKRAddress::InnerLayer {
                    layer: output_layer,
                    offset: slot,
                },
                "{label}: {kind:?} output {channel} must own offset {slot} of layer {output_layer}"
            );
            let poly = storage.get_ext_poly(address);
            assert_eq!(
                poly.len, round_len,
                "{label}: {kind:?} output {channel} length"
            );
            assert_eq!(
                poly.offset,
                slot * round_len,
                "{label}: {kind:?} output {channel} must start at slot {slot} of the layer backing"
            );
            let poly_backing = poly.backing.as_ptr();
            match backing {
                None => backing = Some(poly_backing),
                Some(expected) => assert_eq!(
                    expected, poly_backing,
                    "{label}: layer {output_layer} outputs must share one backing"
                ),
            }
            values[channel] = read_ext_poly(poly, context);
            slot += 1;
        }
        outputs.push((*kind, values));
    }
    assert_eq!(
        outputs.iter().map(|(kind, _)| *kind).collect::<Vec<_>>(),
        PROBE_OUTPUT_TYPES.to_vec(),
        "{label}: layer {output_layer} must emit every probe output type in OutputType order"
    );
    outputs
}

/// Pins the adjacent-pair (LSB) signature directly: after `round_idx`, the
/// probe's distinguished cell sits at `index >> (round_idx + 1)`. Binding the
/// high coordinate instead would leave it at `index & (round_len - 1)`.
pub(super) fn assert_distinguished_cell_at_lsb_position(
    probe: &DistinguishedCellProbe,
    outputs: &ProbeColumns,
    round_idx: u32,
    label: &str,
) {
    let expected_index = probe.index >> (round_idx + 1);
    for ((kind, columns), marks) in outputs.iter().zip(&probe.marks) {
        for (channel, (column, mark)) in columns.iter().zip(marks).enumerate() {
            let Some((fill, distinguished)) = *mark else {
                continue;
            };
            let found = column
                .iter()
                .enumerate()
                .filter(|(_, value)| **value != fill)
                .map(|(idx, _)| idx)
                .collect::<Vec<_>>();
            assert_eq!(
                found,
                vec![expected_index],
                "{label}: {kind:?} channel {channel} round {round_idx} must carry the \
                 distinguished cell at {} >> {} only",
                probe.index,
                round_idx + 1
            );
            assert_eq!(
                column[expected_index], distinguished,
                "{label}: {kind:?} channel {channel} round {round_idx} distinguished value"
            );
        }
    }
}

pub(super) fn expected_lookup_pair_reduction(num: &[E4], den: &[E4]) -> (Vec<E4>, Vec<E4>) {
    let mut reduced_num = Vec::with_capacity(num.len() / 2);
    let mut reduced_den = Vec::with_capacity(den.len() / 2);

    for (num_pair, den_pair) in num
        .as_chunks::<2>()
        .0
        .iter()
        .zip(den.as_chunks::<2>().0.iter())
    {
        let mut left_term = num_pair[0];
        left_term.mul_assign(&den_pair[1]);
        let mut right_term = num_pair[1];
        right_term.mul_assign(&den_pair[0]);
        left_term.add_assign(&right_term);
        reduced_num.push(left_term);

        let mut den_value = den_pair[0];
        den_value.mul_assign(&den_pair[1]);
        reduced_den.push(den_value);
    }

    (reduced_num, reduced_den)
}
