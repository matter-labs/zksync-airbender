use super::*;
use crate::upstream::{FieldExtension, PrimeField};

/// Placeholder — returns empty dims for every section. Retained for
/// unit-test coverage of the empty-slab edge case. Real `prove()` uses
/// [`build_proof_layout_inputs`].
pub(crate) fn placeholder_inputs_for_prove() -> ProofLayoutInputs {
    ProofLayoutInputs {
        output_evaluations: BTreeMap::new(),
        backward_layers: Vec::new(),
        whir: WhirDims {
            setup: empty_base_layer_dims(),
            memory: empty_base_layer_dims(),
            witness: empty_base_layer_dims(),
            intermediate: Vec::new(),
            num_ood_samples: 0,
            total_sumcheck_polys: 0,
            pow_rounds: 0,
            final_monomials_len: 0,
        },
    }
}

fn empty_base_layer_dims() -> WhirBaseLayerDims {
    WhirBaseLayerDims {
        num_columns: 0,
        cap_digest_count: 0,
        query_count: 0,
        leaf_values_len: 0,
        path_len: 0,
    }
}

fn sample_inputs() -> ProofLayoutInputs {
    let backward_layers = vec![
        BackwardLayerDims {
            layer_idx: 8,
            sumcheck_num_rounds: 3,
            final_step_eval_addresses: vec![GKRAddress::BaseLayerWitness(0); 2],
            final_step_eval_degree: 4,
            // Dim-reducing slot: never has orphans.
            extra_evaluations_addresses: Vec::new(),
        },
        BackwardLayerDims {
            layer_idx: 0,
            sumcheck_num_rounds: 5,
            final_step_eval_addresses: vec![GKRAddress::BaseLayerWitness(0); 3],
            final_step_eval_degree: 2,
            // Exercise non-empty orphans to validate the extra
            // range's sizing + parser round-trip in this slot.
            // Production code derives this list via a BTreeSet
            // (`compute_main_layer_orphan_output_addresses_per_layer`),
            // so the ordering matches `GKRAddress`'s `Ord` impl —
            // `InnerLayer` < `ScratchSpace` per the enum-variant
            // declaration order.
            extra_evaluations_addresses: vec![
                GKRAddress::InnerLayer {
                    layer: 1,
                    offset: 0,
                },
                GKRAddress::ScratchSpace(7),
            ],
        },
    ];

    let whir = WhirDims {
        setup: WhirBaseLayerDims {
            num_columns: 4,
            cap_digest_count: 8,
            query_count: 16,
            leaf_values_len: 32,
            path_len: 12,
        },
        memory: WhirBaseLayerDims {
            num_columns: 32,
            cap_digest_count: 8,
            query_count: 16,
            leaf_values_len: 128,
            path_len: 12,
        },
        witness: WhirBaseLayerDims {
            num_columns: 64,
            cap_digest_count: 8,
            query_count: 16,
            leaf_values_len: 256,
            path_len: 12,
        },
        intermediate: vec![
            WhirIntermediateDims {
                cap_digest_count: 8,
                query_count: 12,
                leaf_values_len: 16,
                path_len: 10,
            },
            WhirIntermediateDims {
                cap_digest_count: 8,
                query_count: 10,
                leaf_values_len: 16,
                path_len: 8,
            },
        ],
        num_ood_samples: 2,
        total_sumcheck_polys: 8,
        pow_rounds: 3,
        final_monomials_len: 4,
    };

    let mut output_evaluations = BTreeMap::new();
    output_evaluations.insert(OutputType::PermutationProduct, [2usize, 2usize]);
    output_evaluations.insert(OutputType::Lookup16Bits, [1usize, 1usize]);

    ProofLayoutInputs {
        output_evaluations,
        backward_layers,
        whir,
    }
}

#[test]
fn layout_is_16_byte_aligned_and_nonoverlapping() {
    let inputs = sample_inputs();
    let layout = ProofLayout::new(&inputs);

    let mut ranges: Vec<(String, Range<usize>)> = Vec::new();
    for (&output_type, r) in layout.output_evaluations.iter() {
        ranges.push((format!("{output_type:?}.read"), r.read_set.clone()));
        ranges.push((format!("{output_type:?}.write"), r.write_set.clone()));
    }
    for bw in &layout.backward {
        ranges.push((
            format!("backward[{}].internal", bw.layer_idx),
            bw.internal_round_coefficients.clone(),
        ));
        ranges.push((
            format!("backward[{}].final", bw.layer_idx),
            bw.final_step_evaluations.clone(),
        ));
        if !bw.extra_evaluations_addresses.is_empty() {
            ranges.push((
                format!("backward[{}].extra", bw.layer_idx),
                bw.extra_evaluations.clone(),
            ));
        }
    }
    for (name, base) in [
        ("setup", &layout.whir.setup),
        ("memory", &layout.whir.memory),
        ("witness", &layout.whir.witness),
    ] {
        ranges.push((format!("whir.{name}.cap"), base.cap.clone()));
        ranges.push((format!("whir.{name}.evals"), base.evals.clone()));
        ranges.push((format!("whir.{name}.qi"), base.query_indices.clone()));
        ranges.push((format!("whir.{name}.ql"), base.query_leaves.clone()));
        ranges.push((format!("whir.{name}.qp"), base.query_paths.clone()));
    }
    for (i, im) in layout.whir.intermediate.iter().enumerate() {
        ranges.push((format!("whir.intermediate[{i}].cap"), im.cap.clone()));
        ranges.push((
            format!("whir.intermediate[{i}].qi"),
            im.query_indices.clone(),
        ));
        ranges.push((
            format!("whir.intermediate[{i}].ql"),
            im.query_leaves.clone(),
        ));
        ranges.push((format!("whir.intermediate[{i}].qp"), im.query_paths.clone()));
    }
    ranges.push(("whir.ood".to_string(), layout.whir.ood_samples.clone()));
    ranges.push((
        "whir.sumcheck_polys".to_string(),
        layout.whir.sumcheck_polys.clone(),
    ));
    ranges.push((
        "whir.pow_nonces".to_string(),
        layout.whir.pow_nonces.clone(),
    ));
    ranges.push((
        "whir.final_monomials".to_string(),
        layout.whir.final_monomials.clone(),
    ));

    // Every field start is FIELD_ALIGN-aligned.
    for (name, r) in &ranges {
        assert_eq!(r.start % FIELD_ALIGN, 0, "field `{name}` start not aligned");
        assert!(r.end <= layout.total_bytes);
    }
    // Non-overlap (sort by start, ensure no previous end > current start).
    let mut sorted = ranges.clone();
    sorted.sort_by_key(|(_, r)| r.start);
    for pair in sorted.windows(2) {
        let (a_name, a_r) = &pair[0];
        let (b_name, b_r) = &pair[1];
        assert!(
            a_r.end <= b_r.start,
            "overlap: `{a_name}` ends at {}, `{b_name}` starts at {}",
            a_r.end,
            b_r.start
        );
    }

    // Total bytes is itself FIELD_ALIGN-aligned.
    assert_eq!(layout.total_bytes % FIELD_ALIGN, 0);
    assert!(layout.total_bytes > 0);
}

#[test]
fn backward_range_sizes_match_inputs() {
    let inputs = sample_inputs();
    let layout = ProofLayout::new(&inputs);

    for (dims, laid) in inputs.backward_layers.iter().zip(layout.backward.iter()) {
        assert_eq!(laid.layer_idx, dims.layer_idx);
        assert_eq!(laid.sumcheck_num_rounds, dims.sumcheck_num_rounds);
        let internal_len = dims.sumcheck_num_rounds.saturating_sub(1) * 4;
        assert_eq!(
            laid.internal_round_coefficients.end - laid.internal_round_coefficients.start,
            internal_len * size_of::<E4>()
        );
        let final_len = dims.final_step_eval_addresses.len() * dims.final_step_eval_degree;
        assert_eq!(
            laid.final_step_evaluations.end - laid.final_step_evaluations.start,
            final_len * size_of::<E4>()
        );
        // 1 E4 per orphan address.
        let extra_len = dims.extra_evaluations_addresses.len();
        assert_eq!(
            laid.extra_evaluations.end - laid.extra_evaluations.start,
            extra_len * size_of::<E4>()
        );
        assert_eq!(
            laid.extra_evaluations_addresses,
            dims.extra_evaluations_addresses,
        );
    }
}

#[test]
fn whir_range_sizes_match_inputs() {
    let inputs = sample_inputs();
    let layout = ProofLayout::new(&inputs);

    let check_base = |dims: &WhirBaseLayerDims, laid: &WhirBaseLayerByteLayout| {
        assert_eq!(
            laid.cap.end - laid.cap.start,
            dims.cap_digest_count * DIGEST_U32_WORDS * size_of::<u32>()
        );
        assert_eq!(
            laid.evals.end - laid.evals.start,
            dims.num_columns * size_of::<E4>()
        );
        assert_eq!(
            laid.query_indices.end - laid.query_indices.start,
            dims.query_count * size_of::<u32>()
        );
        assert_eq!(
            laid.query_leaves.end - laid.query_leaves.start,
            dims.query_count * dims.leaf_values_len * size_of::<BF>()
        );
        assert_eq!(
            laid.query_paths.end - laid.query_paths.start,
            dims.query_count * dims.path_len * DIGEST_U32_WORDS * size_of::<u32>()
        );
    };
    check_base(&inputs.whir.setup, &layout.whir.setup);
    check_base(&inputs.whir.memory, &layout.whir.memory);
    check_base(&inputs.whir.witness, &layout.whir.witness);

    for (dims, laid) in inputs
        .whir
        .intermediate
        .iter()
        .zip(layout.whir.intermediate.iter())
    {
        assert_eq!(
            laid.cap.end - laid.cap.start,
            dims.cap_digest_count * DIGEST_U32_WORDS * size_of::<u32>()
        );
        assert_eq!(
            laid.query_indices.end - laid.query_indices.start,
            dims.query_count * size_of::<u32>()
        );
        assert_eq!(
            laid.query_leaves.end - laid.query_leaves.start,
            dims.query_count * dims.leaf_values_len * size_of::<E4>()
        );
        assert_eq!(
            laid.query_paths.end - laid.query_paths.start,
            dims.query_count * dims.path_len * DIGEST_U32_WORDS * size_of::<u32>()
        );
    }

    assert_eq!(
        layout.whir.ood_samples.end - layout.whir.ood_samples.start,
        inputs.whir.num_ood_samples * size_of::<E4>()
    );
    assert_eq!(
        layout.whir.sumcheck_polys.end - layout.whir.sumcheck_polys.start,
        inputs.whir.total_sumcheck_polys * 3 * size_of::<E4>()
    );
    assert_eq!(
        layout.whir.pow_nonces.end - layout.whir.pow_nonces.start,
        inputs.whir.pow_rounds * size_of::<u64>()
    );
    assert_eq!(
        layout.whir.final_monomials.end - layout.whir.final_monomials.start,
        inputs.whir.final_monomials_len * size_of::<E4>()
    );
}

#[test]
fn typed_accessors_match_ranges() {
    let inputs = sample_inputs();
    let layout = ProofLayout::new(&inputs);
    let mut slab = vec![0u8; layout.total_bytes];
    // align the test buffer to 16B by taking the offset into a larger Vec —
    // in production the device allocator guarantees alignment.
    let (_, typed, _) = unsafe { slab.align_to::<u128>() };
    assert!(!typed.is_empty(), "test buffer must be 16-byte aligned");

    // Round-trip: write via device pointer view, read via host slice view.
    let slab_ptr = slab.as_mut_ptr();
    for (i, bw_layout) in layout.backward.iter().enumerate() {
        unsafe {
            let (ptr, len) = layout.backward_final_step_evals_device_mut(slab_ptr, i);
            assert_eq!(
                ptr as *const u8 as usize,
                slab_ptr as usize + bw_layout.final_step_evaluations.start
            );
            assert_eq!(
                len * size_of::<E4>(),
                bw_layout.final_step_evaluations.end - bw_layout.final_step_evaluations.start
            );
            let (extra_ptr, extra_len) = layout.backward_extra_evaluations_device_mut(slab_ptr, i);
            assert_eq!(
                extra_ptr as *const u8 as usize,
                slab_ptr as usize + bw_layout.extra_evaluations.start
            );
            assert_eq!(
                extra_len * size_of::<E4>(),
                bw_layout.extra_evaluations.end - bw_layout.extra_evaluations.start
            );
            assert_eq!(extra_len, bw_layout.extra_evaluations_addresses.len());
        }
        let host = layout.backward_final_step_evals_host(&slab, i);
        assert_eq!(
            host.len() * size_of::<E4>(),
            bw_layout.final_step_evaluations.end - bw_layout.final_step_evaluations.start
        );
        let extra_host = layout.backward_extra_evaluations_host(&slab, i);
        assert_eq!(
            extra_host.len() * size_of::<E4>(),
            bw_layout.extra_evaluations.end - bw_layout.extra_evaluations.start,
        );
    }
}

#[test]
fn parser_round_trips_extra_evaluations() {
    let inputs = sample_inputs();
    let layout = ProofLayout::new(&inputs);

    // Layer 0 has 2 orphan addresses (per `sample_inputs`). Write
    // recognizable values into the slab's `extra_evaluations` range
    // for layer-slot 1 (= main layer, the second slot here), then
    // run the parser and assert the BTreeMap has the expected keys
    // and values.
    let mut slab = vec![0u8; layout.total_bytes];
    let layer_slot = 1usize;
    let bw = &layout.backward[layer_slot];
    assert_eq!(bw.extra_evaluations_addresses.len(), 2);

    // Write `[E4::from_limbs([1,0,0,0]), E4::from_limbs([2,0,0,0])]`
    // into the slab via the device-side accessor (we have a host
    // pointer here but the call shape matches production usage).
    let slab_ptr = slab.as_mut_ptr();
    unsafe {
        let (ptr, len) = layout.backward_extra_evaluations_device_mut(slab_ptr, layer_slot);
        assert_eq!(len, 2);
        let written: [E4; 2] = [
            E4::from_base(BF::from_u32_unchecked(1)),
            E4::from_base(BF::from_u32_unchecked(2)),
        ];
        std::ptr::copy_nonoverlapping(written.as_ptr(), ptr, 2);
    }

    let parsed = layout.parse_sumcheck_intermediate_values(&slab, BTreeMap::new());
    let layer_idx = inputs.backward_layers[layer_slot].layer_idx;
    let intermediate = parsed.get(&layer_idx).expect("layer slot in parsed map");
    assert_eq!(
        intermediate.extra_evaluations_from_caching_relations.len(),
        2,
    );
    let by_addr: Vec<_> = intermediate
        .extra_evaluations_from_caching_relations
        .iter()
        .collect();
    // BTreeMap iteration follows GKRAddress's `Ord`: InnerLayer < ScratchSpace.
    assert_eq!(
        *by_addr[0].0,
        GKRAddress::InnerLayer {
            layer: 1,
            offset: 0,
        }
    );
    assert_eq!(*by_addr[1].0, GKRAddress::ScratchSpace(7));
    // `extras_flat[0] = 1` was written under the address at slab
    // index 0 = InnerLayer{1, 0}, `extras_flat[1] = 2` under
    // ScratchSpace(7). The map preserves those associations.
    assert_eq!(*by_addr[0].1, E4::from_base(BF::from_u32_unchecked(1)));
    assert_eq!(*by_addr[1].1, E4::from_base(BF::from_u32_unchecked(2)));
}
