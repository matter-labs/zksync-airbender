use super::*;
use crate::upstream::{FieldExtension, PrimeField};

fn sample_e4(value: u32) -> E4 {
    E4::from_base(BF::from_u32_unchecked(value))
}

#[repr(C, align(32))]
#[derive(Clone, Copy)]
struct AlignedSlabBlock([u8; FIELD_ALIGN]);

const _: () = {
    assert!(FIELD_ALIGN == 32);
    assert!(size_of::<AlignedSlabBlock>() == FIELD_ALIGN);
    assert!(std::mem::align_of::<AlignedSlabBlock>() >= std::mem::align_of::<E4>());
};

struct AlignedSlab {
    blocks: Vec<AlignedSlabBlock>,
}

impl AlignedSlab {
    fn zeroed(byte_len: usize) -> Self {
        assert_eq!(byte_len % FIELD_ALIGN, 0);
        Self {
            blocks: vec![AlignedSlabBlock([0; FIELD_ALIGN]); byte_len / FIELD_ALIGN],
        }
    }

    fn as_bytes_mut(&mut self) -> &mut [u8] {
        let byte_len = self.blocks.len() * FIELD_ALIGN;
        // SAFETY: `AlignedSlabBlock` is a contiguous, initialized byte block;
        // its 32-byte alignment satisfies every typed proof-slab accessor.
        unsafe { std::slice::from_raw_parts_mut(self.blocks.as_mut_ptr().cast(), byte_len) }
    }
}

fn sample_inputs() -> ProofLayoutInputs {
    let backward_layers = vec![
        BackwardLayerDims {
            layer_idx: 8,
            sumcheck_num_rounds: 3,
            final_step_eval_addresses: vec![GKRAddress::BaseLayerWitness(0); 2],
            final_step_eval_degree: 4,
            // Dim-reducing slot: never has cached-relation extras.
            extra_evaluations_addresses: Vec::new(),
        },
        BackwardLayerDims {
            layer_idx: 0,
            sumcheck_num_rounds: 5,
            final_step_eval_addresses: vec![GKRAddress::BaseLayerWitness(0); 3],
            final_step_eval_degree: 2,
            // Exercise non-empty cached-relation extras to validate the extra
            // range's sizing + parser round-trip in this slot.
            // Production stores this list in `GKRAddress` order, so
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
        pack_log2: 0,
        original_evaluation_point_len: 2,
        setup: WhirBaseLayerDims {
            num_columns: 4,
            logical_num_columns: 4,
            cap_digest_count: 8,
            query_count: 16,
            leaf_values_len: 32,
            path_len: 12,
        },
        memory: WhirBaseLayerDims {
            num_columns: 32,
            logical_num_columns: 32,
            cap_digest_count: 8,
            query_count: 16,
            leaf_values_len: 128,
            path_len: 12,
        },
        witness: WhirBaseLayerDims {
            num_columns: 64,
            logical_num_columns: 64,
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
fn layout_is_32_byte_aligned_and_nonoverlapping() {
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
    ranges.push((
        "whir.original_evaluation_point".to_string(),
        layout.whir.original_evaluation_point.clone(),
    ));
    ranges.push((
        "whir.batching_challenge".to_string(),
        layout.whir.batching_challenge.clone(),
    ));
    // Shared base-oracle `query_indices` range (single copy across the three
    // base oracles).
    ranges.push((
        "whir.base_query_indices".to_string(),
        layout.whir.base_query_indices.clone(),
    ));
    for (name, base) in [
        ("setup", &layout.whir.setup),
        ("memory", &layout.whir.memory),
        ("witness", &layout.whir.witness),
    ] {
        ranges.push((format!("whir.{name}.cap"), base.cap.clone()));
        ranges.push((format!("whir.{name}.evals"), base.evals.clone()));
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
        // `sumcheck_num_rounds` monomials.
        let internal_len = dims.sumcheck_num_rounds * 4;
        assert_eq!(
            laid.internal_round_coefficients.end - laid.internal_round_coefficients.start,
            internal_len * size_of::<E4>()
        );
        let final_len = dims.final_step_eval_addresses.len() * dims.final_step_eval_degree;
        assert_eq!(
            laid.final_step_evaluations.end - laid.final_step_evaluations.start,
            final_len * size_of::<E4>()
        );
        // 1 E4 per extra-evaluation address.
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

    assert_eq!(
        layout.whir.original_evaluation_point.end - layout.whir.original_evaluation_point.start,
        inputs.whir.original_evaluation_point_len * size_of::<E4>()
    );
    assert_eq!(
        layout.whir.batching_challenge.end - layout.whir.batching_challenge.start,
        size_of::<E4>()
    );

    // Shared base-oracle `query_indices` slab range — sized by the common
    // `query_count` across setup/memory/witness.
    assert_eq!(
        inputs.whir.setup.query_count,
        inputs.whir.memory.query_count
    );
    assert_eq!(
        inputs.whir.setup.query_count,
        inputs.whir.witness.query_count
    );
    assert_eq!(
        layout.whir.base_query_indices.end - layout.whir.base_query_indices.start,
        inputs.whir.setup.query_count * size_of::<u32>()
    );

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
    let mut slab_storage = AlignedSlab::zeroed(layout.total_bytes);
    let slab = slab_storage.as_bytes_mut();
    assert_eq!(slab.as_ptr() as usize % FIELD_ALIGN, 0);
    let slab_ptr = slab.as_mut_ptr();

    assert_eq!(
        layout.whir_original_evaluation_point_host(slab).len(),
        inputs.whir.original_evaluation_point_len,
    );
    assert_eq!(layout.whir_batching_challenge_host(slab).len(), 1);
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
        let host = layout.backward_final_step_evals_host(slab, i);
        assert_eq!(
            std::mem::size_of_val(host),
            bw_layout.final_step_evaluations.end - bw_layout.final_step_evaluations.start
        );
        let extra_host = layout.backward_extra_evaluations_host(slab, i);
        assert_eq!(
            std::mem::size_of_val(extra_host),
            bw_layout.extra_evaluations.end - bw_layout.extra_evaluations.start,
        );
    }
}

#[test]
fn parser_round_trips_extra_evaluations() {
    let inputs = sample_inputs();
    let layout = ProofLayout::new(&inputs);

    // Layer 0 has 2 extra-evaluation addresses (per `sample_inputs`). Write
    // recognizable values into the slab's `extra_evaluations` range
    // for layer-slot 1 (= main layer, the second slot here), then
    // run the parser and assert the BTreeMap has the expected keys
    // and values.
    let mut slab_storage = AlignedSlab::zeroed(layout.total_bytes);
    let slab = slab_storage.as_bytes_mut();
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

    let parsed = layout.parse_sumcheck_intermediate_values(slab, BTreeMap::new());
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

#[test]
fn cpu_parser_splits_whir_streams_by_schedule() {
    let inputs = sample_inputs();
    let layout = ProofLayout::new(&inputs);
    let mut slab_storage = AlignedSlab::zeroed(layout.total_bytes);
    let slab = slab_storage.as_bytes_mut();
    let point = [sample_e4(10), sample_e4(20)];
    let batching = sample_e4(30);
    // 8 sumcheck polynomials over the sample's 3 rounds (2 intermediate
    // oracles): a round-0 fold of 1, then 4 + 3 = 8 total
    let polys: Vec<[E4; 3]> = (0..8)
        .map(|i| {
            [
                sample_e4(3 * i + 1),
                sample_e4(3 * i + 2),
                sample_e4(3 * i + 3),
            ]
        })
        .collect();
    let ood = [sample_e4(100), sample_e4(101)];
    let nonces = [7u64, 8, 9];

    unsafe {
        let (point_ptr, point_len) =
            layout.whir_original_evaluation_point_device_mut(slab.as_mut_ptr());
        assert_eq!(point_len, point.len());
        std::ptr::copy_nonoverlapping(point.as_ptr(), point_ptr, point.len());
        let (batching_ptr, batching_len) =
            layout.whir_batching_challenge_device_mut(slab.as_mut_ptr());
        assert_eq!(batching_len, 1);
        std::ptr::copy_nonoverlapping(&batching, batching_ptr, 1);
        let (ptr, len) = layout.whir_sumcheck_polys_device_mut(slab.as_mut_ptr());
        assert_eq!(len, 3 * polys.len());
        let flat: Vec<E4> = polys.iter().flatten().copied().collect();
        std::ptr::copy_nonoverlapping(flat.as_ptr(), ptr, flat.len());
        let (ptr, len) = layout.whir_ood_samples_device_mut(slab.as_mut_ptr());
        assert_eq!(len, ood.len());
        std::ptr::copy_nonoverlapping(ood.as_ptr(), ptr, ood.len());
        let (ptr, len) = layout.whir_pow_nonces_device_mut(slab.as_mut_ptr());
        assert_eq!(len, nonces.len());
        std::ptr::copy_nonoverlapping(nonces.as_ptr(), ptr, nonces.len());
    }

    // the device-side handoff fields stay readable from the slab
    assert_eq!(layout.whir_original_evaluation_point_host(slab), &point[..]);
    assert_eq!(layout.whir_batching_challenge_host(slab), &[batching][..]);

    let schedule =
        WhirSchedule::from_legacy_arrays(2, 8, 0, &[1, 4, 3], &[16, 12, 10], &[4, 8], &[1, 1, 1]);
    let proof = layout.parse_whir_proof(slab, &schedule);
    assert_eq!(proof.base_sumcheck_polys, polys[..1].to_vec());
    assert_eq!(
        proof.intermediate_whir_oracles[0].sumcheck_polys,
        polys[1..5].to_vec()
    );
    assert_eq!(
        proof.intermediate_whir_oracles[1].sumcheck_polys,
        polys[5..8].to_vec()
    );
    assert_eq!(proof.intermediate_whir_oracles[0].ood_samples, vec![ood[0]]);
    assert_eq!(proof.intermediate_whir_oracles[1].ood_samples, vec![ood[1]]);
    assert_eq!(proof.base_queries_pow_nonce, 7);
    assert_eq!(proof.intermediate_whir_oracles[0].queries_pow_nonce, 8);
    assert_eq!(proof.intermediate_whir_oracles[1].queries_pow_nonce, 9);
    assert_eq!(proof.whir_schedule, schedule);
}

#[test]
fn cpu_packed_proof_layout_keeps_logical_claims_and_aliases_k0() {
    let inputs = sample_inputs();
    let identity = ProofLayout::new(&inputs);
    for base in [
        &identity.whir.memory,
        &identity.whir.witness,
        &identity.whir.setup,
    ] {
        assert_eq!(
            base.logical_evals, base.evals,
            "k0 must alias without another range"
        );
    }
    for k in 1..=4 {
        let mut inputs = sample_inputs();
        inputs.whir.pack_log2 = k;
        inputs.whir.original_evaluation_point_len = 20 + k;
        let pack = 1usize << k;
        for (base, logical) in [
            (&mut inputs.whir.memory, pack + 1),
            (&mut inputs.whir.witness, 2 * pack + 1),
            (&mut inputs.whir.setup, 0),
        ] {
            base.logical_num_columns = logical;
            base.num_columns = logical.div_ceil(pack);
        }
        let layout = ProofLayout::new(&inputs);
        let mut slab = AlignedSlab::zeroed(layout.total_bytes);
        let bytes = slab.as_bytes_mut();
        let nonce = 0x1234_5678_9abc_def0u64;
        // This CPU mirror checks the device accessor's offset without dereferencing
        // its pointer, then reads the same slot through the terminal host accessor.
        let (nonce_ptr, nonce_len) =
            unsafe { layout.batched_proximity_pow_nonce_device_mut(bytes.as_mut_ptr()) };
        assert_eq!(nonce_len, 1);
        assert_eq!(
            nonce_ptr as usize,
            bytes.as_ptr() as usize + layout.batched_proximity_pow_nonce.start
        );
        bytes[layout.batched_proximity_pow_nonce.clone()].copy_from_slice(&nonce.to_le_bytes());
        assert_eq!(layout.batched_proximity_pow_nonce_host(bytes), nonce);
        let mut ranges = Vec::new();
        for (slot, kind) in [
            WhirBaseLayerKind::Memory,
            WhirBaseLayerKind::Witness,
            WhirBaseLayerKind::Setup,
        ]
        .into_iter()
        .enumerate()
        {
            let base = match kind {
                WhirBaseLayerKind::Memory => &layout.whir.memory,
                WhirBaseLayerKind::Witness => &layout.whir.witness,
                WhirBaseLayerKind::Setup => &layout.whir.setup,
            };
            for (range, sentinel) in [
                (&base.logical_evals, sample_e4(100 + slot as u32)),
                (&base.evals, sample_e4(200 + slot as u32)),
            ] {
                assert_eq!(range.start % FIELD_ALIGN, 0);
                if !range.is_empty() {
                    ranges.push(range.clone());
                }
                // SAFETY: the aligned host slab is exclusively owned and each
                // tested range is E4-aligned and within the allocation.
                unsafe {
                    let values = std::slice::from_raw_parts_mut(
                        bytes.as_mut_ptr().add(range.start).cast::<E4>(),
                        range.len() / size_of::<E4>(),
                    );
                    values.fill(sentinel);
                }
            }
        }
        ranges.sort_by_key(|range| range.start);
        for adjacent in ranges.windows(2) {
            assert!(adjacent[0].end <= adjacent[1].start);
        }
        for (slot, kind) in [
            WhirBaseLayerKind::Memory,
            WhirBaseLayerKind::Witness,
            WhirBaseLayerKind::Setup,
        ]
        .into_iter()
        .enumerate()
        {
            assert!(layout
                .whir_base_logical_evals_host(bytes, kind)
                .iter()
                .all(|v| *v == sample_e4(100 + slot as u32)));
            assert!(layout
                .whir_base_evals_host(bytes, kind)
                .iter()
                .all(|v| *v == sample_e4(200 + slot as u32)));
        }
        assert_eq!(
            layout.whir_original_evaluation_point_host(bytes).len(),
            20 + k
        );
    }
}
