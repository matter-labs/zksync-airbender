use super::*;

pub(crate) fn build_proof_layout_inputs<E>(
    compiled_circuit: &GKRCircuitArtifact<BF>,
    external_challenges: &prover::gkr::prover::GKRExternalChallenges<BF, E>,
    whir_schedule: &WhirSchedule,
    final_trace_size_log_2: usize,
    memory_geometry: ProofLayoutBaseLayerGeometry,
    witness_geometry: ProofLayoutBaseLayerGeometry,
    setup_geometry: ProofLayoutBaseLayerGeometry,
) -> ProofLayoutInputs
where
    E: field::Field + field::FieldExtension<BF>,
{
    // Normalize-once for the address-derivation helpers so they see the
    // same `(MaxQuadratic { output: ScratchSpace(K) })` shape that the
    // backward main-layer scheduler operates on. Without this, orphan
    // addresses derived structurally would still carry `InnerLayer { ..
    // }` for scratch-mapped MaxQuadratic outputs, while runtime kernel
    // outputs (post-normalize) carry `ScratchSpace(K)` — and the
    // resulting `next_claim_layout` augmentation would never match
    // L-1's `claim_idx` lookup. The clone is paid once per proof.
    let compiled_circuit =
        crate::prover::gkr::transform::normalize_compiled_circuit_for_gpu(compiled_circuit.clone());
    let initial_trace_size_log_2 = compiled_circuit.trace_len.trailing_zeros() as usize;
    let dimension_reducing_inputs = crate::prover::gkr::backward::derive_dimension_reducing_inputs(
        compiled_circuit.layers.len(),
        &compiled_circuit.global_output_map,
        initial_trace_size_log_2,
        final_trace_size_log_2,
    );
    let main_layer_input_addresses_per_layer =
        crate::prover::gkr::backward::collect_main_layer_input_addresses_per_layer::<E>(
            &compiled_circuit,
            external_challenges,
        );
    let main_layer_outputs =
        crate::prover::gkr::backward::collect_main_layer_kernel_output_addresses_per_layer::<E>(
            &compiled_circuit,
            external_challenges,
        );
    let main_layer_orphan_output_addresses_per_layer =
        crate::prover::gkr::backward::compute_main_layer_orphan_output_addresses_per_layer::<E>(
            &main_layer_input_addresses_per_layer,
            &main_layer_outputs,
        );
    assert!(initial_trace_size_log_2 >= final_trace_size_log_2);
    let num_dim_reducing_layers = initial_trace_size_log_2 - final_trace_size_log_2;
    let num_main_layers = compiled_circuit.layers.len();
    assert_eq!(
        dimension_reducing_inputs.len(),
        num_dim_reducing_layers,
        "dimension_reducing_inputs must have one entry per dim-reducing layer",
    );
    assert_eq!(
        main_layer_input_addresses_per_layer.len(),
        num_main_layers,
        "main_layer_input_addresses_per_layer must have one entry per main layer",
    );
    assert_eq!(
        main_layer_orphan_output_addresses_per_layer.len(),
        num_main_layers,
        "main_layer_orphan_output_addresses_per_layer must have one entry per main layer",
    );

    // ------------------------------------------------------------------
    // output_evaluations: one (read_set, write_set) entry per OutputType.
    // Both halves have length `1 << final_trace_size_log_2` (the reduced-
    // output polynomial size at the initial sumcheck layer).
    // ------------------------------------------------------------------
    let reduced_poly_len = 1usize << final_trace_size_log_2;
    let mut output_evaluations = BTreeMap::new();
    for (&output_type, addresses) in compiled_circuit.global_output_map.iter() {
        assert_eq!(
            addresses.len(),
            2,
            "global_output_map[{:?}] must have exactly 2 entries (read + write set)",
            output_type,
        );
        output_evaluations.insert(output_type, [reduced_poly_len, reduced_poly_len]);
    }

    // ------------------------------------------------------------------
    // backward_layers (scheduler high-to-low order)
    // ------------------------------------------------------------------
    //
    // Dim-reducing slot 0 is the highest layer_idx = `num_main_layers +
    // num_dim_reducing_layers - 1` (= `initial_layer_for_sumcheck`), with
    // sumcheck_num_rounds = final_trace_size_log_2. Each subsequent
    // dim-reducing slot covers one lower layer_idx and one more folding step
    // (see backward.rs:3251-3253 + backward.rs:3387). Main layers follow in
    // `compiled_circuit.layers.into_iter().enumerate().rev()` order — index
    // `num_main_layers - 1` down to 0 — each with
    // `sumcheck_num_rounds = initial_trace_size_log_2` (backward.rs:3503).
    let mut backward_layers = Vec::with_capacity(num_dim_reducing_layers + num_main_layers);
    for slot in 0..num_dim_reducing_layers {
        let layer_idx = num_main_layers + num_dim_reducing_layers - 1 - slot;
        let sumcheck_num_rounds = final_trace_size_log_2 + slot;
        let io_map = dimension_reducing_inputs
            .get(&layer_idx)
            .unwrap_or_else(|| {
                panic!("dimension_reducing_inputs missing entry for layer_idx {layer_idx}")
            });
        let mut addresses: BTreeSet<GKRAddress> = BTreeSet::new();
        for io in io_map.values() {
            for addr in io.inputs.iter() {
                addresses.insert(*addr);
            }
        }
        backward_layers.push(BackwardLayerDims {
            layer_idx,
            sumcheck_num_rounds,
            final_step_eval_addresses: addresses.into_iter().collect(),
            final_step_eval_degree: 4,
            // Dim-reducing layers don't host the kind of orphan-output
            // pattern that main-layer `MaxQuadratic` produces; the
            // forward dim-reduction pass wires every output from one
            // round directly into the next round's inputs.
            extra_evaluations_addresses: Vec::new(),
        });
    }
    for layer_idx in (0..num_main_layers).rev() {
        backward_layers.push(BackwardLayerDims {
            layer_idx,
            sumcheck_num_rounds: initial_trace_size_log_2,
            final_step_eval_addresses: main_layer_input_addresses_per_layer[layer_idx].clone(),
            final_step_eval_degree: 2,
            extra_evaluations_addresses: main_layer_orphan_output_addresses_per_layer[layer_idx]
                .clone(),
        });
    }

    // ------------------------------------------------------------------
    // whir
    // ------------------------------------------------------------------
    assert_eq!(
        whir_schedule.whir_steps_schedule.len(),
        whir_schedule.whir_queries_schedule.len(),
    );
    assert_eq!(
        whir_schedule.whir_steps_schedule.len(),
        whir_schedule.whir_pow_schedule.len(),
    );
    assert_eq!(
        whir_schedule.whir_steps_schedule.len(),
        whir_schedule.whir_steps_lde_factors.len() + 1,
    );
    let initial_values_per_leaf = 1usize << whir_schedule.whir_steps_schedule[0];
    let tree_cap_size = whir_schedule.cap_size;
    let tree_cap_log2 = tree_cap_size.trailing_zeros() as usize;
    let initial_query_count = whir_schedule.whir_queries_schedule[0];

    let base_layer_dims = |g: ProofLayoutBaseLayerGeometry| -> WhirBaseLayerDims {
        // `cap_digest_count`: total digests across all LDE cosets for this
        // base layer. `allocate_tree_caps` sizes each coset at
        // `1 << (log_tree_cap_size - log_lde_factor)` digests (trace_holder.rs)
        // so the sum over `lde_factor` cosets is `1 << log_tree_cap_size`.
        let cap_digest_count = 1usize << g.log_tree_cap_size;
        let leaf_values_len = g.columns_count * initial_values_per_leaf;
        // Matches whir_fold.rs:1765-1776 and the setup_columns_count==0
        // branch at 1846.
        let path_len = if g.columns_count == 0 {
            0
        } else {
            (g.log_domain_size - g.log_rows_per_leaf - (g.log_tree_cap_size - g.log_lde_factor))
                as usize
        };
        WhirBaseLayerDims {
            num_columns: g.columns_count,
            cap_digest_count,
            query_count: initial_query_count,
            leaf_values_len,
            path_len,
        }
    };

    let mut folded_trace_len_log2 = initial_trace_size_log_2;
    let mut intermediate = Vec::with_capacity(whir_schedule.whir_steps_lde_factors.len());
    for (oracle_idx, &lde_factor) in whir_schedule.whir_steps_lde_factors.iter().enumerate() {
        folded_trace_len_log2 -= whir_schedule.whir_steps_schedule[oracle_idx];
        let values_per_leaf_log2 = whir_schedule.whir_steps_schedule[oracle_idx + 1];
        let path_len = folded_trace_len_log2 + lde_factor.trailing_zeros() as usize
            - values_per_leaf_log2
            - tree_cap_log2;
        intermediate.push(WhirIntermediateDims {
            cap_digest_count: tree_cap_size,
            query_count: whir_schedule.whir_queries_schedule[oracle_idx + 1],
            leaf_values_len: 1usize << values_per_leaf_log2,
            path_len,
        });
    }

    let whir = WhirDims {
        setup: base_layer_dims(setup_geometry),
        memory: base_layer_dims(memory_geometry),
        witness: base_layer_dims(witness_geometry),
        intermediate,
        num_ood_samples: whir_schedule.whir_steps_lde_factors.len(),
        total_sumcheck_polys: whir_schedule.whir_steps_schedule.iter().sum::<usize>(),
        pow_rounds: whir_schedule.whir_pow_schedule.len(),
        // GPU prover currently leaves `WhirPolyCommitProof::final_monomials`
        // as `vec![]` (whir_fold.rs:1870). If a future commit teaches WHIR
        // to emit the final monomial basis, lift this from the schedule via
        // `initial_trace_size_log_2 - sum(whir_steps_schedule)`.
        final_monomials_len: 0,
    };

    ProofLayoutInputs {
        output_evaluations,
        backward_layers,
        whir,
    }
}
