use proc_macro2::TokenStream;
use quote::{quote, TokenStreamExt};

use crate::mersenne_wrapper::MersenneWrapper;
use prover::cs::definitions::GKRAddress;
use prover::cs::gkr_compiler::{
    GKRCircuitArtifact, GKRLayerDescription, NoFieldGKRRelation, OutputType,
};
use prover::field::{Field, FieldExtension, PrimeField};
use prover::gkr::prover::{GKRProof, WhirSchedule};
use prover::merkle_trees::ColumnMajorMerkleTreeConstructor;

pub mod constraint_kernel;
pub mod dim_reducing_layer;
pub mod standard_layer;

/// Output group metadata used during code generation.
#[derive(Clone, Debug)]
pub struct GKROutputGroupInfo {
    pub output_type: OutputType,
    pub num_addresses: usize,
}

fn addr_to_idx(addr: &GKRAddress, sorted: &[GKRAddress]) -> usize {
    sorted
        .binary_search(addr)
        .unwrap_or_else(|_| panic!("address {:?} not found in sorted list", addr))
}

fn transform_gkr_address(addr: &GKRAddress) -> TokenStream {
    match addr {
        GKRAddress::BaseLayerWitness(offset) => {
            quote! { GKRAddress::BaseLayerWitness(#offset) }
        }
        GKRAddress::BaseLayerMemory(offset) => {
            quote! { GKRAddress::BaseLayerMemory(#offset) }
        }
        GKRAddress::InnerLayer { layer, offset } => {
            quote! { GKRAddress::InnerLayer { layer: #layer, offset: #offset } }
        }
        GKRAddress::Setup(offset) => {
            quote! { GKRAddress::Setup(#offset) }
        }
        GKRAddress::ScratchSpace(offset) => {
            quote! { GKRAddress::ScratchSpace(#offset) }
        }
        GKRAddress::Cached { layer, offset } => {
            quote! { GKRAddress::Cached { layer: #layer, offset: #offset } }
        }
    }
}

fn collect_sorted_unique_addrs(layer: &GKRLayerDescription) -> Vec<GKRAddress> {
    use std::collections::BTreeSet;
    let mut addrs = BTreeSet::new();

    for gate in layer
        .gates
        .iter()
        .chain(layer.gates_with_external_connections.iter())
    {
        use NoFieldGKRRelation as R;
        match &gate.enforced_relation {
            R::LinearBaseFieldRelation { input, .. } => {
                for (_, addr) in input.linear_terms.iter() {
                    addrs.insert(*addr);
                }
            }
            R::MaxQuadratic { input, .. } => {
                for (addr, terms) in input.quadratic_terms.iter() {
                    addrs.insert(*addr);
                    for &(_, b) in terms.iter() {
                        addrs.insert(b);
                    }
                }
                for &(_, addr) in input.linear_terms.iter() {
                    addrs.insert(addr);
                }
            }
            R::EnforceConstraintsMaxQuadratic { input } => {
                for ((a, b), _) in &input.quadratic_terms {
                    addrs.insert(*a);
                    addrs.insert(*b);
                }
                for (addr, _) in &input.linear_terms {
                    addrs.insert(*addr);
                }
            }
            R::Copy { input, .. } => {
                addrs.insert(*input);
            }
            R::InitialGrandProductFromCaches { input, .. } | R::TrivialProduct { input, .. } => {
                addrs.insert(input[0]);
                addrs.insert(input[1]);
            }
            R::UnbalancedGrandProductWithCache { scalar, input, .. } => {
                addrs.insert(*scalar);
                addrs.insert(*input);
            }
            R::MaskIntoIdentityProduct { input, mask, .. } => {
                addrs.insert(*input);
                addrs.insert(*mask);
            }
            R::MaterializeSingleLookupInput { input, .. } => {
                for (_, addr) in &input.input.linear_terms {
                    addrs.insert(*addr);
                }
            }
            R::MaterializedVectorLookupInput { input, .. } => {
                for col in &input.columns {
                    for (_, addr) in &col.linear_terms {
                        addrs.insert(*addr);
                    }
                }
            }
            R::LookupWithCachedDensAndSetup { input, setup, .. } => {
                addrs.insert(input[0]);
                addrs.insert(input[1]);
                addrs.insert(setup[0]);
                addrs.insert(setup[1]);
            }
            R::LookupPairFromBaseInputs { input, .. } => {
                for (_, addr) in &input[0].input.linear_terms {
                    addrs.insert(*addr);
                }
                for (_, addr) in &input[1].input.linear_terms {
                    addrs.insert(*addr);
                }
            }
            R::LookupPairFromMaterializedBaseInputs { input, .. } => {
                addrs.insert(input[0]);
                addrs.insert(input[1]);
            }
            R::LookupFromMaterializedBaseInputWithSetup { input, setup, .. } => {
                addrs.insert(*input);
                addrs.insert(setup[0]);
                addrs.insert(setup[1]);
            }
            R::LookupUnbalancedPairWithMaterializedBaseInputs {
                input, remainder, ..
            } => {
                addrs.insert(input[0]);
                addrs.insert(input[1]);
                addrs.insert(*remainder);
            }
            R::LookupPairFromVectorInputs { input, .. } => {
                for col in &input[0].columns {
                    for (_, addr) in &col.linear_terms {
                        addrs.insert(*addr);
                    }
                }
                for col in &input[1].columns {
                    for (_, addr) in &col.linear_terms {
                        addrs.insert(*addr);
                    }
                }
            }
            R::LookupPairFromMaterializedVectorInputs { input, .. }
            | R::LookupPairFromCachedVectorInputs { input, .. } => {
                addrs.insert(input[0]);
                addrs.insert(input[1]);
            }
            R::LookupUnbalancedPairWithMaterializedVectorInputs {
                input, remainder, ..
            } => {
                addrs.insert(input[0]);
                addrs.insert(input[1]);
                addrs.insert(*remainder);
            }
            R::AggregateLookupRationalPair { input, .. } => {
                addrs.insert(input[0][0]);
                addrs.insert(input[0][1]);
                addrs.insert(input[1][0]);
                addrs.insert(input[1][1]);
            }
        }
    }
    addrs.into_iter().collect()
}

fn collect_output_addrs(layer: &GKRLayerDescription) -> Vec<GKRAddress> {
    use std::collections::BTreeSet;
    let mut addrs = BTreeSet::new();

    for gate in layer
        .gates
        .iter()
        .chain(layer.gates_with_external_connections.iter())
    {
        use NoFieldGKRRelation as R;
        match &gate.enforced_relation {
            R::EnforceConstraintsMaxQuadratic { .. } => {}
            R::LinearBaseFieldRelation { output, .. }
            | R::MaxQuadratic { output, .. }
            | R::Copy { output, .. }
            | R::InitialGrandProductFromCaches { output, .. }
            | R::UnbalancedGrandProductWithCache { output, .. }
            | R::TrivialProduct { output, .. }
            | R::MaskIntoIdentityProduct { output, .. }
            | R::MaterializeSingleLookupInput { output, .. }
            | R::MaterializedVectorLookupInput { output, .. } => {
                addrs.insert(*output);
            }
            R::LookupPairFromBaseInputs { output, .. }
            | R::LookupPairFromMaterializedBaseInputs { output, .. }
            | R::LookupUnbalancedPairWithMaterializedBaseInputs { output, .. }
            | R::LookupFromMaterializedBaseInputWithSetup { output, .. }
            | R::LookupPairFromVectorInputs { output, .. }
            | R::LookupPairFromMaterializedVectorInputs { output, .. }
            | R::LookupPairFromCachedVectorInputs { output, .. }
            | R::LookupUnbalancedPairWithMaterializedVectorInputs { output, .. }
            | R::LookupWithCachedDensAndSetup { output, .. }
            | R::AggregateLookupRationalPair { output, .. } => {
                addrs.insert(output[0]);
                addrs.insert(output[1]);
            }
        }
    }
    addrs.into_iter().collect()
}

fn collect_extra_addrs_from_cached_relations(
    layer: &GKRLayerDescription,
    input_sorted_addrs: &[GKRAddress],
) -> Vec<GKRAddress> {
    use std::collections::BTreeSet;
    let input_set: BTreeSet<GKRAddress> = input_sorted_addrs.iter().copied().collect();
    let mut extra = BTreeSet::new();
    for (_cached_addr, relation) in layer.cached_relations.iter() {
        for dep in relation.dependencies() {
            if !input_set.contains(&dep) {
                extra.insert(dep);
            }
        }
    }
    extra.into_iter().collect()
}

fn compute_max_pow(layer: &GKRLayerDescription) -> usize {
    use NoFieldGKRRelation as R;
    let mut max_pow = 0usize;
    for gate in layer
        .gates
        .iter()
        .chain(layer.gates_with_external_connections.iter())
    {
        if let R::EnforceConstraintsMaxQuadratic { input } = &gate.enforced_relation {
            for (_, terms) in &input.quadratic_terms {
                for &(_, pow) in terms.iter() {
                    max_pow = max_pow.max(pow);
                }
            }
            for (_, terms) in &input.linear_terms {
                for &(_, pow) in terms.iter() {
                    max_pow = max_pow.max(pow);
                }
            }
            for &(_, pow) in input.constants.iter() {
                max_pow = max_pow.max(pow);
            }
        }
    }
    max_pow
}

/// Output of the GKR inlined code generator, split into per-file token streams.
pub struct GeneratedGKRFiles {
    /// Per-circuit compile-time constants (GKR_ROUNDS, GKR_ADDRS, etc.) and static data.
    pub constants: TokenStream,
    /// GKR verifier: layer functions and the main `verify_gkr_sumcheck` entry point.
    pub gkr: TokenStream,
    /// Module root: re-exports.
    pub mod_rs: TokenStream,
    /// WHIR round functions (stub until M1 step 12).
    pub whir: TokenStream,
    /// Merkle path verification (stub until M1 step 8).
    pub merkle: TokenStream,
}

pub fn generate_gkr_inlined<MW: MersenneWrapper, F: PrimeField, E: FieldExtension<F> + Field, T>(
    compiled_circuit: &GKRCircuitArtifact<F>,
    proof: &GKRProof<F, E, T>,
    final_trace_size_log_2: usize,
    whir_schedule: &WhirSchedule,
) -> GeneratedGKRFiles
where
    T: ColumnMajorMerkleTreeConstructor<F>,
    [(); E::DEGREE]: Sized,
{
    let num_standard_layers = compiled_circuit.layers.len();
    let initial_layer_for_sumcheck = *proof
        .sumcheck_intermediate_values
        .keys()
        .max()
        .expect("proof must have sumcheck values");

    // Precompute sorted input addresses for each standard layer.
    let standard_sorted_addrs: Vec<Vec<GKRAddress>> = compiled_circuit
        .layers
        .iter()
        .map(|l| collect_sorted_unique_addrs(l))
        .collect();

    // Build dim-reducing iteration-order addresses.
    let build_dim_reducing_addrs = |layer_idx: usize| -> Vec<GKRAddress> {
        let mut addrs = Vec::new();
        if layer_idx == num_standard_layers {
            for (_, group_addrs) in compiled_circuit.global_output_map.iter() {
                for addr in group_addrs.iter() {
                    addrs.push(*addr);
                }
            }
        } else {
            let mut off = 0;
            for (output_type, group_addrs) in compiled_circuit.global_output_map.iter() {
                match output_type {
                    OutputType::PermutationProduct => {
                        for i in 0..group_addrs.len() {
                            addrs.push(GKRAddress::InnerLayer {
                                layer: layer_idx,
                                offset: off + i,
                            });
                        }
                        off += group_addrs.len();
                    }
                    _ => {
                        addrs.push(GKRAddress::InnerLayer {
                            layer: layer_idx,
                            offset: off,
                        });
                        addrs.push(GKRAddress::InnerLayer {
                            layer: layer_idx,
                            offset: off + 1,
                        });
                        off += 2;
                    }
                }
            }
        }
        addrs
    };

    let dim_reducing_sorted_addrs: Vec<Vec<GKRAddress>> = (num_standard_layers
        ..=initial_layer_for_sumcheck)
        .map(|layer_idx| {
            let mut addrs = build_dim_reducing_addrs(layer_idx);
            addrs.sort();
            addrs
        })
        .collect();

    let output_sorted_addrs_per_layer: Vec<Vec<GKRAddress>> = (0..num_standard_layers)
        .map(|layer_idx| {
            use std::collections::BTreeSet;
            let mut addrs: BTreeSet<GKRAddress> = BTreeSet::new();
            if layer_idx + 1 < num_standard_layers {
                // Regular: layer L+1's input addresses (from fold)
                for a in &standard_sorted_addrs[layer_idx + 1] {
                    addrs.insert(*a);
                }
                // Extra: cached relation dependencies at layer L+1
                let extras = collect_extra_addrs_from_cached_relations(
                    &compiled_circuit.layers[layer_idx + 1],
                    &standard_sorted_addrs[layer_idx + 1],
                );
                for a in &extras {
                    addrs.insert(*a);
                }
            } else if !dim_reducing_sorted_addrs.is_empty() {
                // Highest standard layer: claims come from dim-reducing fold
                for a in &dim_reducing_sorted_addrs[0] {
                    addrs.insert(*a);
                }
            } else {
                for a in &standard_sorted_addrs[layer_idx] {
                    addrs.insert(*a);
                }
            }
            addrs.into_iter().collect()
        })
        .collect();

    let get_output_sorted_addrs =
        |layer_idx: usize| -> &[GKRAddress] { &output_sorted_addrs_per_layer[layer_idx] };

    // Output group info
    let output_groups: Vec<GKROutputGroupInfo> = compiled_circuit
        .global_output_map
        .iter()
        .map(|(ot, addrs)| GKROutputGroupInfo {
            output_type: *ot,
            num_addresses: addrs.len(),
        })
        .collect();

    // --- Buffer size constants ---
    let max_sumcheck_rounds = proof
        .sumcheck_intermediate_values
        .values()
        .map(|v| v.sumcheck_num_rounds)
        .max()
        .unwrap_or(0);

    let max_unique_addrs_standard = compiled_circuit
        .layers
        .iter()
        .map(|l| collect_sorted_unique_addrs(l).len())
        .max()
        .unwrap_or(0);

    let max_output_addrs = output_sorted_addrs_per_layer
        .iter()
        .map(|a| a.len())
        .max()
        .unwrap_or(0);
    let max_merged_claims = (0..num_standard_layers)
        .map(|layer_idx| {
            let regular = standard_sorted_addrs[layer_idx].len();
            let extras = collect_extra_addrs_from_cached_relations(
                &compiled_circuit.layers[layer_idx],
                &standard_sorted_addrs[layer_idx],
            )
            .len();
            regular + extras
        })
        .max()
        .unwrap_or(0);
    let max_unique_addrs_standard = max_unique_addrs_standard
        .max(max_output_addrs)
        .max(max_merged_claims);

    let dim_reducing_addr_count: usize = compiled_circuit
        .global_output_map
        .iter()
        .map(|(_, addrs)| addrs.len())
        .sum();
    let max_addrs = max_unique_addrs_standard.max(dim_reducing_addr_count);

    let max_pow = compiled_circuit
        .layers
        .iter()
        .map(|l| compute_max_pow(l))
        .max()
        .unwrap_or(0)
        + 1;

    let total_output_polys: usize = compiled_circuit
        .global_output_map
        .iter()
        .map(|(_, addrs)| addrs.len())
        .sum();
    let max_evals = total_output_polys * (1usize << final_trace_size_log_2);

    let degree = E::DEGREE;
    let digest_words = prover::transcript::blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;
    let block_words = prover::transcript::blake2s_u32::BLAKE2S_BLOCK_SIZE_U32_WORDS;
    let dim_reducing_words_per_addr = 4 * degree;
    let standard_words_per_addr = 2 * degree;
    let max_data_words = (max_addrs * dim_reducing_words_per_addr)
        .max(max_addrs * standard_words_per_addr)
        .max(max_evals * degree);
    let total = digest_words + max_data_words;
    let eval_buf_size = (total + block_words - 1) / block_words * block_words;

    // seed + 4 cubic coefficients, rounded up to next Blake2s block boundary
    let commit_buf_total = digest_words + 4 * degree;
    let commit_buf_size = (commit_buf_total + block_words - 1) / block_words * block_words;

    let initial_transcript_num_u32_words = {
        let mut tmp = Vec::<u32>::new();
        if let Some(top_bits) = proof.inits_and_teardowns_top_bits {
            tmp.push(top_bits);
        }
        proof.external_challenges.flatten_into_buffer(&mut tmp);
        proof
            .whir_proof
            .setup_commitment
            .commitment
            .cap
            .add_into_buffer(&mut tmp);
        proof
            .whir_proof
            .memory_commitment
            .commitment
            .cap
            .add_into_buffer(&mut tmp);
        proof
            .whir_proof
            .witness_commitment
            .commitment
            .cap
            .add_into_buffer(&mut tmp);
        tmp.len()
    };

    // --- Generate per-layer functions ---
    let mut layer_functions = TokenStream::new();

    // Standard layers
    for layer_idx in 0..num_standard_layers {
        layer_functions.extend(standard_layer::generate_layer_compute_claim::<MW>(
            &compiled_circuit.layers[layer_idx],
            layer_idx,
            get_output_sorted_addrs(layer_idx),
        ));
        let layer_max_pow = compute_max_pow(&compiled_circuit.layers[layer_idx]) + 1;
        layer_functions.extend(
            standard_layer::generate_layer_final_step_accumulator::<MW, F>(
                &compiled_circuit.layers[layer_idx],
                layer_idx,
                &standard_sorted_addrs[layer_idx],
                layer_max_pow,
            ),
        );
    }

    // Dim-reducing layers
    for (dim_idx, layer_idx) in (num_standard_layers..=initial_layer_for_sumcheck).enumerate() {
        layer_functions.extend(
            dim_reducing_layer::generate_dim_reducing_compute_claim::<MW>(
                &output_groups,
                layer_idx,
            ),
        );
        let iteration_order_addrs = build_dim_reducing_addrs(layer_idx);
        let sorted = &dim_reducing_sorted_addrs[dim_idx];
        let input_sorted_indices: Vec<usize> = iteration_order_addrs
            .iter()
            .map(|addr| addr_to_idx(addr, sorted))
            .collect();
        layer_functions.extend(
            dim_reducing_layer::generate_dim_reducing_final_step_accumulator::<MW>(
                &output_groups,
                &input_sorted_indices,
                layer_idx,
            ),
        );
    }

    // --- Generate static data ---
    let mut static_data = TokenStream::new();

    // Only layer 0 sorted addresses are needed at runtime (returned in GKRVerifierOutput)
    if !standard_sorted_addrs.is_empty() {
        let sorted = &standard_sorted_addrs[0];
        let mut addrs_stream = TokenStream::new();
        addrs_stream.append_separated(sorted.iter().map(|a| transform_gkr_address(a)), quote! {,});
        static_data.extend(quote! {
            pub const LAYER_0_SORTED_ADDRS: &[GKRAddress] = &[#addrs_stream];
        });
    }

    // Base layer additional openings
    let base_layer_additional_openings: Vec<TokenStream> = if !compiled_circuit.layers.is_empty() {
        compiled_circuit.layers[0]
            .additional_base_layer_openings
            .iter()
            .map(|a| transform_gkr_address(a))
            .collect()
    } else {
        vec![]
    };
    let mut base_openings_stream = TokenStream::new();
    base_openings_stream.append_separated(base_layer_additional_openings.iter(), quote! {,});

    // --- Generate the main verify function body ---
    let total_layers = initial_layer_for_sumcheck + 1;

    let field_struct = MW::field_struct();
    let quartic_struct = MW::quartic_struct();
    let quartic_zero = MW::quartic_zero();
    let quartic_one = MW::quartic_one();

    let mut main_body = TokenStream::new();

    // Transcript setup
    main_body.extend(quote! {
        let mut transcript_buf = LazyVec::<u32, GKR_TRANSCRIPT_U32>::new();
        for _ in 0..GKR_TRANSCRIPT_U32 {
            transcript_buf.push(I::read_word());
        }
        let mut seed = Blake2sTranscript::commit_initial(transcript_buf.as_slice());
        let mut hasher = DelegatedBlake2sState::new();

        let mut init_challenges = [#quartic_zero; 3];
        draw_field_els_into::<#field_struct, #quartic_struct>(&mut hasher, &mut seed, &mut init_challenges);
        let lookup_additive_challenge = init_challenges[1];
        let constraints_batch_challenge = init_challenges[2];
    });

    // Inline build_initial_claims with all values hardcoded
    let total_output_polys: usize = output_groups.iter().map(|g| g.num_addresses).sum();
    let evals_per_poly = 1usize << final_trace_size_log_2;
    let total_evals_needed = total_output_polys * evals_per_poly;
    let num_challenges = final_trace_size_log_2 + 1;
    let evaluation_point_len = final_trace_size_log_2;

    // Generate the per-group claim accumulation (unrolled)
    let mut claim_accum_body = TokenStream::new();
    let mut eval_offset_val = 0usize;
    for group in &output_groups {
        let count = match group.output_type {
            OutputType::PermutationProduct => group.num_addresses,
            _ => 2,
        };
        for _ in 0..count {
            let off = eval_offset_val;
            let end = eval_offset_val + evals_per_poly;
            claim_accum_body.extend(quote! {
                {
                    let vals: &[#quartic_struct; #evals_per_poly] =
                        evals_slice[#off..#end].try_into().unwrap_unchecked();
                    let eq_arr: &[#quartic_struct; #evals_per_poly] =
                        eq_buf.as_slice().try_into().unwrap_unchecked();
                    let claim = dot_eq(vals, eq_arr);
                    prev_claims.push(claim);
                }
            });
            eval_offset_val += evals_per_poly;
        }
    }

    main_body.extend(quote! {
        // --- build initial claims ---
        let mut evals_flat = [core::mem::MaybeUninit::<#quartic_struct>::uninit(); GKR_EVALS];
        let evals_slice = unsafe {
            let dst = core::slice::from_raw_parts_mut(
                evals_flat.as_mut_ptr().cast::<#quartic_struct>(), #total_evals_needed);
            read_field_els::<#field_struct, #quartic_struct, I>(dst);
            core::slice::from_raw_parts(evals_flat.as_ptr().cast::<#quartic_struct>(), #total_evals_needed)
        };
        commit_field_els::<#field_struct, #quartic_struct>(&mut seed, evals_slice);

        let mut all_challenges = [#quartic_zero; GKR_ROUNDS + 1];
        draw_field_els_into::<#field_struct, #quartic_struct>(
            &mut hasher, &mut seed, &mut all_challenges[..#num_challenges]);
        let batching_challenge = all_challenges[#num_challenges - 1];

        let mut eq_buf = LazyVec::<#quartic_struct, #evals_per_poly>::new();
        let eq_challenges: &[#quartic_struct; #evaluation_point_len] =
            all_challenges[..#evaluation_point_len].try_into().unwrap_unchecked();
        make_eq_poly(eq_challenges, &mut eq_buf);

        let mut prev_claims: LazyVec<#quartic_struct, GKR_ADDRS> = LazyVec::new();
        #claim_accum_body

        let mut prev_point = [#quartic_zero; GKR_ROUNDS];
        prev_point[..#evaluation_point_len].copy_from_slice(&all_challenges[..#evaluation_point_len]);

        let mut state = LayerState {
            prev_point,
            prev_point_len: #evaluation_point_len,
            prev_claims,
            batching_challenge,
        };

        let mut eval_buf = AlignedArray64::<u32, GKR_EVAL_BUF>::new_uninit();
    });

    // Dim-reducing layers (top to bottom, reversed)
    for config_idx in (num_standard_layers..=initial_layer_for_sumcheck).rev() {
        let proof_values = proof
            .sumcheck_intermediate_values
            .get(&config_idx)
            .expect("missing sumcheck values");
        let num_sumcheck_rounds = proof_values.sumcheck_num_rounds;
        let dim_idx = config_idx - num_standard_layers;
        let num_input_addrs = dim_reducing_sorted_addrs[dim_idx].len();

        let compute_claim_fn = quote::format_ident!("dim_reducing_{}_compute_claim", config_idx);
        let final_step_fn =
            quote::format_ident!("dim_reducing_{}_final_step_accumulator", config_idx);

        let num_regular_rounds = num_sumcheck_rounds - 1;

        main_body.extend(quote! {
            {
                let initial_claim = #compute_claim_fn(
                    &state.prev_claims,
                    state.batching_challenge,
                );

                let (final_claim, final_eq_prefactor) =
                    verify_sumcheck_rounds::<#field_struct, #quartic_struct, I, #num_regular_rounds, GKR_COMMIT_BUF>(
                        &mut seed,
                        initial_claim,
                        &mut state.prev_point,
                        #config_idx,
                    )?;
                let mut fc_len = #num_regular_rounds;

                let data_words = #num_input_addrs * 4 * <#quartic_struct as FieldExtension<#field_struct>>::DEGREE;
                read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);

                {
                    let evals: &[[#quartic_struct; 4]] = eval_buf.transmute_subslice(
                        BLAKE2S_DIGEST_SIZE_U32_WORDS, #num_input_addrs);
                    let f = #final_step_fn(evals, state.batching_challenge);
                    verify_final_step_check::<#field_struct, #quartic_struct>(
                        f,
                        *state.prev_point.get_unchecked(state.prev_point_len - 1),
                        final_eq_prefactor,
                        final_claim,
                        #config_idx,
                    )?;
                }

                commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);

                let mut draw_buf = [#quartic_zero; 3];
                draw_field_els_into::<#field_struct, #quartic_struct>(&mut hasher, &mut seed, &mut draw_buf);
                let r_before_last = draw_buf[0];
                let r_last = draw_buf[1];
                let next_batching = draw_buf[2];

                *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
                fc_len += 1;
                *state.prev_point.get_unchecked_mut(fc_len) = r_last;
                fc_len += 1;

                const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
                const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
                let mut eq4 = LazyVec::<#quartic_struct, DIM_REDUCING_EQ_SIZE>::new();
                make_eq_poly(&[r_before_last, r_last], &mut eq4);
                let evals: &[[#quartic_struct; DIM_REDUCING_EQ_SIZE]] = eval_buf.transmute_subslice(
                    BLAKE2S_DIGEST_SIZE_U32_WORDS, #num_input_addrs);
                let eq4_arr: &[#quartic_struct; DIM_REDUCING_EQ_SIZE] =
                    eq4.as_slice().try_into().unwrap_unchecked();
                state.prev_claims.clear();
                for i in 0..#num_input_addrs {
                    let e = evals.get_unchecked(i);
                    state.prev_claims.push(dot_eq(e, eq4_arr));
                }

                state.batching_challenge = next_batching;
                state.prev_point_len = fc_len;
            }
        });
    }

    // Build challenge_powers once for all standard layers
    if num_standard_layers > 0 {
        let mul_cb = MW::mul_assign(quote! { pow }, quote! { constraints_batch_challenge });
        main_body.extend(quote! {
            let challenge_powers: [#quartic_struct; GKR_MAX_POW] = {
                let mut lv = LazyVec::<#quartic_struct, GKR_MAX_POW>::new();
                let mut pow = #quartic_one;
                for _ in 0..GKR_MAX_POW {
                    lv.push(pow);
                    #mul_cb;
                }
                unsafe { lv.into_array() }
            };
        });
    }

    // Standard layers (top to bottom, reversed)
    for config_idx in (0..num_standard_layers).rev() {
        let proof_values = proof
            .sumcheck_intermediate_values
            .get(&config_idx)
            .expect("missing sumcheck values");
        let num_sumcheck_rounds = proof_values.sumcheck_num_rounds;
        let num_dedup_addrs = standard_sorted_addrs[config_idx].len();

        let compute_claim_fn = quote::format_ident!("layer_{}_compute_claim", config_idx);
        let final_step_fn = quote::format_ident!("layer_{}_final_step_accumulator", config_idx);

        let num_regular_rounds = num_sumcheck_rounds - 1;

        let extra_addrs = collect_extra_addrs_from_cached_relations(
            &compiled_circuit.layers[config_idx],
            &standard_sorted_addrs[config_idx],
        );
        let num_extra = extra_addrs.len();

        let has_extras = num_extra > 0;
        let fold_and_extras_code = if has_extras {
            // Compute the target address layout: regular(this_layer) + extras(this_layer)
            let regular_set: std::collections::BTreeSet<GKRAddress> =
                standard_sorted_addrs[config_idx].iter().copied().collect();
            let mut target_addrs: std::collections::BTreeSet<GKRAddress> = regular_set.clone();
            for a in &extra_addrs {
                target_addrs.insert(*a);
            }
            let target_addrs: Vec<GKRAddress> = target_addrs.into_iter().collect();

            let sub = MW::sub_assign(quote! { diff }, quote! { f0 });
            let mul_r = MW::mul_assign(quote! { diff }, quote! { last_r });
            let add_f0 = MW::add_assign(quote! { diff }, quote! { f0 });
            let mut build_stmts = TokenStream::new();
            build_stmts.extend(quote! {
                let mut extra_evals = [#quartic_zero; #num_extra];
                read_field_els::<#field_struct, #quartic_struct, I>(&mut extra_evals);
                commit_field_els::<#field_struct, #quartic_struct>(&mut seed, &extra_evals);

                let final_step_evals: &[[#quartic_struct; 2]] = eval_buf.transmute_subslice(
                    BLAKE2S_DIGEST_SIZE_U32_WORDS, #num_dedup_addrs);
                state.prev_claims.clear();
            });

            let mut regular_idx = 0usize;
            let mut extra_idx = 0usize;
            for addr in target_addrs.iter() {
                if regular_set.contains(addr) {
                    build_stmts.extend(quote! {
                        {
                            let ev = unsafe { final_step_evals.get_unchecked(#regular_idx) };
                            let f0 = ev[0];
                            let mut diff = ev[1];
                            #sub;
                            #mul_r;
                            #add_f0;
                            state.prev_claims.push(diff);
                        }
                    });
                    regular_idx += 1;
                } else {
                    build_stmts.extend(quote! {
                        state.prev_claims.push(extra_evals[#extra_idx]);
                    });
                    extra_idx += 1;
                }
            }

            build_stmts
        } else {
            // No extras: use the standard fold function
            quote! {
                fold_standard_claims::<#field_struct, #quartic_struct, #num_dedup_addrs, GKR_ADDRS, GKR_EVAL_BUF>(
                    &eval_buf, last_r, &mut state.prev_claims,
                );
            }
        };

        main_body.extend(quote! {
            {
                let initial_claim = #compute_claim_fn(
                    &state.prev_claims,
                    state.batching_challenge,
                );

                let (final_claim, final_eq_prefactor) =
                    verify_sumcheck_rounds::<#field_struct, #quartic_struct, I, #num_regular_rounds, GKR_COMMIT_BUF>(
                        &mut seed,
                        initial_claim,
                        &mut state.prev_point,
                        #config_idx,
                    )?;
                let mut fc_len = #num_regular_rounds;

                let data_words = #num_dedup_addrs * 2 * <#quartic_struct as FieldExtension<#field_struct>>::DEGREE;
                read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);

                {
                    let evals: &[[#quartic_struct; 2]] = eval_buf.transmute_subslice(
                        BLAKE2S_DIGEST_SIZE_U32_WORDS, #num_dedup_addrs);
                    let f = #final_step_fn(
                        evals,
                        state.batching_challenge,
                        lookup_additive_challenge,
                        &challenge_powers,
                    );
                    verify_final_step_check::<#field_struct, #quartic_struct>(
                        f,
                        *state.prev_point.get_unchecked(state.prev_point_len - 1),
                        final_eq_prefactor,
                        final_claim,
                        #config_idx,
                    )?;
                }

                commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);

                let mut draw_buf = [#quartic_zero; 2];
                draw_field_els_into::<#field_struct, #quartic_struct>(&mut hasher, &mut seed, &mut draw_buf);
                let last_r = draw_buf[0];
                let next_batching = draw_buf[1];

                *state.prev_point.get_unchecked_mut(fc_len) = last_r;
                fc_len += 1;

                #fold_and_extras_code

                state.batching_challenge = next_batching;
                state.prev_point_len = fc_len;
            }
        });
    }

    // Grand product accumulator and output
    main_body.extend(quote! {
        let grand_product_accumulator: #quartic_struct = read_field_el::<#field_struct, #quartic_struct, I>();
        commit_field_els::<#field_struct, #quartic_struct>(&mut seed, &[grand_product_accumulator]);

        let mut draw_buf = [#quartic_zero; 1];
        draw_field_els_into::<#field_struct, #quartic_struct>(&mut hasher, &mut seed, &mut draw_buf);
        let whir_batching_challenge = draw_buf[0];

        Ok(GKRVerifierOutput {
            base_layer_claims: state.prev_claims,
            base_layer_addrs: LAYER_0_SORTED_ADDRS,
            evaluation_point: state.prev_point,
            evaluation_point_len: state.prev_point_len,
            grand_product_accumulator,
            additional_base_layer_openings: BASE_LAYER_ADDITIONAL_OPENINGS,
            whir_batching_challenge,
            whir_transcript_seed: seed,
        })
    });

    let field_use_stmts = MW::field_use_statements();

    // trace_len_log2 = number of sumcheck rounds at the base (layer 0)
    let trace_len_log2 = proof
        .sumcheck_intermediate_values
        .get(&0)
        .expect("proof must have sumcheck values for layer 0")
        .sumcheck_num_rounds;

    let whir_rounds = whir_schedule.whir_steps_schedule.len();
    let whir_fold_steps = &whir_schedule.whir_steps_schedule;
    let whir_queries = &whir_schedule.whir_queries_schedule;
    let whir_pow_bits = &whir_schedule.whir_pow_schedule;
    let whir_lde_factors = &whir_schedule.whir_steps_lde_factors;
    let whir_base_lde_factor = whir_schedule.base_lde_factor;
    let whir_cap_size = whir_schedule.cap_size;
    let whir_cap_size_log2 = whir_cap_size.trailing_zeros() as usize;

    let total_fold_steps: usize = whir_fold_steps.iter().sum();
    assert!(
        trace_len_log2 >= total_fold_steps,
        "total fold steps ({}) exceed trace_len_log2 ({})",
        total_fold_steps,
        trace_len_log2
    );
    let final_m = trace_len_log2 - total_fold_steps;
    let final_monomials_len = 1usize << final_m;

    // Per-oracle claim counts from base layer (layer 0) sorted addresses
    let (num_memory_claims, num_witness_claims, num_setup_claims) = if !standard_sorted_addrs
        .is_empty()
    {
        let mut mem = 0usize;
        let mut wit = 0usize;
        let mut setup = 0usize;
        for addr in &standard_sorted_addrs[0] {
            match addr {
                GKRAddress::BaseLayerMemory(_) => mem += 1,
                GKRAddress::BaseLayerWitness(_) => wit += 1,
                GKRAddress::Setup(_) => setup += 1,
                _ => {} // inner/cached/scratch don't appear at base layer
            }
        }
        (mem, wit, setup)
    } else {
        (0, 0, 0)
    };
    let num_base_claims = num_memory_claims + num_witness_claims + num_setup_claims;

    // Base oracle depth: tree_depth = trace_len_log2 + log2(base_lde_factor) - initial_fold_steps
    // oracle_depth = tree_depth - log2(cap_size)
    let base_lde_factor_log2 = whir_base_lde_factor.trailing_zeros() as usize;
    let initial_fold_steps = whir_fold_steps[0];
    let base_oracle_depth =
        trace_len_log2 + base_lde_factor_log2 - initial_fold_steps - whir_cap_size_log2;

    // Intermediate oracle depths (one per round except the last)
    let num_intermediate_oracles = whir_rounds - 1;
    let mut whir_oracle_depths = Vec::with_capacity(num_intermediate_oracles);
    {
        let mut poly_size_log2 = trace_len_log2;
        for i in 0..num_intermediate_oracles {
            poly_size_log2 -= whir_fold_steps[i];
            let lde_factor_log2 = whir_lde_factors[i].trailing_zeros() as usize;
            let next_fold_steps = whir_fold_steps[i + 1];
            let depth = poly_size_log2 + lde_factor_log2 - next_fold_steps - whir_cap_size_log2;
            whir_oracle_depths.push(depth);
        }
    }

    let constants = quote! {
        use ::verifier_common::cs::definitions::GKRAddress;

        pub const GKR_ROUNDS: usize = #max_sumcheck_rounds;
        pub const GKR_ADDRS: usize = #max_addrs;
        pub const GKR_EVALS: usize = #max_evals;
        pub const GKR_TRANSCRIPT_U32: usize = #initial_transcript_num_u32_words;
        pub const GKR_MAX_POW: usize = #max_pow;
        pub const GKR_EVAL_BUF: usize = #eval_buf_size;
        pub const GKR_COMMIT_BUF: usize = #commit_buf_size;

        #static_data

        pub const BASE_LAYER_ADDITIONAL_OPENINGS: &[GKRAddress] = &[#base_openings_stream];

        pub const WHIR_ROUNDS: usize = #whir_rounds;
        pub const WHIR_FOLD_STEPS: [usize; #whir_rounds] = [#(#whir_fold_steps),*];
        pub const WHIR_QUERIES: [usize; #whir_rounds] = [#(#whir_queries),*];
        pub const WHIR_POW_BITS: [u32; #whir_rounds] = [#(#whir_pow_bits),*];
        pub const WHIR_BASE_LDE_FACTOR: usize = #whir_base_lde_factor;
        pub const WHIR_LDE_FACTORS: [usize; #num_intermediate_oracles] = [#(#whir_lde_factors),*];
        pub const WHIR_CAP_SIZE: usize = #whir_cap_size;

        pub const FINAL_M: usize = #final_m;
        pub const FINAL_MONOMIALS_LEN: usize = #final_monomials_len;

        pub const NUM_BASE_CLAIMS: usize = #num_base_claims;
        pub const NUM_MEMORY_CLAIMS: usize = #num_memory_claims;
        pub const NUM_WITNESS_CLAIMS: usize = #num_witness_claims;
        pub const NUM_SETUP_CLAIMS: usize = #num_setup_claims;

        pub const BASE_ORACLE_DEPTH: usize = #base_oracle_depth;
        pub const WHIR_ORACLE_DEPTHS: [usize; #num_intermediate_oracles] = [#(#whir_oracle_depths),*];
    };

    let gkr = quote! {
        #field_use_stmts
        use ::verifier_common::cs::definitions::GKRAddress;
        use ::verifier_common::gkr::{
            GKRVerifierOutput, GKRVerificationError,
            LayerState, LazyVec,
            verify_sumcheck_rounds, verify_final_step_check,
            fold_standard_claims,
            make_eq_poly, dot_eq,
            read_eval_data_from_nds, commit_eval_buffer,
            draw_field_els_into, read_field_el, read_field_els, commit_field_els,
        };
        use ::verifier_common::field_ops;
        use ::verifier_common::transcript::{Blake2sTranscript, Seed};
        use ::verifier_common::blake2s_u32::{
            AlignedArray64, DelegatedBlake2sState, BLAKE2S_DIGEST_SIZE_U32_WORDS,
        };
        use ::verifier_common::field::{Field, FieldExtension, PrimeField};
        use ::verifier_common::non_determinism_source::NonDeterminismSource;

        use super::constants::*;

        #layer_functions

        #[allow(unused_braces, unused_mut, unused_variables, unused_unsafe)]
        pub fn verify_gkr_sumcheck<
            I: NonDeterminismSource,
        >() -> Result<GKRVerifierOutput<'static, #quartic_struct, GKR_ROUNDS, GKR_ADDRS>, GKRVerificationError>
        {
            unsafe {
                #main_body
            }
        }
    };

    let mod_rs = quote! {
        pub mod constants;
        pub mod gkr;
        pub mod whir;
        pub mod merkle;

        pub use gkr::verify_gkr_sumcheck;
    };

    let whir = quote! {
        //! WHIR round functions — generated per-circuit.
        //! Populated starting from M1 step 12.
    };

    let merkle = quote! {
        //! Merkle path verification — generated per-circuit.
        //! Populated starting from M1 step 8.
    };

    GeneratedGKRFiles {
        constants,
        gkr,
        mod_rs,
        whir,
        merkle,
    }
}
