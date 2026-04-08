use proc_macro2::TokenStream;
use quote::{quote, TokenStreamExt};

use crate::mersenne_wrapper::MersenneWrapper;
pub use crate::utils::{
    addr_to_idx, coeff_to_internal_repr, collect_extra_addrs_from_cached_relations,
    collect_sorted_unique_addrs, compute_max_pow, transform_gkr_address,
};
use prover::cs::definitions::GKRAddress;
use prover::cs::gkr_compiler::{
    GKRCircuitArtifact, GKRLayerDescription, NoFieldGKRCacheRelation, OutputType,
};
use prover::field::{Field, FieldExtension, PrimeField};
use prover::gkr::prover::{GKRProof, WhirSchedule};
use prover::merkle_trees::ColumnMajorMerkleTreeConstructor;

pub mod constraint_kernel;
pub mod dim_reducing_layer;
pub mod standard_layer;

/// Describes a single base-layer oracle (setup, memory, or witness).
/// All three are structurally identical — only their column counts and
/// cap sizes differ.
#[derive(Clone, Debug)]
pub struct OracleInfo {
    pub num_columns: usize,
    pub cap_size: usize, // number of cap digests (not words)
    pub depth: usize,    // Merkle tree depth (0 for empty oracles)
}

pub struct GKRGeneratedFiles {
    pub constants: TokenStream,
    pub gkr: TokenStream,
    pub oracles: Vec<OracleInfo>, // [setup, memory, witness] order
    pub trace_len_log2: usize,
}

#[derive(Clone, Debug)]
pub struct GKROutputGroupInfo {
    pub output_type: OutputType,
    pub num_addresses: usize,
}

pub fn generate_gkr_common<MW: MersenneWrapper>() -> TokenStream {
    let field_struct = MW::field_struct();
    let quartic_struct = MW::quartic_struct();
    let quartic_one = MW::quartic_one();

    let sc_add_p1_c1 = MW::add_assign(quote! { p1 }, quote! { coeffs[1] });
    let sc_add_p1_c2 = MW::add_assign(quote! { p1 }, quote! { coeffs[2] });
    let sc_add_p1_c3 = MW::add_assign(quote! { p1 }, quote! { coeffs[3] });
    let sc_add_sum_p1 = MW::add_assign(quote! { sum }, quote! { p1 });
    let sc_mul_sum_eq = MW::mul_assign(quote! { sum }, quote! { eq_prefactor });
    let sc_mul_res_rk = MW::mul_assign(quote! { result }, quote! { r_k });
    let sc_add_res_c2 = MW::add_assign(quote! { result }, quote! { coeffs[2] });
    let sc_add_res_c1 = MW::add_assign(quote! { result }, quote! { coeffs[1] });
    let sc_add_res_c0 = MW::add_assign(quote! { result }, quote! { coeffs[0] });
    let sc_sub_omr_rk = MW::sub_assign(quote! { one_minus_r }, quote! { r_k });
    let sc_sub_omp_p = MW::sub_assign(quote! { one_minus_p }, quote! { p });
    let sc_mul_t_omp = MW::mul_assign(quote! { t }, quote! { one_minus_p });
    let sc_mul_rp_p = MW::mul_assign(quote! { rp }, quote! { p });
    let sc_add_t_rp = MW::add_assign(quote! { t }, quote! { rp });

    let fs_sub_eq0_lpp = MW::sub_assign(quote! { eq0 }, quote! { last_prev_point });
    let fs_mul_rhs_f0 = MW::mul_assign(quote! { rhs }, quote! { f[0] });
    let fs_mul_t_f1 = MW::mul_assign(quote! { t }, quote! { f[1] });
    let fs_add_rhs_t = MW::add_assign(quote! { rhs }, quote! { t });
    let fs_mul_rhs_eq = MW::mul_assign(quote! { rhs }, quote! { final_eq_prefactor });

    let fold_sub_diff_f0 = MW::sub_assign(quote! { diff }, quote! { f0 });
    let fold_mul_diff_lr = MW::mul_assign(quote! { diff }, quote! { last_r });
    let fold_add_diff_f0 = MW::add_assign(quote! { diff }, quote! { f0 });

    let field_from_u32 = MW::field_from_raw_repr_with_reduction(quote! { w });

    quote! {
        #[inline(always)]
        pub fn verify_sumcheck_rounds<
            I: NonDeterminismSource,
            const NUM_ROUNDS: usize,
            const COMMIT_BUF: usize,
        >(
            ts: &mut TranscriptState,
            initial_claim: #quartic_struct,
            challenges: &mut [#quartic_struct],
            layer_idx: usize,
        ) -> Result<(#quartic_struct, #quartic_struct), GKRVerificationError> {
            let mut claim = initial_claim;
            let mut eq_prefactor = #quartic_one;

            let coeff_data_words = 4 * EXT_DEGREE;

            let mut commit_buf = CommitBuf::<COMMIT_BUF>::new();
            let mut draw_buf = LazyVec::<u32, BLAKE2S_DIGEST_SIZE_U32_WORDS>::new();
            unsafe { draw_buf.set_len(BLAKE2S_DIGEST_SIZE_U32_WORDS); }

            for round in 0..NUM_ROUNDS {
                {
                    let mut i = 0;
                    while i < coeff_data_words {
                        commit_buf.data_write(i, I::read_word());
                        i += 1;
                    }
                }

                // Copy coefficients out before committing (commit borrows &mut self).
                let coeffs: [#quartic_struct; 4] = unsafe {
                    *commit_buf.data_as::<[#quartic_struct; 4]>(1).as_ptr()
                };

                let p0 = coeffs[0];
                let mut p1 = coeffs[0];
                #sc_add_p1_c1;
                #sc_add_p1_c2;
                #sc_add_p1_c3;

                let mut sum = p0;
                #sc_add_sum_p1;
                #sc_mul_sum_eq;

                if sum != claim {
                    return Err(GKRVerificationError::SumcheckRoundFailed {
                        layer: layer_idx,
                        round,
                    });
                }

                ts.commit(&mut commit_buf, coeff_data_words);

                ts.draw_raw(draw_buf.as_mut_slice());
                let r_k = {
                    let mut arr = LazyVec::<#field_struct, EXT_DEGREE>::new();
                    for i in 0..EXT_DEGREE {
                        let w = *draw_buf.get(i);
                        arr.push(#field_from_u32);
                    }
                    unsafe { core::mem::transmute::<[#field_struct; EXT_DEGREE], #quartic_struct>(arr.into_array()) }
                };

                {
                    let mut result = coeffs[3];
                    #sc_mul_res_rk;
                    #sc_add_res_c2;
                    #sc_mul_res_rk;
                    #sc_add_res_c1;
                    #sc_mul_res_rk;
                    #sc_add_res_c0;
                    claim = result;
                }
                {
                    let p = unsafe { *challenges.get_unchecked(round) };
                    let mut one_minus_r = #quartic_one;
                    #sc_sub_omr_rk;
                    let mut one_minus_p = #quartic_one;
                    #sc_sub_omp_p;
                    let mut t = one_minus_r;
                    #sc_mul_t_omp;
                    let mut rp = r_k;
                    #sc_mul_rp_p;
                    #sc_add_t_rp;
                    eq_prefactor = t;
                }

                unsafe { *challenges.get_unchecked_mut(round) = r_k };
            }

            Ok((claim, eq_prefactor))
        }

        #[inline(always)]
        pub fn verify_final_step_check(
            f: [#quartic_struct; 2],
            last_prev_point: #quartic_struct,
            final_eq_prefactor: #quartic_struct,
            final_claim: #quartic_struct,
            layer_idx: usize,
        ) -> Result<(), GKRVerificationError> {
            let mut eq0 = #quartic_one;
            #fs_sub_eq0_lpp;
            let mut rhs = eq0;
            #fs_mul_rhs_f0;
            let mut t = last_prev_point;
            #fs_mul_t_f1;
            #fs_add_rhs_t;
            #fs_mul_rhs_eq;
            if rhs != final_claim {
                return Err(GKRVerificationError::FinalStepCheckFailed { layer: layer_idx });
            }
            Ok(())
        }

        #[inline(always)]
        pub fn fold_standard_claims<
            const NUM_ADDRS: usize,
            const ADDRS: usize,
            const BUF: usize,
        >(
            eval_buf: &CommitBuf<BUF>,
            last_r: #quartic_struct,
            claims: &mut LazyVec<#quartic_struct, ADDRS>,
        ) {
            let final_step_evals: &[[#quartic_struct; 2]] =
                unsafe { eval_buf.data_as(NUM_ADDRS) };
            claims.clear();
            for i in 0..NUM_ADDRS {
                let evals = unsafe { final_step_evals.get_unchecked(i) };
                let f0 = evals[0];
                let mut diff = evals[1];
                #fold_sub_diff_f0;
                #fold_mul_diff_lr;
                #fold_add_diff_f0;
                claims.push(diff);
            }
        }
    }
}

/// Generate code to verify cache relations for a layer.
/// After sumcheck and fold, `state.prev_claims` has claims for all addresses
/// in `target_addrs` order. This generates checks for lookup-type cache relations.
///
/// Uses const descriptor arrays + compact loops instead of unrolling per-relation.
fn generate_cache_relation_checks<MW: MersenneWrapper, F: PrimeField>(
    layer: &GKRLayerDescription,
    target_addrs: &[GKRAddress],
    layer_idx: usize,
) -> TokenStream {
    let quartic_struct = MW::quartic_struct();
    let field_struct = MW::field_struct();
    let quartic_zero = MW::quartic_zero();
    let quartic_one = MW::quartic_one();

    let coeff_to_mont = |c: u32| -> u32 { F::from_u32_with_reduction(c).as_u32_raw_repr_reduced() };

    // Collect SingleColumnLookup descriptors: (cached_idx, constant, term_start, term_count)
    // and flat terms: (coeff_mont, dep_idx)
    let mut single_descs: Vec<(usize, u32, usize, usize)> = Vec::new();
    let mut single_terms: Vec<(u32, usize)> = Vec::new();

    // Collect VectorizedLookup descriptors: (cached_idx, col_start, col_count)
    // col entries: (constant_mont, term_start, term_count)
    // flat terms: (coeff_mont, dep_idx)
    let mut vector_descs: Vec<(usize, usize, usize)> = Vec::new();
    let mut vector_cols: Vec<(u32, usize, usize)> = Vec::new();
    let mut vector_terms: Vec<(u32, usize)> = Vec::new();

    // Collect VectorizedLookupSetup descriptors: (cached_idx, dep_start, dep_count)
    // flat deps: dep_idx
    let mut vsetup_descs: Vec<(usize, usize, usize)> = Vec::new();
    let mut vsetup_deps: Vec<usize> = Vec::new();

    let find_idx = |addr: &GKRAddress| -> usize {
        target_addrs
            .iter()
            .position(|a| a == addr)
            .unwrap_or_else(|| {
                panic!(
                    "Layer {}: cache dep {:?} not in target_addrs",
                    layer_idx, addr
                )
            })
    };

    for (cached_addr, relation) in layer.cached_relations.iter() {
        let cached_idx = find_idx(cached_addr);

        match relation {
            NoFieldGKRCacheRelation::SingleColumnLookup {
                relation: rel,
                range_check_width: _,
            } => {
                let term_start = single_terms.len();
                for &(coeff, ref addr) in rel.input.linear_terms.iter() {
                    single_terms.push((coeff_to_mont(coeff), find_idx(addr)));
                }
                single_descs.push((
                    cached_idx,
                    coeff_to_mont(rel.input.constant),
                    term_start,
                    rel.input.linear_terms.len(),
                ));
            }
            NoFieldGKRCacheRelation::VectorizedLookup(rel) => {
                let col_start = vector_cols.len();
                for column in rel.columns.iter() {
                    let t_start = vector_terms.len();
                    for &(coeff, ref addr) in column.linear_terms.iter() {
                        vector_terms.push((coeff_to_mont(coeff), find_idx(addr)));
                    }
                    vector_cols.push((
                        coeff_to_mont(column.constant),
                        t_start,
                        column.linear_terms.len(),
                    ));
                }
                vector_descs.push((cached_idx, col_start, rel.columns.len()));
            }
            NoFieldGKRCacheRelation::VectorizedLookupSetup(setup_addrs) => {
                let dep_start = vsetup_deps.len();
                for addr in setup_addrs.iter() {
                    vsetup_deps.push(find_idx(addr));
                }
                vsetup_descs.push((cached_idx, dep_start, setup_addrs.len()));
            }
            NoFieldGKRCacheRelation::MemoryTuple(_) => {}
        }
    }

    let mut checks = TokenStream::new();

    // SingleColumnLookup checks
    if !single_descs.is_empty() {
        let num_descs = single_descs.len();
        let sd_cached: Vec<usize> = single_descs.iter().map(|d| d.0).collect();
        let sd_const: Vec<u32> = single_descs.iter().map(|d| d.1).collect();
        let sd_start: Vec<usize> = single_descs.iter().map(|d| d.2).collect();
        let sd_count: Vec<usize> = single_descs.iter().map(|d| d.3).collect();

        let num_terms = single_terms.len();
        let st_coeff: Vec<u32> = single_terms.iter().map(|t| t.0).collect();
        let st_dep: Vec<usize> = single_terms.iter().map(|t| t.1).collect();

        let mul_base = MW::mul_assign_by_base(
            quote! { t },
            quote! { #field_struct::from_reduced_raw_repr(coeff) },
        );
        let add_exp = MW::add_assign(quote! { expected }, quote! { t });

        checks.extend(quote! {
            {
                const SC_DESCS: [(usize, u32, usize, usize); #num_descs] = [
                    #( (#sd_cached, #sd_const, #sd_start, #sd_count), )*
                ];
                const SC_TERMS: [(u32, usize); #num_terms] = [
                    #( (#st_coeff, #st_dep), )*
                ];
                let mut _sc = 0;
                while _sc < #num_descs {
                    let (cached_idx, constant, term_start, term_count) = SC_DESCS[_sc];
                    let mut expected: #quartic_struct =
                        <#quartic_struct as FieldExtension<#field_struct>>::from_base(
                            #field_struct::from_reduced_raw_repr(constant));
                    let mut _t = 0;
                    while _t < term_count {
                        let (coeff, dep_idx) = SC_TERMS[term_start + _t];
                        let mut t = *state.prev_claims.get_unchecked(dep_idx);
                        #mul_base;
                        #add_exp;
                        _t += 1;
                    }
                    let cached = *state.prev_claims.get_unchecked(cached_idx);
                    if expected != cached {
                        return Err(GKRVerificationError::CacheRelationFailed { layer: #layer_idx });
                    }
                    _sc += 1;
                }
            }
        });
    }

    // VectorizedLookup checks
    if !vector_descs.is_empty() {
        let num_descs = vector_descs.len();
        let vd_cached: Vec<usize> = vector_descs.iter().map(|d| d.0).collect();
        let vd_col_start: Vec<usize> = vector_descs.iter().map(|d| d.1).collect();
        let vd_col_count: Vec<usize> = vector_descs.iter().map(|d| d.2).collect();

        let num_cols = vector_cols.len();
        let vc_const: Vec<u32> = vector_cols.iter().map(|c| c.0).collect();
        let vc_term_start: Vec<usize> = vector_cols.iter().map(|c| c.1).collect();
        let vc_term_count: Vec<usize> = vector_cols.iter().map(|c| c.2).collect();

        let num_terms = vector_terms.len();
        let vt_coeff: Vec<u32> = vector_terms.iter().map(|t| t.0).collect();
        let vt_dep: Vec<usize> = vector_terms.iter().map(|t| t.1).collect();

        let mul_base = MW::mul_assign_by_base(
            quote! { t },
            quote! { #field_struct::from_reduced_raw_repr(coeff) },
        );
        let add_col = MW::add_assign(quote! { col_val }, quote! { t });
        let mul_ap = MW::mul_assign(quote! { term }, quote! { alpha_power });
        let add_exp = MW::add_assign(quote! { expected }, quote! { term });
        let mul_alpha = MW::mul_assign(quote! { alpha_power }, quote! { lookup_alpha });

        checks.extend(quote! {
            {
                const VL_DESCS: [(usize, usize, usize); #num_descs] = [
                    #( (#vd_cached, #vd_col_start, #vd_col_count), )*
                ];
                const VL_COLS: [(u32, usize, usize); #num_cols] = [
                    #( (#vc_const, #vc_term_start, #vc_term_count), )*
                ];
                const VL_TERMS: [(u32, usize); #num_terms] = [
                    #( (#vt_coeff, #vt_dep), )*
                ];
                let mut _vl = 0;
                while _vl < #num_descs {
                    let (cached_idx, col_start, col_count) = VL_DESCS[_vl];
                    let mut expected: #quartic_struct = #quartic_zero;
                    let mut alpha_power: #quartic_struct = #quartic_one;
                    let mut _c = 0;
                    while _c < col_count {
                        let (col_constant, term_start, term_count) = VL_COLS[col_start + _c];
                        let mut col_val: #quartic_struct =
                            <#quartic_struct as FieldExtension<#field_struct>>::from_base(
                                #field_struct::from_reduced_raw_repr(col_constant));
                        let mut _t = 0;
                        while _t < term_count {
                            let (coeff, dep_idx) = VL_TERMS[term_start + _t];
                            let mut t = *state.prev_claims.get_unchecked(dep_idx);
                            #mul_base;
                            #add_col;
                            _t += 1;
                        }
                        let mut term = col_val;
                        #mul_ap;
                        #add_exp;
                        #mul_alpha;
                        _c += 1;
                    }
                    let cached = *state.prev_claims.get_unchecked(cached_idx);
                    if expected != cached {
                        return Err(GKRVerificationError::CacheRelationFailed { layer: #layer_idx });
                    }
                    _vl += 1;
                }
            }
        });
    }

    // VectorizedLookupSetup checks
    if !vsetup_descs.is_empty() {
        let num_descs = vsetup_descs.len();
        let vs_cached: Vec<usize> = vsetup_descs.iter().map(|d| d.0).collect();
        let vs_dep_start: Vec<usize> = vsetup_descs.iter().map(|d| d.1).collect();
        let vs_dep_count: Vec<usize> = vsetup_descs.iter().map(|d| d.2).collect();

        let num_deps = vsetup_deps.len();

        let mul_ap = MW::mul_assign(quote! { term }, quote! { alpha_power });
        let add_exp = MW::add_assign(quote! { expected }, quote! { term });
        let mul_alpha = MW::mul_assign(quote! { alpha_power }, quote! { lookup_alpha });

        checks.extend(quote! {
            {
                const VS_DESCS: [(usize, usize, usize); #num_descs] = [
                    #( (#vs_cached, #vs_dep_start, #vs_dep_count), )*
                ];
                const VS_DEPS: [usize; #num_deps] = [
                    #( #vsetup_deps, )*
                ];
                let mut _vs = 0;
                while _vs < #num_descs {
                    let (cached_idx, dep_start, dep_count) = VS_DESCS[_vs];
                    let mut expected: #quartic_struct = #quartic_zero;
                    let mut alpha_power: #quartic_struct = #quartic_one;
                    let mut _d = 0;
                    while _d < dep_count {
                        let dep_idx = VS_DEPS[dep_start + _d];
                        let mut term = *state.prev_claims.get_unchecked(dep_idx);
                        #mul_ap;
                        #add_exp;
                        #mul_alpha;
                        _d += 1;
                    }
                    let cached = *state.prev_claims.get_unchecked(cached_idx);
                    if expected != cached {
                        return Err(GKRVerificationError::CacheRelationFailed { layer: #layer_idx });
                    }
                    _vs += 1;
                }
            }
        });
    }

    checks
}

#[allow(clippy::needless_range_loop)]
pub fn generate_gkr_inlined<MW: MersenneWrapper, F: PrimeField, E: FieldExtension<F> + Field, T>(
    compiled_circuit: &GKRCircuitArtifact<F>,
    proof: &GKRProof<F, E, T>,
    final_trace_size_log_2: usize,
    whir_schedule: &WhirSchedule,
) -> GKRGeneratedFiles
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

    let standard_sorted_addrs: Vec<Vec<GKRAddress>> = compiled_circuit
        .layers
        .iter()
        .map(collect_sorted_unique_addrs)
        .collect();

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
                for a in &standard_sorted_addrs[layer_idx + 1] {
                    addrs.insert(*a);
                }
                let extras = collect_extra_addrs_from_cached_relations(
                    &compiled_circuit.layers[layer_idx + 1],
                    &standard_sorted_addrs[layer_idx + 1],
                );
                for a in &extras {
                    addrs.insert(*a);
                }
            } else if !dim_reducing_sorted_addrs.is_empty() {
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

    let output_groups: Vec<GKROutputGroupInfo> = compiled_circuit
        .global_output_map
        .iter()
        .map(|(ot, addrs)| GKROutputGroupInfo {
            output_type: *ot,
            num_addresses: addrs.len(),
        })
        .collect();

    let max_sumcheck_rounds = proof
        .sumcheck_intermediate_values
        .values()
        .map(|v| v.sumcheck_num_rounds)
        .max()
        .unwrap_or(0);

    let max_unique_addrs_standard = standard_sorted_addrs
        .iter()
        .map(|a| a.len())
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

    let total_output_polys: usize = compiled_circuit
        .global_output_map
        .values()
        .map(|addrs| addrs.len())
        .sum();
    let max_addrs = max_unique_addrs_standard.max(total_output_polys);

    let max_pow = compiled_circuit
        .layers
        .iter()
        .map(compute_max_pow)
        .max()
        .unwrap_or(0)
        + 1;

    let max_evals = total_output_polys * (1usize << final_trace_size_log_2);

    let degree = E::DEGREE;
    let digest_words = prover::transcript::blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;
    // Largest draw is all_challenges: (final_trace_size_log_2 + 1) extension elements.
    let draw_buf_capacity = ((final_trace_size_log_2 + 1) * degree).next_multiple_of(digest_words);
    let block_words = prover::transcript::blake2s_u32::BLAKE2S_BLOCK_SIZE_U32_WORDS;
    let dim_reducing_words_per_addr = 4 * degree;
    let standard_words_per_addr = 2 * degree;
    let max_data_words = (max_addrs * dim_reducing_words_per_addr)
        .max(max_addrs * standard_words_per_addr)
        .max(max_evals * degree);
    let total = digest_words + max_data_words;
    let eval_buf_size = total.div_ceil(block_words) * block_words;

    let commit_buf_total = digest_words + 4 * degree;
    let commit_buf_size = commit_buf_total.div_ceil(block_words) * block_words;

    let evals_commit_total = digest_words + max_evals * degree;
    let evals_commit_buf_size = evals_commit_total.div_ceil(block_words) * block_words;

    let num_teardown_sets = compiled_circuit.memory_layout.teardown_sets.len();
    let num_linearization_challenges = proof
        .external_challenges
        .permutation_argument_linearization_challenges
        .len();

    // trace_len_log2 is needed early for address_high_bits_shift computation.
    let trace_len_log2 = proof
        .sumcheck_intermediate_values
        .get(&0)
        .expect("proof must have sumcheck values for layer 0")
        .sumcheck_num_rounds;

    // For circuits with teardown sets, this encodes the set index in the high
    // bits of the address. Must match prover's high_bits_offset_for_inits_and_teardowns.
    let address_high_bits_shift_val: u32 = if num_teardown_sets > 0 {
        const WORD_BITS: u32 = 2;
        (trace_len_log2 as u32) + WORD_BITS - 16
    } else {
        0
    };

    let initial_transcript_num_u32_words = {
        let mut tmp = Vec::<u32>::new();
        tmp.extend(core::iter::repeat(0u32).take(num_teardown_sets));
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

    let mut layer_functions = TokenStream::new();

    // Emit shared eval helper functions (used by table-driven gate evaluation)
    layer_functions.extend(standard_layer::generate_eval_helpers::<MW, F>());

    for layer_idx in 0..num_standard_layers {
        layer_functions.extend(standard_layer::generate_layer_compute_claim::<MW>(
            &compiled_circuit.layers[layer_idx],
            layer_idx,
            get_output_sorted_addrs(layer_idx),
        ));
        layer_functions.extend(
            standard_layer::generate_layer_final_step_accumulator::<MW, F>(
                &compiled_circuit.layers[layer_idx],
                layer_idx,
                &standard_sorted_addrs[layer_idx],
            ),
        );
    }

    // Generate shared dim-reducing functions ONCE (not per layer).
    if num_standard_layers <= initial_layer_for_sumcheck {
        layer_functions
            .extend(dim_reducing_layer::generate_dim_reducing_compute_claim::<MW>(&output_groups));
        layer_functions.extend(
            dim_reducing_layer::generate_dim_reducing_final_step_accumulator::<MW>(&output_groups),
        );
    }

    // Generate per-layer const index arrays for dim-reducing layers.
    let mut dim_reduce_index_arrays = TokenStream::new();
    for (dim_idx, layer_idx) in (num_standard_layers..=initial_layer_for_sumcheck).enumerate() {
        let iteration_order_addrs = build_dim_reducing_addrs(layer_idx);
        let sorted = &dim_reducing_sorted_addrs[dim_idx];
        let input_sorted_indices: Vec<usize> = iteration_order_addrs
            .iter()
            .map(|addr| addr_to_idx(addr, sorted))
            .collect();
        let num_indices = input_sorted_indices.len();
        let array_name = quote::format_ident!("DIM_REDUCE_INDICES_{}", layer_idx);
        dim_reduce_index_arrays.extend(quote! {
            const #array_name: [usize; #num_indices] = [#( #input_sorted_indices ),*];
        });
    }

    let mut static_data = TokenStream::new();

    if !standard_sorted_addrs.is_empty() {
        let sorted = &standard_sorted_addrs[0];
        let mut addrs_stream = TokenStream::new();
        addrs_stream.append_separated(sorted.iter().map(transform_gkr_address), quote! {,});
        static_data.extend(quote! {
            pub const LAYER_0_SORTED_ADDRS: &[GKRAddress] = &[#addrs_stream];
        });
    }

    // additional_base_layer_openings was removed in the no-caches refactor.
    let base_layer_additional_openings: Vec<TokenStream> = vec![];
    let mut base_openings_stream = TokenStream::new();
    base_openings_stream.append_separated(base_layer_additional_openings.iter(), quote! {,});

    let field_struct = MW::field_struct();
    let quartic_struct = MW::quartic_struct();
    let quartic_one = MW::quartic_one();

    let mut main_body = TokenStream::new();

    main_body.extend(quote! {
        let mut transcript_buf = LazyVec::<u32, GKR_TRANSCRIPT_U32>::new();
        {
            let mut i = 0;
            while i < GKR_TRANSCRIPT_U32 {
                transcript_buf.push(I::read_word());
                i += 1;
            }
        }

        // Extract oracle caps, reordering from transcript layout [setup, memory, witness]
        // to oracle list order [memory, witness, setup].
        let oracle_caps: [u32; TOTAL_CAP_WORDS] = {
            let mut caps = [0u32; TOTAL_CAP_WORDS];
            let src = transcript_buf.as_slice();
            let base = CAPS_OFFSET_IN_TRANSCRIPT;
            let mut dst = 0;
            let mut i = 0;
            while i < NUM_ORACLES {
                let words = ORACLE_CAP_WORDS[i];
                let src_offset = ORACLE_CAP_TRANSCRIPT_OFFSETS[i];
                let mut j = 0;
                while j < words {
                    caps[dst + j] = src[base + src_offset + j];
                    j += 1;
                }
                dst += words;
                i += 1;
            }
            caps
        };

        let mut ts = TranscriptState::new(
            Blake2sTranscript::commit_initial(transcript_buf.as_slice())
        );

        let mut init_challenges = LazyVec::<#quartic_struct, 3>::new();
        unsafe { init_challenges.set_len(3); }
        draw_field_els_into::<DRAW_BUF_CAPACITY>(&mut ts, init_challenges.as_mut_slice());
        let lookup_alpha = *init_challenges.get(0);
        let lookup_additive_challenge = *init_challenges.get(1);
        let constraints_batch_challenge = *init_challenges.get(2);

        // Extract external memory argument challenges from transcript buffer.
        // Layout: [teardown_top_bits | linearization_challenges | additive_part | caps...]
        let (linearization_challenges, permutation_argument_additive_part) = {
            let ext_start = #num_teardown_sets;
            let num_lin = #num_linearization_challenges;
            let mut lin = LazyVec::<#quartic_struct, #num_linearization_challenges>::new();
            let mut i = 0;
            while i < num_lin {
                let base = ext_start + i * EXT_DEGREE;
                let mut arr = LazyVec::<#field_struct, EXT_DEGREE>::new();
                let mut k = 0;
                while k < EXT_DEGREE {
                    arr.push(#field_struct::from_raw_repr_with_reduction(
                        *transcript_buf.get(base + k),
                    ));
                    k += 1;
                }
                lin.push(unsafe {
                    core::mem::transmute::<[#field_struct; EXT_DEGREE], #quartic_struct>(arr.into_array())
                });
                i += 1;
            }
            let add_base = ext_start + num_lin * EXT_DEGREE;
            let mut add_arr = LazyVec::<#field_struct, EXT_DEGREE>::new();
            let mut k = 0;
            while k < EXT_DEGREE {
                add_arr.push(#field_struct::from_raw_repr_with_reduction(
                    *transcript_buf.get(add_base + k),
                ));
                k += 1;
            }
            let additive = unsafe {
                core::mem::transmute::<[#field_struct; EXT_DEGREE], #quartic_struct>(add_arr.into_array())
            };
            (unsafe { lin.into_array() }, additive)
        };
        let address_high_bits_shift: u32 = #address_high_bits_shift_val;
    });

    let total_output_polys: usize = output_groups.iter().map(|g| g.num_addresses).sum();
    let evals_per_poly = 1usize << final_trace_size_log_2;
    let total_evals_needed = total_output_polys * evals_per_poly;
    let num_challenges = final_trace_size_log_2 + 1;
    let evaluation_point_len = final_trace_size_log_2;

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
        let mut evals_commit_buf = CommitBuf::<GKR_EVALS_COMMIT_BUF>::new();
        let evals_data_words = #total_evals_needed * EXT_DEGREE;
        {
            let mut i = 0;
            while i < evals_data_words {
                evals_commit_buf.data_write(i, read_reduced_field_el::<I>());
                i += 1;
            }
        }
        ts.commit(&mut evals_commit_buf, evals_data_words);
        let evals_slice: &[#quartic_struct] = unsafe { evals_commit_buf.data_as(#total_evals_needed) };

        let mut all_challenges = LazyVec::<#quartic_struct, { GKR_ROUNDS + 1 }>::new();
        unsafe { all_challenges.set_len(#num_challenges); }
        draw_field_els_into::<DRAW_BUF_CAPACITY>(
            &mut ts, all_challenges.as_mut_slice());
        let batching_challenge = *all_challenges.get(#num_challenges - 1);

        let mut eq_buf = LazyVec::<#quartic_struct, #evals_per_poly>::new();
        let eq_challenges: &[#quartic_struct; #evaluation_point_len] =
            all_challenges.as_slice()[..#evaluation_point_len].try_into().unwrap_unchecked();
        make_eq_poly(eq_challenges, &mut eq_buf);

        let mut prev_claims: LazyVec<#quartic_struct, GKR_ADDRS> = LazyVec::new();
        #claim_accum_body

        let prev_point = {
            let mut lv = LazyVec::<#quartic_struct, GKR_ROUNDS>::new();
            for i in 0..#evaluation_point_len {
                lv.push(*all_challenges.get(i));
            }
            // Remaining slots are written by subsequent layers before being read.
            unsafe { lv.set_len(GKR_ROUNDS); }
            unsafe { lv.into_array() }
        };

        let mut state = LayerState {
            prev_point,
            prev_point_len: #evaluation_point_len,
            prev_claims,
            batching_challenge,
        };

        let mut eval_buf = CommitBuf::<GKR_EVAL_BUF>::new();

        #dim_reduce_index_arrays
    });

    for config_idx in (num_standard_layers..=initial_layer_for_sumcheck).rev() {
        let proof_values = proof
            .sumcheck_intermediate_values
            .get(&config_idx)
            .expect("missing sumcheck values");
        let num_sumcheck_rounds = proof_values.sumcheck_num_rounds;
        let dim_idx = config_idx - num_standard_layers;
        let num_input_addrs = dim_reducing_sorted_addrs[dim_idx].len();
        let indices_name = quote::format_ident!("DIM_REDUCE_INDICES_{}", config_idx);
        let num_regular_rounds = num_sumcheck_rounds - 1;

        main_body.extend(quote! {
            {
                let initial_claim = dim_reducing_compute_claim(&state.prev_claims, state.batching_challenge);
                let (final_claim, final_eq_prefactor) =
                    verify_sumcheck_rounds::<I, #num_regular_rounds, GKR_COMMIT_BUF>(
                        &mut ts, initial_claim, &mut state.prev_point, #config_idx)?;
                let mut fc_len = #num_regular_rounds;
                let data_words = #num_input_addrs * 4 * <#quartic_struct as FieldExtension<#field_struct>>::DEGREE;
                {
                    let mut i = 0;
                    while i < data_words {
                        eval_buf.data_write(i, I::read_word());
                        i += 1;
                    }
                }
                {
                    let evals: &[[#quartic_struct; 4]] = eval_buf.data_as(#num_input_addrs);
                    let f = dim_reducing_final_step_accumulator(evals, state.batching_challenge, &#indices_name);
                    verify_final_step_check(f,
                        *state.prev_point.get_unchecked(state.prev_point_len - 1),
                        final_eq_prefactor, final_claim, #config_idx)?;
                }
                ts.commit(&mut eval_buf, data_words);
                let mut draw_buf = LazyVec::<#quartic_struct, 3>::new();
                unsafe { draw_buf.set_len(3); }
                draw_field_els_into::<DRAW_BUF_CAPACITY>(&mut ts, draw_buf.as_mut_slice());
                let r_before_last = *draw_buf.get(0);
                let r_last = *draw_buf.get(1);
                let next_batching = *draw_buf.get(2);
                *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
                fc_len += 1;
                *state.prev_point.get_unchecked_mut(fc_len) = r_last;
                fc_len += 1;
                const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
                const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
                let mut eq4 = LazyVec::<#quartic_struct, DIM_REDUCING_EQ_SIZE>::new();
                make_eq_poly(&[r_before_last, r_last], &mut eq4);
                let evals: &[[#quartic_struct; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(#num_input_addrs);
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

        // Compute merged target_addrs (regular + extra, sorted) for cache relation checks.
        let regular_set: std::collections::BTreeSet<GKRAddress> =
            standard_sorted_addrs[config_idx].iter().copied().collect();
        let target_addrs: Vec<GKRAddress> = {
            let mut addrs = regular_set.clone();
            for a in &extra_addrs {
                addrs.insert(*a);
            }
            addrs.into_iter().collect()
        };

        let fold_and_extras_code = if num_extra > 0 {
            let sub = MW::sub_assign(quote! { diff }, quote! { f0 });
            let mul_r = MW::mul_assign(quote! { diff }, quote! { last_r });
            let add_f0 = MW::add_assign(quote! { diff }, quote! { f0 });

            // Build a const array of extra positions: (merged_idx, extra_idx)
            let mut extra_positions: Vec<(usize, usize)> = Vec::new();
            let mut extra_idx = 0usize;
            for (merged_idx, addr) in target_addrs.iter().enumerate() {
                if !regular_set.contains(addr) {
                    extra_positions.push((merged_idx, extra_idx));
                    extra_idx += 1;
                }
            }
            let num_merged = target_addrs.len();
            let num_extra_pos = extra_positions.len();
            let ep_merged: Vec<usize> = extra_positions.iter().map(|p| p.0).collect();
            let ep_extra: Vec<usize> = extra_positions.iter().map(|p| p.1).collect();

            let extra_data_words = num_extra * E::DEGREE;
            let extra_commit_total = digest_words + extra_data_words;
            let extra_commit_buf_size = extra_commit_total.div_ceil(block_words) * block_words;
            quote! {
                const EXTRA_COMMIT_BUF: usize = #extra_commit_buf_size;
                let mut extra_buf = CommitBuf::<EXTRA_COMMIT_BUF>::new();
                let extra_data_words = #num_extra * EXT_DEGREE;
                {
                    let mut i = 0;
                    while i < extra_data_words {
                        extra_buf.data_write(i, read_reduced_field_el::<I>());
                        i += 1;
                    }
                }
                let mut extra_evals = LazyVec::<#quartic_struct, #num_extra>::new();
                {
                    let slice: &[#quartic_struct] = unsafe { extra_buf.data_as(#num_extra) };
                    for el in slice {
                        extra_evals.push(*el);
                    }
                }
                ts.commit(&mut extra_buf, extra_data_words);
                let final_step_evals: &[[#quartic_struct; 2]] = unsafe { eval_buf.data_as(#num_dedup_addrs) };
                state.prev_claims.clear();
                {
                    const EXTRA_POS: [(usize, usize); #num_extra_pos] = [
                        #( (#ep_merged, #ep_extra), )*
                    ];
                    let mut regular_idx: usize = 0;
                    let mut ep_idx: usize = 0;
                    let mut merged_idx: usize = 0;
                    while merged_idx < #num_merged {
                        if ep_idx < #num_extra_pos && EXTRA_POS[ep_idx].0 == merged_idx {
                            state.prev_claims.push(*extra_evals.get(EXTRA_POS[ep_idx].1));
                            ep_idx += 1;
                        } else {
                            let ev = final_step_evals.get_unchecked(regular_idx);
                            let f0 = ev[0];
                            let mut diff = ev[1];
                            #sub; #mul_r; #add_f0;
                            state.prev_claims.push(diff);
                            regular_idx += 1;
                        }
                        merged_idx += 1;
                    }
                }
            }
        } else {
            quote! {
                fold_standard_claims::<#num_dedup_addrs, GKR_ADDRS, GKR_EVAL_BUF>(
                    &eval_buf, last_r, &mut state.prev_claims);
            }
        };

        let cache_check_code = generate_cache_relation_checks::<MW, F>(
            &compiled_circuit.layers[config_idx],
            &target_addrs,
            config_idx,
        );

        main_body.extend(quote! {
            {
                let initial_claim = #compute_claim_fn(&state.prev_claims, state.batching_challenge);
                let (final_claim, final_eq_prefactor) =
                    verify_sumcheck_rounds::<I, #num_regular_rounds, GKR_COMMIT_BUF>(
                        &mut ts, initial_claim, &mut state.prev_point, #config_idx)?;
                let mut fc_len = #num_regular_rounds;
                let data_words = #num_dedup_addrs * 2 * <#quartic_struct as FieldExtension<#field_struct>>::DEGREE;
                {
                    let mut i = 0;
                    while i < data_words {
                        eval_buf.data_write(i, I::read_word());
                        i += 1;
                    }
                }
                {
                    let evals: &[[#quartic_struct; 2]] = eval_buf.data_as(#num_dedup_addrs);
                    let f = #final_step_fn(evals, state.batching_challenge,
                        lookup_additive_challenge, lookup_alpha, &challenge_powers,
                        &linearization_challenges, permutation_argument_additive_part,
                        address_high_bits_shift);
                    verify_final_step_check(f,
                        *state.prev_point.get_unchecked(state.prev_point_len - 1),
                        final_eq_prefactor, final_claim, #config_idx)?;
                }
                ts.commit(&mut eval_buf, data_words);
                let mut draw_buf = LazyVec::<#quartic_struct, 2>::new();
                unsafe { draw_buf.set_len(2); }
                draw_field_els_into::<DRAW_BUF_CAPACITY>(&mut ts, draw_buf.as_mut_slice());
                let last_r = *draw_buf.get(0);
                let next_batching = *draw_buf.get(1);
                *state.prev_point.get_unchecked_mut(fc_len) = last_r;
                fc_len += 1;
                #fold_and_extras_code
                #cache_check_code
                state.batching_challenge = next_batching;
                state.prev_point_len = fc_len;
            }
        });
    }

    main_body.extend(quote! {
        // Draw WHIR batching challenge BEFORE reading the grand product.
        // The prover draws this from the post-sumcheck seed, without committing
        // the grand product first (grand product is computed later).
        let mut draw_buf = LazyVec::<#quartic_struct, 1>::new();
        unsafe { draw_buf.set_len(1); }
        draw_field_els_into::<DRAW_BUF_CAPACITY>(&mut ts, draw_buf.as_mut_slice());
        let whir_batching_challenge = *draw_buf.get(0);

        let grand_product_accumulator: #quartic_struct = read_field_el::<I>();
        Ok(GKRVerifierOutput {
            base_layer_claims: state.prev_claims,
            base_layer_addrs: LAYER_0_SORTED_ADDRS,
            evaluation_point: state.prev_point,
            evaluation_point_len: state.prev_point_len,
            grand_product_accumulator,
            additional_base_layer_openings: BASE_LAYER_ADDITIONAL_OPENINGS,
            whir_batching_challenge,
            whir_transcript_seed: ts.seed,
            oracle_caps,
        })
    });

    let field_use_stmts = MW::field_use_statements();

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

    // Build uniform oracle list from proof: [memory, witness, setup]
    // This order matches the prover's batching (gamma power assignment).
    let oracle_commitments = [
        &proof.whir_proof.memory_commitment,
        &proof.whir_proof.witness_commitment,
        &proof.whir_proof.setup_commitment,
    ];

    let base_lde_factor_log2 = whir_base_lde_factor.trailing_zeros() as usize;
    let initial_fold_steps = whir_fold_steps[0];

    let oracles: Vec<OracleInfo> = oracle_commitments
        .iter()
        .map(|c| {
            let num_columns = c.num_columns;
            let cap_size = c.commitment.cap.cap.len();
            let depth = if cap_size == 0 {
                0
            } else {
                let cap_size_log2 = cap_size.trailing_zeros() as usize;
                trace_len_log2 + base_lde_factor_log2 - initial_fold_steps - cap_size_log2
            };
            OracleInfo {
                num_columns,
                cap_size,
                depth,
            }
        })
        .collect();

    let total_oracle_cols: usize = oracles.iter().map(|o| o.num_columns).sum();
    let digest_words = 8usize; // BLAKE2S_DIGEST_SIZE_U32_WORDS — TODO: use named constant
    let oracle_cap_words: Vec<usize> = oracles.iter().map(|o| o.cap_size * digest_words).collect();
    let total_cap_words: usize = oracle_cap_words.iter().sum();
    let whir_cap_words = whir_cap_size * digest_words;

    let caps_offset_in_transcript = initial_transcript_num_u32_words - total_cap_words;

    // Transcript cap layout is [setup, memory, witness] (prover order).
    // Oracle list order is [memory, witness, setup].
    // Compute per-oracle byte offsets into the transcript cap region.
    let setup_cap_words = proof.whir_proof.setup_commitment.commitment.cap.cap.len() * digest_words;
    let mem_cap_words_val = proof.whir_proof.memory_commitment.commitment.cap.cap.len() * digest_words;
    let wit_cap_words_val = proof.whir_proof.witness_commitment.commitment.cap.cap.len() * digest_words;
    // Transcript layout: [setup | memory | witness] starting at caps_offset_in_transcript
    // Oracle list: [memory, witness, setup]
    let oracle_cap_transcript_offsets: Vec<usize> = vec![
        setup_cap_words,                           // memory starts after setup
        setup_cap_words + mem_cap_words_val,        // witness starts after setup + memory
        0,                                          // setup starts at 0
    ];

    let oracle_depths: Vec<usize> = oracles.iter().map(|o| o.depth).collect();
    let oracle_num_cols: Vec<usize> = oracles.iter().map(|o| o.num_columns).collect();
    let num_oracles = oracles.len();

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
        use ::verifier_common::cs::definitions::{GKRAddress, VirtualSetupPoly};
        pub const GKR_ROUNDS: usize = #max_sumcheck_rounds;
        pub const GKR_ADDRS: usize = #max_addrs;
        pub const GKR_EVALS: usize = #max_evals;
        pub const GKR_TRANSCRIPT_U32: usize = #initial_transcript_num_u32_words;
        pub const GKR_MAX_POW: usize = #max_pow;
        pub const GKR_EVAL_BUF: usize = #eval_buf_size;
        pub const GKR_COMMIT_BUF: usize = #commit_buf_size;
        pub const GKR_EVALS_COMMIT_BUF: usize = #evals_commit_buf_size;
        pub const DRAW_BUF_CAPACITY: usize = #draw_buf_capacity;
        #static_data
        pub const BASE_LAYER_ADDITIONAL_OPENINGS: &[GKRAddress] = &[#base_openings_stream];
        pub const WHIR_FOLD_STEPS: [usize; #whir_rounds] = [#(#whir_fold_steps),*];
        pub const WHIR_QUERIES: [usize; #whir_rounds] = [#(#whir_queries),*];
        pub const WHIR_POW_BITS: [u32; #whir_rounds] = [#(#whir_pow_bits),*];
        pub const FINAL_MONOMIALS_LEN: usize = #final_monomials_len;
        pub const NUM_ORACLES: usize = #num_oracles;
        pub const ORACLE_NUM_COLS: [usize; #num_oracles] = [#(#oracle_num_cols),*];
        pub const ORACLE_CAP_WORDS: [usize; #num_oracles] = [#(#oracle_cap_words),*];
        pub const ORACLE_DEPTHS: [usize; #num_oracles] = [#(#oracle_depths),*];
        pub const TOTAL_ORACLE_COLS: usize = #total_oracle_cols;
        pub const TOTAL_CAP_WORDS: usize = #total_cap_words;
        pub const ORACLE_CAP_TRANSCRIPT_OFFSETS: [usize; #num_oracles] = [#(#oracle_cap_transcript_offsets),*];
        pub const WHIR_ORACLE_DEPTHS: [usize; #num_intermediate_oracles] = [#(#whir_oracle_depths),*];
        pub const WHIR_CAP_WORDS: usize = #whir_cap_words;
        pub const CAPS_OFFSET_IN_TRANSCRIPT: usize = #caps_offset_in_transcript;
    };

    let gkr = quote! {
        #field_use_stmts
        use ::verifier_common::gkr::{
            GKRVerifierOutput, GKRVerificationError, LayerState, LazyVec,
        };
        use ::verifier_common::structs::{CommitBuf, TranscriptState};
        use super::common::{
            verify_sumcheck_rounds, verify_final_step_check, fold_standard_claims,
            make_eq_poly, dot_eq, draw_field_els_into,
            read_field_el, read_reduced_field_el,
            EXT_DEGREE,
        };
        use ::verifier_common::field_ops;
        use ::verifier_common::transcript::Blake2sTranscript;
        use ::verifier_common::blake2s_u32::DelegatedBlake2sState;
        use ::verifier_common::field::{Field, FieldExtension, PrimeField};
        use ::verifier_common::non_determinism_source::NonDeterminismSource;
        use super::constants::*;

        #layer_functions

        #[allow(unused_braces, unused_mut, unused_variables, unused_unsafe, clippy::needless_borrow, clippy::needless_range_loop, clippy::large_const_arrays)]
        pub fn verify_gkr<I: NonDeterminismSource,
        >() -> Result<GKRVerifierOutput<'static, #quartic_struct, GKR_ROUNDS, GKR_ADDRS, TOTAL_CAP_WORDS>, GKRVerificationError> {
            unsafe { #main_body }
        }
    };

    GKRGeneratedFiles {
        constants,
        gkr,
        oracles,
        trace_len_log2,
    }
}
