use proc_macro2::TokenStream;
use quote::quote;
use std::collections::BTreeMap;

use crate::field_wrapper::FieldWrapper;
pub use crate::utils::{
    addr_to_idx, collect_extra_addrs_from_cached_relations, collect_sorted_unique_addrs,
    BATCHING_CHALLENGE_EXTRA, DIM_REDUCE_EVAL_POINTS, STANDARD_EVAL_POINTS, SUMCHECK_POLY_COEFFS,
};
use prover::common_constants::TIMESTAMP_COLUMNS_NUM_BITS;
use prover::cs::definitions::{GKRAddress, VirtualSetupPoly};
use prover::cs::gkr_compiler::{
    GKRCircuitArtifact, GKRLayerDescription, NoFieldGKRCacheRelation, OutputType,
};
use prover::gkr::prover::WhirSchedule;

pub mod dim_reducing_layer;
pub mod standard_layer;

// Ordering matches prover implementation
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum OracleType {
    Memory = 0,
    Witness,
    Setup,
}

// it matches names of the corresponding accessor functions in the
// initial transcript structure
impl quote::ToTokens for OracleType {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        use quote::quote;

        let quote = match self {
            Self::Memory => {
                quote! { memory_caps_slice }
            }
            Self::Witness => {
                quote! { witness_caps_slice }
            }
            Self::Setup => {
                quote! { setup_caps_slice }
            }
        };

        tokens.extend(quote);
    }
}

#[derive(Clone, Debug)]
pub struct OracleInfo {
    pub num_columns: usize,
    pub cap_size: usize,
    pub depth: usize,
}

pub struct GKRGeneratedFiles {
    pub constants: TokenStream,
    pub gkr: TokenStream,
    pub oracles: BTreeMap<OracleType, OracleInfo>,
    pub trace_len_log2: usize,
}

#[derive(Clone, Debug)]
pub struct GKROutputGroupInfo {
    pub output_type: OutputType,
    pub num_addresses: usize,
}

pub fn generate_gkr_common<MW: FieldWrapper>() -> TokenStream {
    let field_struct = MW::field_struct();
    let quartic_struct = MW::quartic_struct();
    let quartic_one = MW::quartic_one();

    // sumcheck round operations
    let add_p1_c1 = MW::add_assign(quote! { p1 }, quote! { coeffs[1] });
    let add_p1_c2 = MW::add_assign(quote! { p1 }, quote! { coeffs[2] });
    let add_p1_c3 = MW::add_assign(quote! { p1 }, quote! { coeffs[3] });
    let add_sum_p1 = MW::add_assign(quote! { sum }, quote! { p1 });
    let mul_sum_eq = MW::mul_assign(quote! { sum }, quote! { eq_prefactor });
    let mul_res_rk = MW::mul_assign(quote! { result }, quote! { r_k });
    let add_res_c2 = MW::add_assign(quote! { result }, quote! { coeffs[2] });
    let add_res_c1 = MW::add_assign(quote! { result }, quote! { coeffs[1] });
    let add_res_c0 = MW::add_assign(quote! { result }, quote! { coeffs[0] });
    let sub_omr_rk = MW::sub_assign(quote! { one_minus_r }, quote! { r_k });
    let sub_omp_p = MW::sub_assign(quote! { one_minus_p }, quote! { p });
    let mul_t_omp = MW::mul_assign(quote! { t }, quote! { one_minus_p });
    let mul_rp_p = MW::mul_assign(quote! { rp }, quote! { p });
    let add_t_rp = MW::add_assign(quote! { t }, quote! { rp });

    // final step check operations
    let mul_rhs_eq = MW::mul_assign(quote! { rhs }, quote! { final_eq_prefactor });

    let common_fns = quote! {
        #[inline(always)]
        pub fn verify_sumcheck_rounds<
            I: NonDeterminismSource,
            E: ErrorCreator,
            const NUM_ROUNDS: usize,
            const COMMIT_BUF: usize,
        >(
            ts: &mut TranscriptState,
            initial_claim: #quartic_struct,
            challenges: &mut [#quartic_struct],
            layer_idx: usize,
            nd_source: &mut I,
        ) -> Result<(#quartic_struct, #quartic_struct), E::Error> {
            let mut claim = initial_claim;
            let mut eq_prefactor = #quartic_one;

            let coeff_data_words = SUMCHECK_POLY_COEFFS * EXT_DEGREE;

            let mut commit_buf = CommitBuf::<COMMIT_BUF>::new();
            let mut draw_buf = LazyVec::<u32, BLAKE2S_DIGEST_SIZE_U32_WORDS>::new();
            unsafe { draw_buf.set_len(BLAKE2S_DIGEST_SIZE_U32_WORDS); }

            for round in 0..NUM_ROUNDS {
                {
                    let mut i = 0;
                    while i < coeff_data_words {
                        commit_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                        i += 1;
                    }
                }

                // Copy coefficients out before committing (commit borrows &mut self).
                let coeffs: [#quartic_struct; 4] = unsafe {
                    *commit_buf.data_as::<[#quartic_struct; 4]>(1).as_ptr()
                };

                let p0 = coeffs[0];
                let mut p1 = coeffs[0];
                #add_p1_c1;
                #add_p1_c2;
                #add_p1_c3;

                let mut sum = p0;
                #add_sum_p1;
                #mul_sum_eq;

                if sum != claim {
                    return Err(E::gkr_sumcheck_round_failed(layer_idx, round));
                }

                ts.commit(&mut commit_buf, coeff_data_words);

                ts.draw_raw(draw_buf.as_mut_slice());
                let r_k = {
                    let raw = unsafe { (draw_buf.as_slice().as_ptr() as *const [u32; EXT_DEGREE]).as_ref_unchecked() };
                    ext_from_raw_words::<#field_struct, #quartic_struct, EXT_DEGREE>(raw)
                };

                {
                    let mut result = coeffs[3];
                    #mul_res_rk;
                    #add_res_c2;
                    #mul_res_rk;
                    #add_res_c1;
                    #mul_res_rk;
                    #add_res_c0;
                    claim = result;
                }
                {
                    let p = unsafe { *challenges.get_unchecked(round) };
                    let mut one_minus_r = #quartic_one;
                    #sub_omr_rk;
                    let mut one_minus_p = #quartic_one;
                    #sub_omp_p;
                    let mut t = one_minus_r;
                    #mul_t_omp;
                    let mut rp = r_k;
                    #mul_rp_p;
                    #add_t_rp;
                    eq_prefactor = t;
                }

                unsafe { *challenges.get_unchecked_mut(round) = r_k };
            }

            Ok((claim, eq_prefactor))
        }

        // New last-round form: the last sumcheck round is now a regular univariate verified
        // inside `verify_sumcheck_rounds`, so `final_claim` already equals `s_last(r_last)` and
        // `final_eq_prefactor == eq(r_last, last_output_coord)`. The prover sends a single
        // at-point evaluation per input poly, from which the verifier evaluates the GKR kernels
        // ONCE to obtain `g = G(point)`. Consistency is then just `final_claim == g * eq`.
        #[inline(always)]
        pub fn verify_final_step_check<E: ErrorCreator>(
            g: #quartic_struct,
            final_eq_prefactor: #quartic_struct,
            final_claim: #quartic_struct,
            layer_idx: usize,
        ) -> Result<(), E::Error> {
            let mut rhs = g;
            #mul_rhs_eq;
            if rhs != final_claim {
                return Err(E::gkr_final_step_check_failed(layer_idx));
            }
            Ok(())
        }

        // The prover now sends the at-point evaluations directly (the polys already folded at
        // the last challenge), so the next-layer claims are exactly those values - no linear
        // interpolation needed.
        #[inline(always)]
        pub fn fold_standard_claims<
            const NUM_ADDRS: usize,
            const ADDRS: usize,
            const BUF: usize,
        >(
            eval_buf: &CommitBuf<BUF>,
            claims: &mut LazyVec<#quartic_struct, ADDRS>,
        ) {
            let final_step_evals: &[[#quartic_struct; 1]] =
                unsafe { eval_buf.data_as(NUM_ADDRS) };
            claims.clear();
            for i in 0..NUM_ADDRS {
                let evals = unsafe { final_step_evals.get_unchecked(i) };
                claims.push(evals[0]);
            }
        }
    };

    let eval_helpers = standard_layer::generate_eval_helpers::<MW>();

    let quartic_zero = MW::quartic_zero();
    let cc_mul_batch = MW::mul_assign(quote! { current_batch }, quote! { batch_base });
    let cc_mul_t = MW::mul_assign(quote! { t }, quote! { claim });
    let cc_add_combined = MW::add_assign(quote! { combined }, quote! { t });
    let cc_mul_t0 = MW::mul_assign(quote! { t0 }, quote! { c0 });
    let cc_mul_t1 = MW::mul_assign(quote! { t1 }, quote! { c1 });
    let cc_add_t0 = MW::add_assign(quote! { combined }, quote! { t0 });
    let cc_add_t1 = MW::add_assign(quote! { combined }, quote! { t1 });

    let compute_claim = quote! {
        #[inline(always)]
        #[allow(unused_variables)]
        pub unsafe fn compute_claim<const N: usize>(
            output_claims: &[#quartic_struct],
            descs: &[(usize, usize, usize); N],
            batch_base: #quartic_struct,
        ) -> #quartic_struct {
            let mut combined = #quartic_zero;
            let mut current_batch = #quartic_one;
            let mut i = 0;
            while i < N {
                let (n, o0, o1) = unsafe { *descs.get_unchecked(i) };
                if n == 0 {
                    #cc_mul_batch;
                } else if n == 1 {
                    let claim = *output_claims.get_unchecked(o0);
                    let mut t = current_batch;
                    #cc_mul_t;
                    #cc_add_combined;
                    #cc_mul_batch;
                } else {
                    let c0 = *output_claims.get_unchecked(o0);
                    let mut t0 = current_batch;
                    #cc_mul_t0;
                    #cc_add_t0;
                    #cc_mul_batch;
                    let c1 = *output_claims.get_unchecked(o1);
                    let mut t1 = current_batch;
                    #cc_mul_t1;
                    #cc_add_t1;
                    #cc_mul_batch;
                }
                i += 1;
            }
            combined
        }
    };

    quote! {
        #common_fns
        #eval_helpers
        #compute_claim
    }
}

fn build_virtual_setup_eval_checks<MW: FieldWrapper>(
    layer_0_layout: &[GKRAddress],
    trace_len_log_2: usize,
    inits_and_teardowns_word_bits: Option<u32>,
) -> (TokenStream, TokenStream) {
    let mut helpers = TokenStream::new();
    let mut calls = TokenStream::new();

    let mut its_low_idx: Option<usize> = None;
    let mut its_high_idx: Option<usize> = None;

    for (idx, addr) in layer_0_layout.iter().enumerate() {
        let GKRAddress::VirtualSetup(poly) = addr else {
            continue;
        };
        match poly {
            VirtualSetupPoly::RangeCheck16Bits => {
                let (helper, call) = emit_range_check_eval_check::<MW>(
                    "RangeCheck16Bits",
                    "range_check_16bits",
                    idx,
                    16,
                    trace_len_log_2,
                );
                helpers.extend(helper);
                calls.extend(call);
            }
            VirtualSetupPoly::RangeCheckTimestamp => {
                let (helper, call) = emit_range_check_eval_check::<MW>(
                    "RangeCheckTimestamp",
                    "range_check_timestamp",
                    idx,
                    TIMESTAMP_COLUMNS_NUM_BITS as usize,
                    trace_len_log_2,
                );
                helpers.extend(helper);
                calls.extend(call);
            }
            VirtualSetupPoly::InitsAndTeardownsLow => {
                its_low_idx = Some(idx);
            }
            VirtualSetupPoly::InitsAndTeardownsHigh => {
                its_high_idx = Some(idx);
            }
        }
    }

    if its_low_idx.is_some() || its_high_idx.is_some() {
        let lo = its_low_idx.expect("InitsAndTeardownsLow expected when High is present");
        let hi = its_high_idx.expect("InitsAndTeardownsHigh expected when Low is present");
        let word_bits = inits_and_teardowns_word_bits.expect(
            "compiled_circuit.memory_layout.inits_and_teardowns_word_bits must be Some \
             for circuits emitting InitsAndTeardowns VirtualSetup polys",
        ) as usize;
        let (helper, call) =
            emit_inits_and_teardowns_eval_check::<MW>(lo, hi, word_bits, trace_len_log_2);
        helpers.extend(helper);
        calls.extend(call);
    }

    (helpers, calls)
}

fn emit_range_check_eval_check<MW: FieldWrapper>(
    poly_name: &str,
    poly_snake: &str,
    idx: usize,
    bits: usize,
    n: usize,
) -> (TokenStream, TokenStream) {
    let field_struct = MW::field_struct();
    let quartic_struct = MW::quartic_struct();
    let field_one = MW::field_one();
    let quartic_zero = MW::quartic_zero();
    let quartic_one = MW::quartic_one();

    let mul_t_pre = MW::mul_assign_by_base(quote! { t }, quote! { prefactor });
    let add_res_t = MW::add_assign(quote! { result }, quote! { t });
    let dbl_pre = MW::double(quote! { prefactor });
    let sub_t_p = MW::sub_assign(quote! { t }, quote! { *p });
    let mul_res_t = MW::mul_assign(quote! { result }, quote! { t });

    let summary = format!(
        " Closed-form eval of VirtualSetup({}) at `state.prev_point` (lower {} bits free, top bits forced to zero).",
        poly_name, bits,
    );

    let fn_name = quote::format_ident!("check_virtual_setup_{}", poly_snake);

    let helper = quote! {
        #[doc = #summary]
        #[doc = " Source: prover/src/gkr/virtual_polys/range_check.rs."]
        #[doc = " The `prev_claims` index is the position assigned to this VirtualSetup poly by the"]
        #[doc = " canonical layer-0 layout (memory cols → witness cols → setup cols → virtual setups → others)."]
        #[inline(always)]
        fn #fn_name<E: ErrorCreator>(
            state: &LayerState<#quartic_struct, GKR_ROUNDS, GKR_ADDRS>,
        ) -> Result<(), E::Error> {
            unsafe {
                let pt = state.prev_point.get_unchecked(..#n);
                let mut result: #quartic_struct = #quartic_zero;
                let mut prefactor: #field_struct = #field_one;
                let mut k: usize = 0;
                while k < #bits {
                    let mut t = *pt.get_unchecked(#n - 1 - k);
                    #mul_t_pre;
                    #add_res_t;
                    #dbl_pre;
                    k += 1;
                }
                while k < #n {
                    let mut t: #quartic_struct = #quartic_one;
                    let p = pt.get_unchecked(#n - 1 - k);
                    #sub_t_p;
                    #mul_res_t;
                    k += 1;
                }
                if result != *state.prev_claims.get_unchecked(#idx) {
                    return Err(E::gkr_virtual_setup_eval_mismatch(#idx));
                }
            }
            Ok(())
        }
    };

    let call = quote! { #fn_name::<E>(&state)?; };

    (helper, call)
}

fn emit_inits_and_teardowns_eval_check<MW: FieldWrapper>(
    lo_idx: usize,
    hi_idx: usize,
    word_bits: usize,
    n: usize,
) -> (TokenStream, TokenStream) {
    let field_struct = MW::field_struct();
    let quartic_struct = MW::quartic_struct();
    let field_one = MW::field_one();
    let quartic_zero = MW::quartic_zero();

    let mul_t_pre = MW::mul_assign_by_base(quote! { t }, quote! { prefactor });
    let add_low_t = MW::add_assign(quote! { low_eval }, quote! { t });
    let add_high_t = MW::add_assign(quote! { high_eval }, quote! { t });
    let dbl_pre = MW::double(quote! { prefactor });

    let take_count = 16 - word_bits;

    let halves = format!(
        " Low half = bits [{}..16) of the address (top {} bits zeroed); high half = the high {} address bits.",
        word_bits, word_bits, n - take_count,
    );

    let helper = quote! {
        #[doc = " Closed-form eval of VirtualSetup(InitsAndTeardownsLow/High) at `state.prev_point`."]
        #[doc = #halves]
        #[doc = " Source: prover/src/gkr/virtual_polys/init_and_teardown_base.rs."]
        #[doc = " The `prev_claims` indices are positions assigned by the canonical layer-0 layout"]
        #[doc = " (memory cols → witness cols → setup cols → virtual setups → others)`."]
        #[inline(always)]
        fn check_virtual_setup_inits_and_teardowns<E: ErrorCreator>(
            state: &LayerState<#quartic_struct, GKR_ROUNDS, GKR_ADDRS>,
        ) -> Result<(), E::Error> {
            unsafe {
                let pt = state.prev_point.get_unchecked(..#n);

                let mut low_eval: #quartic_struct = #quartic_zero;
                {
                    let mut prefactor: #field_struct = #field_one;
                    let mut wb: usize = 0;
                    while wb < #word_bits {
                        #dbl_pre;
                        wb += 1;
                    }
                    let mut k: usize = 0;
                    while k < #take_count {
                        let mut t = *pt.get_unchecked(#n - 1 - k);
                        #mul_t_pre;
                        #add_low_t;
                        #dbl_pre;
                        k += 1;
                    }
                }

                let mut high_eval: #quartic_struct = #quartic_zero;
                {
                    let mut prefactor: #field_struct = #field_one;
                    let mut k: usize = 0;
                    while k < #n - #take_count {
                        let mut t = *pt.get_unchecked(#n - 1 - #take_count - k);
                        #mul_t_pre;
                        #add_high_t;
                        #dbl_pre;
                        k += 1;
                    }
                }

                if low_eval != *state.prev_claims.get_unchecked(#lo_idx) {
                    return Err(E::gkr_virtual_setup_eval_mismatch(#lo_idx));
                }
                if high_eval != *state.prev_claims.get_unchecked(#hi_idx) {
                    return Err(E::gkr_virtual_setup_eval_mismatch(#hi_idx));
                }
            }
            Ok(())
        }
    };

    let call = quote! { check_virtual_setup_inits_and_teardowns::<E>(&state)?; };

    (helper, call)
}

fn generate_cache_relation_checks<MW: FieldWrapper>(
    layer: &GKRLayerDescription,
    target_addrs: &[GKRAddress],
    layer_idx: usize,
) -> TokenStream {
    let quartic_struct = MW::quartic_struct();
    let field_struct = MW::field_struct();
    let quartic_zero = MW::quartic_zero();
    let quartic_one = MW::quartic_one();

    let mut single_descs: Vec<(usize, u32, usize, usize)> = Vec::new();
    let mut single_terms: Vec<(u32, usize)> = Vec::new();

    let mut vector_descs: Vec<(usize, usize, usize)> = Vec::new();
    let mut vector_cols: Vec<(u32, usize, usize)> = Vec::new();
    let mut vector_terms: Vec<(u32, usize)> = Vec::new();

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
                    single_terms.push((MW::coeff_to_internal_repr(coeff), find_idx(addr)));
                }
                single_descs.push((
                    cached_idx,
                    MW::coeff_to_internal_repr(rel.input.constant),
                    term_start,
                    rel.input.linear_terms.len(),
                ));
            }
            NoFieldGKRCacheRelation::VectorizedLookup(rel) => {
                let col_start = vector_cols.len();
                for column in rel.columns.iter() {
                    let t_start = vector_terms.len();
                    for &(coeff, ref addr) in column.linear_terms.iter() {
                        vector_terms.push((MW::coeff_to_internal_repr(coeff), find_idx(addr)));
                    }
                    vector_cols.push((
                        MW::coeff_to_internal_repr(column.constant),
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
        let from_base_const =
            MW::quartic_from_base(quote! { #field_struct::from_reduced_raw_repr(constant) });

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
                    let mut expected: #quartic_struct = #from_base_const;
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
                        return Err(E::gkr_single_lookup_cache_relation_failed(#layer_idx, _sc));
                    }
                    _sc += 1;
                }
            }
        });
    }

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
        let from_base_col_const =
            MW::quartic_from_base(quote! { #field_struct::from_reduced_raw_repr(col_constant) });

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
                        let mut col_val: #quartic_struct = #from_base_col_const;
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
                        return Err(E::gkr_vector_lookup_cache_relation_failed(#layer_idx, _vl));
                    }
                    _vl += 1;
                }
            }
        });
    }

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
                        return Err(E::gkr_permutation_cache_relation_failed(#layer_idx, _vs));
                    }
                    _vs += 1;
                }
            }
        });
    }

    checks
}

#[allow(clippy::needless_range_loop)]
pub fn generate_gkr_inlined<MW: FieldWrapper>(
    compiled_circuit: &GKRCircuitArtifact<MW::BaseField>,
    sumcheck_output_size_log_2: usize,
    whir_schedule: &WhirSchedule,
) -> GKRGeneratedFiles {
    let num_standard_layers = compiled_circuit.layers.len();
    let trace_len = compiled_circuit.trace_len;
    assert!(trace_len.is_power_of_two());
    let trace_len_log_2 = trace_len.trailing_zeros() as usize;
    let initial_layer_for_sumcheck =
        num_standard_layers + trace_len_log_2 - sumcheck_output_size_log_2;

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
                    OutputType::PermutationProduct | OutputType::InitsAndTeardownsProduct => {
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
        ..initial_layer_for_sumcheck)
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

    let max_sumcheck_rounds = trace_len_log_2;

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

    let max_evals = total_output_polys * (1usize << sumcheck_output_size_log_2);

    let num_memory_commits = (compiled_circuit.memory_layout.total_width > 0) as usize;
    let num_witness_commits = (compiled_circuit.witness_layout.total_width > 0) as usize;
    let num_setup_commits = (compiled_circuit.generic_lookup_tables_width > 0) as usize;

    let num_challenges = sumcheck_output_size_log_2 + BATCHING_CHALLENGE_EXTRA;
    let num_teardown_sets = compiled_circuit.memory_layout.teardown_sets.len();
    let num_linearization_challenges =
        ::cs::definitions::NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES;

    let trace_len_log2 = compiled_circuit.trace_len.trailing_zeros() as usize;

    let address_high_bits_shift_val: u32 = if num_teardown_sets > 0 {
        let word_bits = compiled_circuit
            .memory_layout
            .inits_and_teardowns_word_bits
            .expect(
                "compiled_circuit.memory_layout.inits_and_teardowns_word_bits must be Some \
                 when teardown_sets is non-empty",
            );
        (trace_len_log2 as u32) + word_bits - 16
    } else {
        0
    };

    let mut layer_functions = TokenStream::new();

    for layer_idx in 0..num_standard_layers {
        layer_functions.extend(standard_layer::generate_layer_compute_claim::<MW>(
            &compiled_circuit.layers[layer_idx],
            layer_idx,
            get_output_sorted_addrs(layer_idx),
        ));
        layer_functions.extend(standard_layer::generate_layer_final_step_accumulator::<MW>(
            &compiled_circuit.layers[layer_idx],
            layer_idx,
            &standard_sorted_addrs[layer_idx],
        ));
    }

    if num_standard_layers <= initial_layer_for_sumcheck {
        layer_functions
            .extend(dim_reducing_layer::generate_dim_reducing_compute_claim::<MW>(&output_groups));
        layer_functions.extend(
            dim_reducing_layer::generate_dim_reducing_final_step_accumulator::<MW>(&output_groups),
        );
    }

    let mut dim_reduce_index_arrays = TokenStream::new();
    for (dim_idx, layer_idx) in (num_standard_layers..initial_layer_for_sumcheck).enumerate() {
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

    let field_struct = MW::field_struct();
    let quartic_struct = MW::quartic_struct();
    let quartic_zero = MW::quartic_zero();
    let quartic_one = MW::quartic_one();

    let mut main_body = TokenStream::new();

    main_body.extend(quote! {
        let mut init_challenges = LazyVec::<#quartic_struct, 2>::new();
        unsafe { init_challenges.set_len(2); }
        draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, init_challenges.as_mut_slice());
        let lookup_alpha = *init_challenges.get(0);
        let lookup_additive_challenge = *init_challenges.get(1);
        let address_high_bits_shift: u32 = #address_high_bits_shift_val;
    });

    let total_output_polys: usize = output_groups.iter().map(|g| g.num_addresses).sum();
    let evals_per_poly = 1usize << sumcheck_output_size_log_2;
    let total_evals_needed = total_output_polys * evals_per_poly;
    let evaluation_point_len = sumcheck_output_size_log_2;

    let mut claim_accum_body = TokenStream::new();
    let mut eval_offset_val = 0usize;
    for group in &output_groups {
        let count = match group.output_type {
            OutputType::PermutationProduct => group.num_addresses,
            OutputType::InitsAndTeardownsProduct => group.num_addresses,
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
                evals_commit_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                i += 1;
            }
        }
        ts.commit(&mut evals_commit_buf, evals_data_words);
        let evals_slice: &[#quartic_struct] = unsafe { evals_commit_buf.data_as(#total_evals_needed) };

        let mut all_challenges = LazyVec::<#quartic_struct, { GKR_ROUNDS + 1 }>::new();
        unsafe { all_challenges.set_len(#num_challenges); }
        draw_field_els_into::<DRAW_BUF_CAPACITY>(
            ts, all_challenges.as_mut_slice());
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

        #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR COMPRESSION INIT");
    });

    for config_idx in (num_standard_layers..initial_layer_for_sumcheck).rev() {
        let num_sumcheck_rounds =
            sumcheck_output_size_log_2 + (initial_layer_for_sumcheck - 1 - config_idx);
        let dim_idx = config_idx - num_standard_layers;
        let num_input_addrs = dim_reducing_sorted_addrs[dim_idx].len();
        let indices_name = quote::format_ident!("DIM_REDUCE_INDICES_{}", config_idx);
        // New last-round form: the last *output* coordinate is folded by a univariate round
        // inside `verify_sumcheck_rounds` (drawing `r_before_last`). Only the pairwise/LSB
        // coordinate remains to be fixed in the open via `r_last`.
        let num_regular_rounds = num_sumcheck_rounds;

        let label = &format!("GKR COMPRESSION LAYER {config_idx}");
        main_body.extend(quote! {
            {
                let initial_claim = dim_reducing_compute_claim(state.prev_claims.as_array::<#total_output_polys>(), state.batching_challenge);
                let (final_claim, final_eq_prefactor) =
                    verify_sumcheck_rounds::<I, E, #num_regular_rounds, GKR_COMMIT_BUF>(
                        ts, initial_claim, &mut state.prev_point, #config_idx, nd_source)?;
                let mut fc_len = #num_regular_rounds;
                // Half the data: the [E;2] line in the remaining LSB coordinate (was [E;4]).
                let data_words = #num_input_addrs * 2 * EXT_DEGREE;
                {
                    let mut i = 0;
                    while i < data_words {
                        eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                        i += 1;
                    }
                }
                {
                    let evals: &[[#quartic_struct; 2]] = eval_buf.data_as(#num_input_addrs);
                    // Half the work: evaluate the dimension-reducing kernels over a single LSB pair.
                    let f = dim_reducing_final_step_accumulator(evals, state.batching_challenge, &#indices_name);
                    verify_final_step_check::<E>(f,
                        final_eq_prefactor, final_claim, #config_idx)?;
                }
                ts.commit(&mut eval_buf, data_words);
                let mut draw_buf = LazyVec::<#quartic_struct, 2>::new();
                unsafe { draw_buf.set_len(2); }
                draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
                let r_last = *draw_buf.get(0);
                let next_batching = *draw_buf.get(1);
                *state.prev_point.get_unchecked_mut(fc_len) = r_last;
                fc_len += 1;
                const DIM_REDUCING_EXTRA_CHALLENGES: usize = 1;
                const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
                let mut eq2 = LazyVec::<#quartic_struct, DIM_REDUCING_EQ_SIZE>::new();
                make_eq_poly(&[r_last], &mut eq2);
                let evals: &[[#quartic_struct; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(#num_input_addrs);
                let eq2_arr: &[#quartic_struct; DIM_REDUCING_EQ_SIZE] =
                    eq2.as_slice().try_into().unwrap_unchecked();
                state.prev_claims.clear();
                for i in 0..#num_input_addrs {
                    let e = evals.get_unchecked(i);
                    state.prev_claims.push(dot_eq(e, eq2_arr));
                }
                state.batching_challenge = next_batching;
                state.prev_point_len = fc_len;
                #[cfg(feature = "verifier_stats")]
                    verifier_common::stats::log(#label);
            }
        });
    }

    let num_memory_cols = compiled_circuit.memory_layout.total_width;
    let num_witness_cols = compiled_circuit.witness_layout.total_width;
    let num_setup_cols = compiled_circuit.generic_lookup_tables_width;

    let (
        virtual_setup_helpers,
        virtual_setup_calls,
        layer_0_layout,
        layer_0_src_kind,
        layer_0_src_pos,
    ) = if standard_sorted_addrs.is_empty() {
        for (_, group_addrs) in compiled_circuit.global_output_map.iter() {
            for addr in group_addrs {
                assert!(
                    !matches!(addr, GKRAddress::VirtualSetup(_)),
                    "circuit has zero standard GKR layers but VirtualSetup address {:?} \
                     appears in global_output_map; closed-form eval check cannot be generated",
                    addr
                );
            }
        }
        (
            TokenStream::new(),
            TokenStream::new(),
            Vec::<GKRAddress>::new(),
            Vec::<usize>::new(),
            Vec::<usize>::new(),
        )
    } else {
        use std::collections::BTreeSet;
        let regular_set: BTreeSet<GKRAddress> = standard_sorted_addrs[0].iter().copied().collect();
        let extra_addrs = collect_extra_addrs_from_cached_relations(
            &compiled_circuit.layers[0],
            &standard_sorted_addrs[0],
        );
        let mut merged: BTreeSet<GKRAddress> = regular_set;
        for a in &extra_addrs {
            merged.insert(*a);
        }

        let is_oracle_col = |addr: &GKRAddress| {
            matches!(
                addr,
                GKRAddress::BaseLayerMemory(_)
                    | GKRAddress::BaseLayerWitness(_)
                    | GKRAddress::Setup(_)
            )
        };
        let is_virtual = |addr: &GKRAddress| matches!(addr, GKRAddress::VirtualSetup(_));

        let mut layout: Vec<GKRAddress> = Vec::with_capacity(merged.len());
        for i in 0..num_memory_cols {
            layout.push(GKRAddress::BaseLayerMemory(i));
        }
        for i in 0..num_witness_cols {
            layout.push(GKRAddress::BaseLayerWitness(i));
        }
        for i in 0..num_setup_cols {
            layout.push(GKRAddress::Setup(i));
        }
        for addr in merged.iter() {
            if is_virtual(addr) {
                layout.push(*addr);
            }
        }
        for addr in merged.iter() {
            if !is_oracle_col(addr) && !is_virtual(addr) {
                layout.push(*addr);
            }
        }

        for i in 0..num_memory_cols {
            assert_eq!(layout[i], GKRAddress::BaseLayerMemory(i));
        }
        for j in 0..num_witness_cols {
            assert_eq!(layout[num_memory_cols + j], GKRAddress::BaseLayerWitness(j));
        }
        for k in 0..num_setup_cols {
            assert_eq!(
                layout[num_memory_cols + num_witness_cols + k],
                GKRAddress::Setup(k)
            );
        }
        let total_oracle_cols = num_memory_cols + num_witness_cols + num_setup_cols;
        assert!(
            layout.len() >= total_oracle_cols,
            "layer-0 layout has {} entries, less than TOTAL_ORACLE_COLS = {}",
            layout.len(),
            total_oracle_cols
        );
        for addr in standard_sorted_addrs[0].iter().chain(extra_addrs.iter()) {
            assert!(
                layout.iter().any(|a| a == addr),
                "layer-0 layout missing address {:?}",
                addr
            );
        }

        let (helpers, calls) = build_virtual_setup_eval_checks::<MW>(
            &layout,
            trace_len_log_2,
            compiled_circuit.memory_layout.inits_and_teardowns_word_bits,
        );

        let mut src_kind: Vec<usize> = Vec::with_capacity(layout.len());
        let mut src_pos: Vec<usize> = Vec::with_capacity(layout.len());
        for addr in &layout {
            if let Some(p) = standard_sorted_addrs[0].iter().position(|a| a == addr) {
                src_kind.push(0);
                src_pos.push(p);
            } else if let Some(p) = extra_addrs.iter().position(|a| a == addr) {
                src_kind.push(1);
                src_pos.push(p);
            } else {
                panic!(
                    "layer-0 layout entry {:?} is neither a gate input nor a cache extra",
                    addr
                );
            }
        }

        (helpers, calls, layout, src_kind, src_pos)
    };
    layer_functions.extend(virtual_setup_helpers);

    let layer_0_n_extra: usize = layer_0_src_kind.iter().filter(|&&k| k == 1).count();

    for config_idx in (0..num_standard_layers).rev() {
        let num_sumcheck_rounds = trace_len_log_2;
        let num_dedup_addrs = standard_sorted_addrs[config_idx].len();
        let num_output_addrs = get_output_sorted_addrs(config_idx).len();
        let compute_claim_fn = quote::format_ident!("layer_{}_compute_claim", config_idx);
        let final_step_fn = quote::format_ident!("layer_{}_final_step_accumulator", config_idx);
        // New last-round form: every coordinate (including the last) is folded by a univariate
        // round inside `verify_sumcheck_rounds`, so the number of rounds there is the full count.
        let num_regular_rounds = num_sumcheck_rounds;

        let is_layer_0 = config_idx == 0;

        let extra_addrs = collect_extra_addrs_from_cached_relations(
            &compiled_circuit.layers[config_idx],
            &standard_sorted_addrs[config_idx],
        );
        let num_extra = extra_addrs.len();

        let regular_set: std::collections::BTreeSet<GKRAddress> =
            standard_sorted_addrs[config_idx].iter().copied().collect();
        let target_addrs: Vec<GKRAddress> = {
            let mut addrs = regular_set.clone();
            for a in &extra_addrs {
                addrs.insert(*a);
            }
            addrs.into_iter().collect()
        };

        let (fold_and_extras_code, cache_check_code, virtual_setup_calls_emit) = if is_layer_0 {
            let n_total = layer_0_layout.len();
            let n_extra = layer_0_n_extra;
            let layout_kind: Vec<usize> = layer_0_src_kind.clone();
            let layout_pos: Vec<usize> = layer_0_src_pos.clone();

            let read_extras = if n_extra > 0 {
                quote! {
                    const EXTRA_COMMIT_BUF: usize = {
                        let total = BLAKE2S_DIGEST_SIZE_U32_WORDS + #n_extra * EXT_DEGREE;
                        total.div_ceil(BLAKE2S_BLOCK_SIZE_U32_WORDS) * BLAKE2S_BLOCK_SIZE_U32_WORDS
                    };
                    let mut extra_buf = CommitBuf::<EXTRA_COMMIT_BUF>::new();
                    let extra_data_words = #n_extra * EXT_DEGREE;
                    {
                        let mut i = 0;
                        while i < extra_data_words {
                            extra_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                            i += 1;
                        }
                    }
                    let mut extra_evals = LazyVec::<#quartic_struct, #n_extra>::new();
                    {
                        let slice: &[#quartic_struct] = unsafe { extra_buf.data_as(#n_extra) };
                        for el in slice {
                            extra_evals.push(*el);
                        }
                    }
                    ts.commit(&mut extra_buf, extra_data_words);
                }
            } else {
                quote! {
                    let extra_evals = LazyVec::<#quartic_struct, 0usize>::new();
                }
            };

            let fold = quote! {
                #read_extras
                let final_step_evals: &[[#quartic_struct; 1]] = unsafe { eval_buf.data_as(#num_dedup_addrs) };
                state.prev_claims.clear();
                {
                    const LAYOUT_KIND: [usize; #n_total] = [#( #layout_kind ),*];
                    const LAYOUT_POS:  [usize; #n_total] = [#( #layout_pos  ),*];
                    let mut i = 0usize;
                    while i < #n_total {
                        let kind = unsafe { *LAYOUT_KIND.get_unchecked(i) };
                        let pos = unsafe { *LAYOUT_POS.get_unchecked(i)  };
                        let claim: #quartic_struct = if kind == 0usize {
                            // At-point evaluation sent directly by the prover.
                            unsafe { final_step_evals.get_unchecked(pos)[0] }
                        } else {
                            *extra_evals.get(pos)
                        };
                        state.prev_claims.push(claim);
                        i += 1;
                    }
                }
            };

            let cache_check = generate_cache_relation_checks::<MW>(
                &compiled_circuit.layers[0],
                &layer_0_layout,
                0,
            );

            (fold, cache_check, virtual_setup_calls.clone())
        } else {
            let fold = if num_extra > 0 {
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

                quote! {
                    const EXTRA_COMMIT_BUF: usize = {
                        let total = BLAKE2S_DIGEST_SIZE_U32_WORDS + #num_extra * EXT_DEGREE;
                        total.div_ceil(BLAKE2S_BLOCK_SIZE_U32_WORDS) * BLAKE2S_BLOCK_SIZE_U32_WORDS
                    };
                    let mut extra_buf = CommitBuf::<EXTRA_COMMIT_BUF>::new();
                    let extra_data_words = #num_extra * EXT_DEGREE;
                    {
                        let mut i = 0;
                        while i < extra_data_words {
                            extra_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
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
                    let final_step_evals: &[[#quartic_struct; 1]] = unsafe { eval_buf.data_as(#num_dedup_addrs) };
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
                                // At-point evaluation sent directly by the prover.
                                state.prev_claims.push(final_step_evals.get_unchecked(regular_idx)[0]);
                                regular_idx += 1;
                            }
                            merged_idx += 1;
                        }
                    }
                }
            } else {
                quote! {
                    fold_standard_claims::<#num_dedup_addrs, GKR_ADDRS, GKR_EVAL_BUF>(
                        &eval_buf, &mut state.prev_claims);
                }
            };

            let cache_check = generate_cache_relation_checks::<MW>(
                &compiled_circuit.layers[config_idx],
                &target_addrs,
                config_idx,
            );

            (fold, cache_check, TokenStream::new())
        };

        let label = &format!("GKR MAIN LAYER {config_idx}");
        main_body.extend(quote! {
            {
                let initial_claim = #compute_claim_fn(state.prev_claims.as_array::<#num_output_addrs>(), state.batching_challenge);
                // All folding rounds (incl. the last) are verified here; `final_claim` is the
                // running claim after the last challenge and `state.prev_point` holds the full
                // folding point.
                let (final_claim, final_eq_prefactor) =
                    verify_sumcheck_rounds::<I, E, #num_regular_rounds, GKR_COMMIT_BUF>(
                        ts, initial_claim, &mut state.prev_point, #config_idx, nd_source)?;
                let fc_len = #num_regular_rounds;
                // Half the data: one at-point evaluation per input poly (was two endpoints).
                let data_words = #num_dedup_addrs * EXT_DEGREE;
                {
                    let mut i = 0;
                    while i < data_words {
                        eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                        i += 1;
                    }
                }
                {
                    let evals: &[[#quartic_struct; 1]] = eval_buf.data_as(#num_dedup_addrs);
                    // Half the work: evaluate the GKR kernels at a single set of inputs.
                    let f = #final_step_fn(evals, state.batching_challenge,
                        lookup_additive_challenge, lookup_alpha,
                        &external_challenges.permutation_argument_linearization_challenges,
                        external_challenges.permutation_argument_additive_part,
                        address_high_bits_shift,
                        &initial_transcript.inits_and_teardowns_top_bits);
                    verify_final_step_check::<E>(f[0],
                        final_eq_prefactor, final_claim, #config_idx)?;
                }
                ts.commit(&mut eval_buf, data_words);
                let next_batching = draw_single_field_el(ts);
                #fold_and_extras_code
                #cache_check_code
                #virtual_setup_calls_emit
                state.batching_challenge = next_batching;
                state.prev_point_len = fc_len;

                #[cfg(feature = "verifier_stats")]
                    verifier_common::stats::log(#label);
            }
        });
    }

    let mut output_checks = TokenStream::new();
    {
        let mul = |a: TokenStream, b: TokenStream| MW::mul_assign(a, b);
        let add = |a: TokenStream, b: TokenStream| MW::add_assign(a, b);

        let mut eval_offset = 0usize;
        let mut lookup_type_idx = 0usize;
        let mut permutation_product_emitted = false;
        for group in &output_groups {
            match group.output_type {
                OutputType::PermutationProduct => {
                    assert_eq!(group.num_addresses, 2);
                    let read_off = eval_offset;
                    let write_off = eval_offset + evals_per_poly;
                    eval_offset += 2 * evals_per_poly;

                    let mul_rp = mul(quote! { read_product }, quote! { eval });
                    let mul_wp = mul(quote! { write_product }, quote! { eval });
                    output_checks.extend(quote! {
                        {
                            let mut read_product = #quartic_one;
                            for i in 0..#evals_per_poly {
                                let eval = *evals_slice.get_unchecked(#read_off + i);
                                #mul_rp;
                            }
                            let mut write_product = #quartic_one;
                            for i in 0..#evals_per_poly {
                                let eval = *evals_slice.get_unchecked(#write_off + i);
                                #mul_wp;
                            }
                            permutation_read_product = read_product;
                            permutation_write_product = write_product;
                        }
                    });
                    permutation_product_emitted = true;
                }
                OutputType::InitsAndTeardownsProduct => {
                    assert!(permutation_product_emitted);
                    assert_eq!(group.num_addresses, 2);
                    let read_off = eval_offset;
                    let write_off = eval_offset + evals_per_poly;
                    eval_offset += 2 * evals_per_poly;

                    let mul_rp = mul(quote! { it_read }, quote! { eval });
                    let mul_wp = mul(quote! { it_write }, quote! { eval });
                    output_checks.extend(quote! {
                        {
                            let mut it_read = #quartic_one;
                            for i in 0..#evals_per_poly {
                                let eval = *evals_slice.get_unchecked(#read_off + i);
                                #mul_rp;
                            }
                            let mut it_write = #quartic_one;
                            for i in 0..#evals_per_poly {
                                let eval = *evals_slice.get_unchecked(#write_off + i);
                                #mul_wp;
                            }
                            inits_and_teardowns_read_product = it_read;
                            inits_and_teardowns_write_product = it_write;
                        }
                    });
                }
                OutputType::Lookup16Bits
                | OutputType::LookupTimestamps
                | OutputType::GenericLookup => {
                    let num_off = eval_offset;
                    let den_off = eval_offset + evals_per_poly;
                    eval_offset += 2 * evals_per_poly;
                    let lt_idx = lookup_type_idx;
                    lookup_type_idx += 1;

                    let mul_an_d = mul(quote! { acc_num }, quote! { d });
                    let mul_n_ad = mul(quote! { t }, quote! { acc_den });
                    let add_an_t = add(quote! { acc_num }, quote! { t });
                    let mul_ad_d = mul(quote! { acc_den }, quote! { d });
                    output_checks.extend(quote! {
                        {
                            let mut acc_num = #quartic_zero;
                            let mut acc_den = #quartic_one;
                            for i in 0..#evals_per_poly {
                                let n = *evals_slice.get_unchecked(#num_off + i);
                                let d = *evals_slice.get_unchecked(#den_off + i);
                                // acc_num = acc_num * d + n * acc_den
                                #mul_an_d;
                                let mut t = n;
                                #mul_n_ad;
                                #add_an_t;
                                // acc_den = acc_den * d
                                #mul_ad_d;
                            }
                            if !acc_num.is_zero() || acc_den.is_zero() {
                                return Err(E::gkr_lookup_identity_failed(#lt_idx));
                            }
                        }
                    });
                }
            }
        }
    }

    main_body.extend(quote! {
        state.batching_challenge = draw_single_field_el(ts);

        let mut permutation_read_product: #quartic_struct = #quartic_one;
        let mut permutation_write_product: #quartic_struct = #quartic_one;
        #[allow(unused_mut)]
        let mut inits_and_teardowns_read_product: #quartic_struct = #quartic_one;
        #[allow(unused_mut)]
        let mut inits_and_teardowns_write_product: #quartic_struct = #quartic_one;

        #output_checks

        #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR MAIN OUTPUT");

        Ok(GKRVerifierOutput {
            base_layer_claims: state.prev_claims,
            evaluation_point: state.prev_point,
            evaluation_point_len: state.prev_point_len,
            permutation_read_product,
            permutation_write_product,
            inits_and_teardowns_read_product,
            inits_and_teardowns_write_product,
            whir_batching_challenge: state.batching_challenge,
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

    let max_pow_entries: usize = whir_queries[..whir_rounds - 1].iter().map(|q| 1 + q).sum();

    let total_fold_steps: usize = whir_fold_steps.iter().sum();
    assert!(
        trace_len_log2 >= total_fold_steps,
        "total fold steps ({}) exceed trace_len_log2 ({})",
        total_fold_steps,
        trace_len_log2
    );
    let final_m = trace_len_log2 - total_fold_steps;
    let final_monomials_len = 1usize << final_m;

    let base_lde_factor_log2 = whir_base_lde_factor.trailing_zeros() as usize;
    let initial_fold_steps = whir_fold_steps[0];
    let configured_cap_size: usize = whir_schedule.cap_size;
    assert!(configured_cap_size > 0);
    let cap_size_log2 = configured_cap_size.trailing_zeros() as usize;
    let canonical_depth =
        trace_len_log2 + base_lde_factor_log2 - initial_fold_steps - cap_size_log2;

    let mut oracles = BTreeMap::new();
    {
        // memory
        let num_columns = compiled_circuit.memory_layout.total_width;
        if num_columns > 0 {
            let info = OracleInfo {
                num_columns,
                cap_size: configured_cap_size,
                depth: canonical_depth,
            };
            oracles.insert(OracleType::Memory, info);
        }

        // witness
        let num_columns = compiled_circuit.witness_layout.total_width;
        if num_columns > 0 {
            let info = OracleInfo {
                num_columns,
                cap_size: configured_cap_size,
                depth: canonical_depth,
            };
            oracles.insert(OracleType::Witness, info);
        }

        // setup
        let num_columns = compiled_circuit.generic_lookup_tables_width;
        if num_columns > 0 {
            let info = OracleInfo {
                num_columns,
                cap_size: configured_cap_size,
                depth: canonical_depth,
            };
            oracles.insert(OracleType::Setup, info);
        }
    }

    let total_oracle_cols: usize = oracles.iter().map(|(_, o)| o.num_columns).sum();
    let digest_words = prover::transcript::blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;
    let whir_cap_words = whir_cap_size * digest_words;

    let oracle_depths: Vec<usize> = oracles.iter().map(|(_, o)| o.depth).collect();
    let oracle_num_cols: Vec<usize> = oracles.iter().map(|(_, o)| o.num_columns).collect();
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
        use ::verifier_common::blake2s_u32::{
            BLAKE2S_BLOCK_SIZE_U32_WORDS, BLAKE2S_DIGEST_SIZE_U32_WORDS,
        };
        use ::verifier_common::{DIM_REDUCE_EVAL_POINTS, STANDARD_EVAL_POINTS, SUMCHECK_POLY_COEFFS};
        use super::common::EXT_DEGREE;

        // Upper bound on GKR sumcheck rounds for internal buffers
        pub const GKR_ROUNDS: usize = #max_sumcheck_rounds;

        pub const GKR_ADDRS: usize = #max_addrs;
        pub const GKR_EVALS: usize = #max_evals;

        pub const INIT_AND_TEARDOWN_SETS: usize = #num_teardown_sets;

        pub const EXTERNAL_CHALLENGES_FLATTENED_SIZE: usize =
            EXT_DEGREE * (#num_linearization_challenges + 1);

        pub const CAP_SIZE: usize = #configured_cap_size;

        pub const NUM_MEMORY_COMMITS: usize = #num_memory_commits;
        pub const NUM_WITNESS_COMMITS: usize = #num_witness_commits;
        pub const NUM_SETUP_COMMITS: usize = #num_setup_commits;

        pub const PADDING_WORDS: usize = {
            let mut total = #num_teardown_sets;
            total += EXT_DEGREE
                * (::verifier_common::cs::definitions::NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES + 1);
            total += CAP_SIZE
                * BLAKE2S_DIGEST_SIZE_U32_WORDS
                * (NUM_MEMORY_COMMITS + NUM_WITNESS_COMMITS + NUM_SETUP_COMMITS);
            let rem = total % BLAKE2S_BLOCK_SIZE_U32_WORDS;
            if rem == 0 { 0 } else { BLAKE2S_BLOCK_SIZE_U32_WORDS - rem }
        };

        pub const GKR_EVAL_BUF: usize = {
            let dim_reducing = #max_addrs * DIM_REDUCE_EVAL_POINTS * EXT_DEGREE;
            let standard = #max_addrs * STANDARD_EVAL_POINTS * EXT_DEGREE;
            let evals = #max_evals * EXT_DEGREE;
            let max_data = if dim_reducing > standard { dim_reducing } else { standard };
            let max_data = if max_data > evals { max_data } else { evals };
            let total = BLAKE2S_DIGEST_SIZE_U32_WORDS + max_data;
            total.div_ceil(BLAKE2S_BLOCK_SIZE_U32_WORDS) * BLAKE2S_BLOCK_SIZE_U32_WORDS
        };
        pub const GKR_COMMIT_BUF: usize = {
            let total = BLAKE2S_DIGEST_SIZE_U32_WORDS + SUMCHECK_POLY_COEFFS * EXT_DEGREE;
            total.div_ceil(BLAKE2S_BLOCK_SIZE_U32_WORDS) * BLAKE2S_BLOCK_SIZE_U32_WORDS
        };
        pub const GKR_EVALS_COMMIT_BUF: usize = {
            let total = BLAKE2S_DIGEST_SIZE_U32_WORDS + #max_evals * EXT_DEGREE;
            total.div_ceil(BLAKE2S_BLOCK_SIZE_U32_WORDS) * BLAKE2S_BLOCK_SIZE_U32_WORDS
        };
        pub const DRAW_BUF_CAPACITY: usize =
            (#num_challenges * EXT_DEGREE).next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS);
        pub const WHIR_FOLD_STEPS: [usize; #whir_rounds] = [#(#whir_fold_steps),*];
        pub const WHIR_QUERIES: [usize; #whir_rounds] = [#(#whir_queries),*];
        pub const WHIR_POW_BITS: [u32; #whir_rounds] = [#(#whir_pow_bits),*];
        pub const MAX_POW_ENTRIES: usize = #max_pow_entries;
        pub const FINAL_MONOMIALS_LEN: usize = #final_monomials_len;
        pub const NUM_ORACLES: usize = #num_oracles;
        pub const ORACLE_NUM_COLS: [usize; #num_oracles] = [#(#oracle_num_cols),*];
        pub const ORACLE_DEPTHS: [usize; #num_oracles] = [#(#oracle_depths),*];
        pub const TOTAL_ORACLE_COLS: usize = #total_oracle_cols;
        pub const WHIR_ORACLE_DEPTHS: [usize; #num_intermediate_oracles] = [#(#whir_oracle_depths),*];
        pub const WHIR_CAP_WORDS: usize = #whir_cap_words;

        #field_use_stmts

        pub type ConcreteInitialTranscript = ::verifier_common::InitialGKRTranscript<
            #quartic_struct,
            INIT_AND_TEARDOWN_SETS,
            EXTERNAL_CHALLENGES_FLATTENED_SIZE,
            CAP_SIZE,
            NUM_MEMORY_COMMITS,
            NUM_WITNESS_COMMITS,
            NUM_SETUP_COMMITS,
            PADDING_WORDS,
        >;
        pub type ConcreteGKRVerifierOutput = ::verifier_common::GKRVerifierOutput<#quartic_struct, GKR_ROUNDS, GKR_ADDRS>;
        pub type ConcreteVerifierOutput = ::verifier_common::VerifierOutput<#quartic_struct, INIT_AND_TEARDOWN_SETS, CAP_SIZE, NUM_MEMORY_COMMITS, NUM_SETUP_COMMITS>;

    };

    let gkr = quote! {
        #field_use_stmts
        use ::verifier_common::gkr::{
            GKRVerifierOutput, LayerState,
        };
        use ::verifier_common::lazy_vec::LazyVec;
        use ::verifier_common::errors::ErrorCreator;
        use ::verifier_common::structs::{CommitBuf, TranscriptState};
        use ::verifier_common::blake2s_u32::{
            BLAKE2S_BLOCK_SIZE_U32_WORDS, BLAKE2S_DIGEST_SIZE_U32_WORDS,
        };
        use super::common::{
            verify_sumcheck_rounds, verify_final_step_check, fold_standard_claims,
            make_eq_poly, dot_eq, draw_field_els_into, draw_single_field_el,
            read_field_el, read_reduced_field_el,
            ext_from_nds, ext_from_raw_words,
            EXT_DEGREE,
        };
        use ::verifier_common::field_ops;
        use ::verifier_common::field::{Field, FieldExtension, PrimeField};
        use ::verifier_common::non_determinism_source::NonDeterminismSource;
        use ::verifier_common::GKRExternalChallenges;
        use ::verifier_common::gkr::SimpleGateType;
        use super::constants::*;

        #layer_functions

        #[allow(unused_variables, unused_mut, unused_unsafe)]
        pub(crate) fn verify_gkr<I: NonDeterminismSource, E: ErrorCreator>(
            external_challenges: &GKRExternalChallenges<#field_struct, #quartic_struct>,
            initial_transcript: &ConcreteInitialTranscript,
            ts: &mut ::verifier_common::structs::TranscriptState,
            nd_source: &mut I,
        ) -> Result<ConcreteGKRVerifierOutput, E::Error> {
            unsafe { #main_body }
        }

        pub struct VerifierImplementation;

        impl ::verifier_common::ConcreteVerifierImpl<
            #field_struct,
            #quartic_struct,
            INIT_AND_TEARDOWN_SETS,
            EXTERNAL_CHALLENGES_FLATTENED_SIZE,
            CAP_SIZE,
            NUM_MEMORY_COMMITS,
            NUM_WITNESS_COMMITS,
            NUM_SETUP_COMMITS,
            PADDING_WORDS,
            GKR_ROUNDS,
            GKR_ADDRS,
        > for VerifierImplementation {
            #[inline(always)]
            fn verify_gkr<I: NonDeterminismSource, E: ErrorCreator>(
                external_challenges: &GKRExternalChallenges<#field_struct, #quartic_struct>,
                initial_transcript: &ConcreteInitialTranscript,
                transcript_state: &mut ::verifier_common::structs::TranscriptState,
                nd_source: &mut I,
            ) -> Result<ConcreteGKRVerifierOutput, E::Error> {
                verify_gkr::<I, E>(
                    external_challenges,
                    initial_transcript,
                    transcript_state,
                    nd_source,
                )
            }
            #[inline(always)]
            fn verify_whir<I: NonDeterminismSource, E: ErrorCreator>(
                initial_transcript: &ConcreteInitialTranscript,
                transcript_state: &mut ::verifier_common::structs::TranscriptState,
                whir_batching_challenge: #quartic_struct,
                base_layer_claims: &[#quartic_struct],
                initial_claim_point: &[#quartic_struct],
                nd_source: &mut I,
            ) -> Result<(), E::Error> {
                super::whir::verify_whir::<I, E>(
                    initial_transcript,
                    transcript_state,
                    whir_batching_challenge,
                    base_layer_claims,
                    initial_claim_point,
                    nd_source,
                )
            }
        }
    };

    GKRGeneratedFiles {
        constants,
        gkr,
        oracles,
        trace_len_log2,
    }
}
