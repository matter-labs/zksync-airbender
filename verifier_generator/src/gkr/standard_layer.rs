use proc_macro2::TokenStream;
use quote::quote;

use crate::field_wrapper::FieldWrapper;
use prover::cs::definitions::gkr::NoFieldVectorLookupRelation;
use prover::cs::definitions::gkr::RamWordRepresentation;
use prover::cs::definitions::GKRAddress;
use prover::cs::definitions::{
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
};
use prover::cs::gkr_compiler::{
    CompiledAddressSpaceRelationStrict, CompiledAddressStrict, CompiledMemoryTimestamp,
    GKRLayerDescription, InitsOrTeardownsTimestampAndValue, NoFieldGKRRelation,
    NoFieldSpecialMemoryContributionRelation,
};
use prover::field::PrimeField;
use verifier_common::gkr::SimpleGateType;

use super::addr_to_idx;
use super::coeff_to_internal_repr;

pub fn generate_eval_helpers<MW: FieldWrapper>() -> TokenStream {
    let field_struct = MW::field_struct();
    let quartic_struct = MW::quartic_struct();
    let quartic_zero = MW::quartic_zero();
    let quartic_one = MW::quartic_one();

    let from_const = MW::field_from_reduced_raw_repr(quote! { constant as u32 });
    let from_coeff = MW::field_from_reduced_raw_repr(quote! { coeff as u32 });
    let from_col_const = MW::field_from_reduced_raw_repr(quote! { col_const as u32 });
    let mul_t_by_coeff = MW::mul_assign_by_base(quote! { t }, from_coeff.clone());

    let lr_add = MW::add_assign(quote! { result }, quote! { t });

    let vl_mul_alpha = MW::mul_assign(quote! { result }, quote! { alpha });
    let vl_col_add = MW::add_assign(quote! { col_val }, quote! { t });
    let vl_result_add = MW::add_assign(quote! { result }, quote! { col_val });

    let mq_inner_add = MW::add_assign(quote! { inner }, quote! { t });
    let mq_mul_a = MW::mul_assign(quote! { inner }, quote! { a_val });
    let mq_add_inner = MW::add_assign(quote! { val }, quote! { inner });
    let mq_lin_mul = MW::mul_assign_by_base(quote! { lt }, from_coeff.clone());
    let mq_lin_add = MW::add_assign(quote! { val }, quote! { lt });

    let me_add_base = MW::field_from_reduced_raw_repr(quote! { op[1] as u32 });
    let me_add_base_assign = MW::add_assign_base(quote! { result }, me_add_base.clone());
    let me_add_eval = MW::add_assign(quote! { result }, quote! { evals.get_unchecked(op[1])[j] });
    let me_sub_eval = MW::sub_assign(quote! { t }, quote! { evals.get_unchecked(op[1])[j] });
    let me_add_t = MW::add_assign(quote! { result }, quote! { t });
    let me_ch_mul_eval =
        MW::mul_assign_by_base(quote! { t }, quote! { evals.get_unchecked(op[2])[j] });
    let me_ch_add = MW::add_assign(quote! { result }, quote! { t });
    let me_ch_mul_const_val = MW::field_from_reduced_raw_repr(quote! { op[2] as u32 });
    let me_ch_mul_const = MW::mul_assign_by_base(quote! { t }, me_ch_mul_const_val.clone());
    let me_ev_plus_const = MW::field_from_reduced_raw_repr(quote! { op[3] as u32 });
    let me_add_const_to_ev = MW::add_assign_base(quote! { ev }, me_ev_plus_const.clone());
    let me_mul_ev = MW::mul_assign_by_base(quote! { t }, quote! { ev });
    let me_dyn_const = MW::field_from_reduced_raw_repr(quote! { op[4] as u32 });
    let me_dyn_add_const = MW::add_assign_base(quote! { ev }, me_dyn_const.clone());
    let me_dyn_coeff = MW::field_from_reduced_raw_repr(quote! { op[5] as u32 });
    let me_dyn_mul = MW::mul_assign_by_base(quote! { dyn_val }, me_dyn_coeff.clone());
    let me_dyn_add = MW::add_assign(quote! { ev }, quote! { dyn_val });
    let byte_shift_field = quote! { #field_struct::from_u32_with_reduction(1u32 << 8) };
    let me_byte_mul = MW::mul_assign_by_base(quote! { hi }, byte_shift_field.clone());
    let me_byte_add_lo = MW::add_assign(quote! { hi }, quote! { evals.get_unchecked(op[2])[j] });
    let me_byte_ch_mul = MW::mul_assign(quote! { t }, quote! { hi });

    quote! {
        #[inline(always)]
        #[allow(unused_variables)]
        pub unsafe fn eval_linear_relation(
            evals: &[[#quartic_struct; 2]],
            terms: &[(usize, usize)],
            constant: usize,
            j: usize,
        ) -> #quartic_struct {
            let mut result = #quartic_struct::from_base(#from_const);
            let mut i = 0;
            while i < terms.len() {
                let (idx, coeff) = *terms.get_unchecked(i);
                let mut t = evals.get_unchecked(idx)[j];
                #mul_t_by_coeff;
                #lr_add;
                i += 1;
            }
            result
        }

        #[inline(always)]
        #[allow(unused_variables)]
        pub unsafe fn eval_vector_lookup(
            evals: &[[#quartic_struct; 2]],
            alpha: #quartic_struct,
            col_descs: &[(usize, usize)],
            terms: &[(usize, usize)],
            j: usize,
        ) -> #quartic_struct {
            let mut result = #quartic_zero;
            let mut term_offset: usize = 0;
            let mut i = 0;
            while i < col_descs.len() {
                #vl_mul_alpha;
                let (col_const, num_terms) = *col_descs.get_unchecked(i);
                let mut col_val = #quartic_struct::from_base(#from_col_const);
                let mut k = 0;
                while k < num_terms {
                    let (idx, coeff) = *terms.get_unchecked(term_offset + k);
                    let mut t = evals.get_unchecked(idx)[j];
                    #mul_t_by_coeff;
                    #vl_col_add;
                    k += 1;
                }
                #vl_result_add;
                term_offset += num_terms;
                i += 1;
            }
            result
        }

        #[inline(always)]
        #[allow(unused_variables)]
        pub unsafe fn eval_max_quadratic(
            evals: &[[#quartic_struct; 2]],
            quad_outer: &[(usize, usize)],
            quad_inner: &[(usize, usize)],
            linear: &[(usize, usize)],
            constant: usize,
            j: usize,
        ) -> #quartic_struct {
            let mut val = #quartic_struct::from_base(#from_const);
            let mut inner_offset: usize = 0;
            let mut i = 0;
            while i < quad_outer.len() {
                let (addr_a, num_inner) = *quad_outer.get_unchecked(i);
                let mut inner = #quartic_zero;
                let mut k = 0;
                while k < num_inner {
                    let (addr_b, coeff) = *quad_inner.get_unchecked(inner_offset + k);
                    let mut t = evals.get_unchecked(addr_b)[j];
                    #mul_t_by_coeff;
                    #mq_inner_add;
                    k += 1;
                }
                let a_val = evals.get_unchecked(addr_a)[j];
                #mq_mul_a;
                #mq_add_inner;
                inner_offset += num_inner;
                i += 1;
            }
            let mut li = 0;
            while li < linear.len() {
                let (addr, coeff) = *linear.get_unchecked(li);
                let mut lt = evals.get_unchecked(addr)[j];
                #mq_lin_mul;
                #mq_lin_add;
                li += 1;
            }
            val
        }

        pub const ME_OP_ADD_BASE_CONST: usize = 0;
        pub const ME_OP_ADD_EVAL: usize = 1;
        pub const ME_OP_ADD_ONE_MINUS_EVAL: usize = 2;
        pub const ME_OP_CH_MUL_EVAL: usize = 3;
        pub const ME_OP_CH_MUL_CONST: usize = 4;
        pub const ME_OP_CH_MUL_EVAL_PLUS_CONST: usize = 5;
        pub const ME_OP_CH_MUL_EVAL_PLUS_DYN: usize = 6;
        pub const ME_OP_BYTE_VALUE_PAIR: usize = 7;

        #[inline(always)]
        #[allow(unused_variables)]
        pub unsafe fn eval_memory_expr(
            evals: &[[#quartic_struct; 2]],
            challenges: &[#quartic_struct],
            additive_part: #quartic_struct,
            ops: &[[usize; 6]],
            j: usize,
        ) -> #quartic_struct {
            let mut result = additive_part;
            let mut i = 0;
            while i < ops.len() {
                let op = *ops.get_unchecked(i);
                match op[0] {
                    ME_OP_ADD_BASE_CONST => {
                        #me_add_base_assign;
                    }
                    ME_OP_ADD_EVAL => {
                        #me_add_eval;
                    }
                    ME_OP_ADD_ONE_MINUS_EVAL => {
                        let mut t = #quartic_one;
                        #me_sub_eval;
                        #me_add_t;
                    }
                    ME_OP_CH_MUL_EVAL => {
                        let mut t = challenges[op[1]];
                        #me_ch_mul_eval;
                        #me_ch_add;
                    }
                    ME_OP_CH_MUL_CONST => {
                        let mut t = challenges[op[1]];
                        #me_ch_mul_const;
                        #me_ch_add;
                    }
                    ME_OP_CH_MUL_EVAL_PLUS_CONST => {
                        let mut ev = evals.get_unchecked(op[2])[j];
                        #me_add_const_to_ev;
                        let mut t = challenges[op[1]];
                        #me_mul_ev;
                        #me_ch_add;
                    }
                    ME_OP_CH_MUL_EVAL_PLUS_DYN => {
                        let mut ev = evals.get_unchecked(op[2])[j];
                        if op[4] != 0 {
                            #me_dyn_add_const;
                        }
                        let mut dyn_val = evals.get_unchecked(op[3])[j];
                        #me_dyn_mul;
                        #me_dyn_add;
                        let mut t = challenges[op[1]];
                        #me_mul_ev;
                        #me_ch_add;
                    }
                    ME_OP_BYTE_VALUE_PAIR => {
                        let mut hi = evals.get_unchecked(op[3])[j];
                        #me_byte_mul;
                        #me_byte_add_lo;
                        let mut t = challenges[op[1]];
                        #me_byte_ch_mul;
                        #me_ch_add;
                    }
                    _ => core::hint::unreachable_unchecked(),
                }
                i += 1;
            }
            result
        }
    }
}

fn emit_linear_relation_eval<MW: FieldWrapper, F: PrimeField>(
    rel: &prover::cs::definitions::gkr::NoFieldLinearRelation,
    var_name: &str,
    input_sorted_addrs: &[GKRAddress],
) -> TokenStream {
    let var = syn::Ident::new(var_name, proc_macro2::Span::call_site());
    let terms_name = syn::Ident::new(
        &format!("{}_TERMS", var_name.to_uppercase()),
        proc_macro2::Span::call_site(),
    );

    let const_mont = coeff_to_internal_repr::<F>(rel.constant) as usize;
    let mut term_idx = Vec::new();
    let mut term_coeff = Vec::new();
    for &(coeff, ref addr) in rel.linear_terms.iter() {
        term_idx.push(addr_to_idx(addr, input_sorted_addrs));
        term_coeff.push(coeff_to_internal_repr::<F>(coeff) as usize);
    }
    let num_terms = term_idx.len();

    quote! {
        const #terms_name: [(usize, usize); #num_terms] = [
            #( (#term_idx, #term_coeff), )*
        ];
        let mut #var = super::common::eval_linear_relation(evals, &#terms_name, #const_mont, j);
    }
}

fn emit_vector_lookup_eval<MW: FieldWrapper, F: PrimeField>(
    rel: &NoFieldVectorLookupRelation,
    var_name: &str,
    input_sorted_addrs: &[GKRAddress],
) -> TokenStream {
    let var = syn::Ident::new(var_name, proc_macro2::Span::call_site());
    let cols_name = syn::Ident::new(
        &format!("{}_COLS", var_name.to_uppercase()),
        proc_macro2::Span::call_site(),
    );
    let terms_name = syn::Ident::new(
        &format!("{}_VL_TERMS", var_name.to_uppercase()),
        proc_macro2::Span::call_site(),
    );

    let mut col_consts = Vec::new();
    let mut col_counts = Vec::new();
    let mut all_term_idx = Vec::new();
    let mut all_term_coeff = Vec::new();

    for col in rel.columns.iter().rev() {
        col_consts.push(coeff_to_internal_repr::<F>(col.constant) as usize);
        col_counts.push(col.linear_terms.len());
        for &(coeff, ref addr) in col.linear_terms.iter() {
            all_term_idx.push(addr_to_idx(addr, input_sorted_addrs));
            all_term_coeff.push(coeff_to_internal_repr::<F>(coeff) as usize);
        }
    }
    let num_cols = col_consts.len();
    let num_terms = all_term_idx.len();

    quote! {
        const #cols_name: [(usize, usize); #num_cols] = [
            #( (#col_consts, #col_counts), )*
        ];
        const #terms_name: [(usize, usize); #num_terms] = [
            #( (#all_term_idx, #all_term_coeff), )*
        ];
        let mut #var = super::common::eval_vector_lookup(evals, lookup_alpha, &#cols_name, &#terms_name, j);
    }
}

fn emit_single_output_gate<MW: FieldWrapper>(
    body: &mut TokenStream,
    mul_batch: &TokenStream,
    val_computation: TokenStream,
) {
    let mul_contrib = MW::mul_assign(quote! { contrib }, quote! { val });
    let add_acc = MW::add_assign(quote! { acc[j] }, quote! { contrib });
    body.extend(quote! {
        {
            let bc = current_batch;
            #mul_batch;
            for j in 0..2 {
                #val_computation
                let mut contrib = bc;
                #mul_contrib;
                #add_acc;
            }
        }
    });
}

fn emit_setup_horner_eval<F: PrimeField>(
    addrs: &[GKRAddress],
    var_name: &str,
    input_sorted_addrs: &[GKRAddress],
) -> TokenStream {
    let var = syn::Ident::new(var_name, proc_macro2::Span::call_site());
    let cols_name = syn::Ident::new(
        &format!("{}_COLS", var_name.to_uppercase()),
        proc_macro2::Span::call_site(),
    );
    let terms_name = syn::Ident::new(
        &format!("{}_VL_TERMS", var_name.to_uppercase()),
        proc_macro2::Span::call_site(),
    );

    let one_mont = coeff_to_internal_repr::<F>(1) as usize;
    let mut col_consts = Vec::new();
    let mut col_counts = Vec::new();
    let mut term_idx = Vec::new();
    let mut term_coeff = Vec::new();

    for addr in addrs.iter().rev() {
        col_consts.push(0usize);
        col_counts.push(1usize);
        term_idx.push(addr_to_idx(addr, input_sorted_addrs));
        term_coeff.push(one_mont);
    }
    let num_cols = col_consts.len();
    let num_terms = term_idx.len();

    quote! {
        const #cols_name: [(usize, usize); #num_cols] = [
            #( (#col_consts, #col_counts), )*
        ];
        const #terms_name: [(usize, usize); #num_terms] = [
            #( (#term_idx, #term_coeff), )*
        ];
        let mut #var = super::common::eval_vector_lookup(evals, lookup_alpha, &#cols_name, &#terms_name, j);
    }
}

fn emit_max_quadratic_eval<F: PrimeField>(
    input: &prover::cs::gkr_compiler::NoFieldMaxQuadraticGKRRelation,
    var_name: &str,
    input_sorted_addrs: &[GKRAddress],
) -> TokenStream {
    let var = syn::Ident::new(var_name, proc_macro2::Span::call_site());
    let prefix = var_name.to_uppercase();
    let qo_name = syn::Ident::new(&format!("{}_QO", prefix), proc_macro2::Span::call_site());
    let qi_name = syn::Ident::new(&format!("{}_QI", prefix), proc_macro2::Span::call_site());
    let ln_name = syn::Ident::new(&format!("{}_LN", prefix), proc_macro2::Span::call_site());

    let constant = coeff_to_internal_repr::<F>(input.constant) as usize;

    let mut quad_outer_idx = Vec::new();
    let mut quad_outer_count = Vec::new();
    let mut quad_inner_idx = Vec::new();
    let mut quad_inner_coeff = Vec::new();

    for (addr_a, inner_terms) in input.quadratic_terms.iter() {
        quad_outer_idx.push(addr_to_idx(addr_a, input_sorted_addrs));
        quad_outer_count.push(inner_terms.len());
        for &(coeff, ref addr_b) in inner_terms.iter() {
            quad_inner_idx.push(addr_to_idx(addr_b, input_sorted_addrs));
            quad_inner_coeff.push(coeff_to_internal_repr::<F>(coeff) as usize);
        }
    }

    let mut lin_idx = Vec::new();
    let mut lin_coeff = Vec::new();
    for &(coeff, ref addr) in input.linear_terms.iter() {
        lin_idx.push(addr_to_idx(addr, input_sorted_addrs));
        lin_coeff.push(coeff_to_internal_repr::<F>(coeff) as usize);
    }

    let nqo = quad_outer_idx.len();
    let nqi = quad_inner_idx.len();
    let nl = lin_idx.len();

    quote! {
        const #qo_name: [(usize, usize); #nqo] = [ #( (#quad_outer_idx, #quad_outer_count), )* ];
        const #qi_name: [(usize, usize); #nqi] = [ #( (#quad_inner_idx, #quad_inner_coeff), )* ];
        const #ln_name: [(usize, usize); #nl] = [ #( (#lin_idx, #lin_coeff), )* ];
        let #var = super::common::eval_max_quadratic(evals, &#qo_name, &#qi_name, &#ln_name, #constant, j);
    }
}

fn emit_memory_expression_eval<F: PrimeField>(
    rel: &NoFieldSpecialMemoryContributionRelation,
    var_name: &str,
    input_sorted_addrs: &[GKRAddress],
) -> TokenStream {
    let var = syn::Ident::new(var_name, proc_macro2::Span::call_site());
    let ops_name = syn::Ident::new(
        &format!("{}_OPS", var_name.to_uppercase()),
        proc_macro2::Span::call_site(),
    );

    let blm = |offset: usize| GKRAddress::BaseLayerMemory(offset);
    let idx = |offset: usize| addr_to_idx(&blm(offset), input_sorted_addrs);
    let mont = |v: u32| coeff_to_internal_repr::<F>(v) as usize;

    let mut ops: Vec<[usize; 6]> = Vec::new();

    match &rel.address_space {
        CompiledAddressSpaceRelationStrict::Constant(c) => {
            ops.push([0, mont(*c), 0, 0, 0, 0]);
        }
        CompiledAddressSpaceRelationStrict::IsRam(offset) => {
            ops.push([1, idx(*offset), 0, 0, 0, 0]);
        }
        CompiledAddressSpaceRelationStrict::IsRegister(offset) => {
            ops.push([2, idx(*offset), 0, 0, 0, 0]);
        }
    }

    match &rel.address {
        CompiledAddressStrict::ConstantU16(c) => {
            ops.push([
                4,
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
                mont(*c as u32),
                0,
                0,
                0,
            ]);
        }
        CompiledAddressStrict::Constant(c) => {
            ops.push([
                4,
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
                mont(*c),
                0,
                0,
                0,
            ]);
        }
        CompiledAddressStrict::U16Space(offset) => {
            ops.push([
                3,
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
                idx(*offset),
                0,
                0,
                0,
            ]);
        }
        CompiledAddressStrict::U32Space([low, high]) => {
            ops.push([
                3,
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
                idx(*low),
                0,
                0,
                0,
            ]);
            ops.push([
                3,
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX,
                idx(*high),
                0,
                0,
                0,
            ]);
        }
        CompiledAddressStrict::U32SpaceSpecialIndirect {
            low_base,
            low_dynamic_offset,
            low_offset,
            high,
        } => {
            let base_idx = idx(*low_base);
            let off_mont = mont(*low_offset);
            if let Some((c, dyn_off)) = low_dynamic_offset {
                let dyn_idx = idx(*dyn_off);
                let c_mont = mont(*c as u32);
                ops.push([
                    6,
                    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
                    base_idx,
                    dyn_idx,
                    off_mont,
                    c_mont,
                ]);
            } else if *low_offset != 0 {
                ops.push([
                    5,
                    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
                    base_idx,
                    off_mont,
                    0,
                    0,
                ]);
            } else {
                ops.push([
                    3,
                    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
                    base_idx,
                    0,
                    0,
                    0,
                ]);
            }
            ops.push([
                3,
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX,
                idx(*high),
                0,
                0,
                0,
            ]);
        }
        CompiledAddressStrict::U32SpaceGeneric(..) => {
            panic!("U32SpaceGeneric not supported in verifier generator");
        }
    }

    match &rel.timestamp {
        CompiledMemoryTimestamp::Zero => {}
        CompiledMemoryTimestamp::Normal(ts) => {
            let ts_off = rel.timestamp_offset;
            if ts_off != 0 {
                ops.push([
                    5,
                    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX,
                    idx(ts[0]),
                    mont(ts_off),
                    0,
                    0,
                ]);
            } else {
                ops.push([
                    3,
                    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX,
                    idx(ts[0]),
                    0,
                    0,
                    0,
                ]);
            }
            ops.push([
                3,
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX,
                idx(ts[1]),
                0,
                0,
                0,
            ]);
        }
    }

    match &rel.value {
        RamWordRepresentation::Zero => {}
        RamWordRepresentation::U16Limbs(limbs) => {
            ops.push([
                3,
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
                idx(limbs[0]),
                0,
                0,
                0,
            ]);
            ops.push([
                3,
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
                idx(limbs[1]),
                0,
                0,
                0,
            ]);
        }
        RamWordRepresentation::U8Limbs(bytes) => {
            ops.push([
                7,
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
                idx(bytes[0]),
                idx(bytes[1]),
                0,
                0,
            ]);
            ops.push([
                7,
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
                idx(bytes[2]),
                idx(bytes[3]),
                0,
                0,
            ]);
        }
    }

    let num_ops = ops.len();
    let ops_flat: Vec<TokenStream> = ops
        .iter()
        .map(|o| {
            let [a, b, c, d, e, f] = o;
            quote! { [#a, #b, #c, #d, #e, #f] }
        })
        .collect();

    quote! {
        const #ops_name: [[usize; 6]; #num_ops] = [ #( #ops_flat, )* ];
        let mut #var = super::common::eval_memory_expr(evals, linearization_challenges,
            permutation_argument_additive_part, &#ops_name, j);
    }
}

pub fn generate_layer_compute_claim<MW: FieldWrapper>(
    layer: &GKRLayerDescription,
    layer_idx: usize,
    output_sorted_addrs: &[GKRAddress],
) -> TokenStream {
    let fn_name = quote::format_ident!("layer_{}_compute_claim", layer_idx);
    let quartic_struct = MW::quartic_struct();

    // Build descriptor array for the generated compute_claim function.
    // Each gate maps to a (kind, output_idx_0, output_idx_1) tuple.
    // kind:
    //   0 = constraint gate (no output), skips one batching slot
    //   1 = single-output gate, accumulates batch * claim[o0] and advances batch
    //   2 = dual-output gate (lookup pair), accumulates two claims and advances batch twice
    let mut descs = Vec::new();
    for gate in layer
        .gates
        .iter()
        .chain(layer.gates_with_external_connections.iter())
    {
        use NoFieldGKRRelation as R;
        match &gate.enforced_relation {
            R::EnforceSingleMaxQuadraticConstraint { .. } => {
                descs.push((0usize, 0usize, 0usize));
            }
            R::EnforceConstraintsMaxQuadratic { .. } => {
                // TODO: remove once all circuits use individual EnforceSingleMaxQuadraticConstraint gates
                unimplemented!(
                    "EnforceConstraintsMaxQuadratic is not supported by the verifier generator"
                );
            }
            R::LinearBaseFieldRelation { output, .. }
            | R::MaxQuadratic { output, .. }
            | R::CopyInBaseField { output, .. }
            | R::CopyInExtensionField { output, .. }
            | R::InitialGrandProductFromCaches { output, .. }
            | R::InitialGrandProductWithoutCaches { output, .. }
            | R::MaterializeGrandProductTermExpression { output, .. }
            | R::TrivialProduct { output, .. }
            | R::MaskIntoIdentityProduct { output, .. }
            | R::UnbalancedGrandProductWithCache { output, .. }
            | R::MaterializeSingleLookupInput { output, .. }
            | R::MaterializedVectorLookupInput { output, .. }
            | R::InitsOrTeardownsInitialPair { output, .. } => {
                descs.push((1, addr_to_idx(output, output_sorted_addrs), 0));
            }
            R::AggregateLookupRationalPair { output, .. }
            | R::LookupPairFromBaseInputs { output, .. }
            | R::LookupPairFromMaterializedBaseInputs { output, .. }
            | R::LookupUnbalancedPairWithMaterializedBaseInputs { output, .. }
            | R::LookupFromMaterializedBaseInputWithSetup { output, .. }
            | R::LookupPairFromVectorInputs { output, .. }
            | R::LookupPairFromMaterializedVectorInputs { output, .. }
            | R::LookupPairFromCachedVectorInputs { output, .. }
            | R::LookupUnbalancedPairWithMaterializedVectorInputs { output, .. }
            | R::LookupUnbalancedPairWithVectorInputs { output, .. }
            | R::LookupWithCachedDensAndSetup { output, .. }
            | R::LookupWithDensAndSetupExpressions { output, .. }
            | R::LookupFromVectorInputWithSetup { output, .. }
            | R::LookupFromMaterializedVectorInputWithSetup { output, .. } => {
                descs.push((
                    2,
                    addr_to_idx(&output[0], output_sorted_addrs),
                    addr_to_idx(&output[1], output_sorted_addrs),
                ));
            }
        }
    }

    let num_descs = descs.len();
    let num_output_addrs = output_sorted_addrs.len();
    let desc_n: Vec<_> = descs.iter().map(|(n, _, _)| *n).collect();
    let desc_o0: Vec<_> = descs.iter().map(|(_, o0, _)| *o0).collect();
    let desc_o1: Vec<_> = descs.iter().map(|(_, _, o1)| *o1).collect();

    quote! {
        #[inline(always)]
        #[allow(unused_variables)]
        unsafe fn #fn_name(
            output_claims: &[#quartic_struct; #num_output_addrs],
            batch_base: #quartic_struct,
        ) -> #quartic_struct {
            const DESCS: [(usize, usize, usize); #num_descs] = [
                #( (#desc_n, #desc_o0, #desc_o1), )*
            ];
            super::common::compute_claim(output_claims, &DESCS, batch_base)
        }
    }
}

// const GT_COPY: usize = 1;
// const GT_PRODUCT: usize = 2; // InitialGrandProductFromCaches, TrivialProduct
// const GT_MASK_PRODUCT: usize = 3;
// const GT_UNBAL_PRODUCT: usize = 4;
// const GT_LOOKUP_PAIR: usize = 5;
// const GT_LOOKUP_SETUP: usize = 6;
// const GT_LOOKUP_UNBAL: usize = 7;
// const GT_AGGREGATE_PAIR: usize = 8;
// const GT_LOOKUP_CACHED_DENS: usize = 9;

fn emit_simple_gate(
    gate: &prover::cs::gkr_compiler::GateArtifacts,
    input_sorted_addrs: &[GKRAddress],
    simple_group: &mut Vec<(SimpleGateType, [usize; 4])>,
) {
    use NoFieldGKRRelation as R;
    let desc = match &gate.enforced_relation {
        R::CopyInBaseField { input, .. } | R::CopyInExtensionField { input, .. } => (
            SimpleGateType::Copy,
            [addr_to_idx(input, input_sorted_addrs), 0, 0, 0],
        ),
        R::InitialGrandProductFromCaches { input, .. } | R::TrivialProduct { input, .. } => (
            SimpleGateType::Product,
            [
                addr_to_idx(&input[0], input_sorted_addrs),
                addr_to_idx(&input[1], input_sorted_addrs),
                0,
                0,
            ],
        ),
        R::MaskIntoIdentityProduct { input, mask, .. } => (
            SimpleGateType::MaskToIdentity,
            [
                addr_to_idx(input, input_sorted_addrs),
                addr_to_idx(mask, input_sorted_addrs),
                0,
                0,
            ],
        ),
        R::UnbalancedGrandProductWithCache { scalar, input, .. } => (
            SimpleGateType::UnbalancedProduct,
            [
                addr_to_idx(scalar, input_sorted_addrs),
                addr_to_idx(input, input_sorted_addrs),
                0,
                0,
            ],
        ),
        R::LookupPairFromMaterializedBaseInputs { input, .. }
        | R::LookupPairFromMaterializedVectorInputs { input, .. }
        | R::LookupPairFromCachedVectorInputs { input, .. } => (
            SimpleGateType::LookupInitialPair,
            [
                addr_to_idx(&input[0], input_sorted_addrs),
                addr_to_idx(&input[1], input_sorted_addrs),
                0,
                0,
            ],
        ),
        R::LookupFromMaterializedBaseInputWithSetup { input, setup, .. }
        | R::LookupFromMaterializedVectorInputWithSetup { input, setup, .. } => (
            SimpleGateType::LookupWithSetup,
            [
                addr_to_idx(input, input_sorted_addrs),
                addr_to_idx(&setup[0], input_sorted_addrs),
                addr_to_idx(&setup[1], input_sorted_addrs),
                0,
            ],
        ),
        R::LookupUnbalancedPairWithMaterializedBaseInputs {
            input, remainder, ..
        }
        | R::LookupUnbalancedPairWithMaterializedVectorInputs {
            input, remainder, ..
        } => (
            SimpleGateType::LookupUnbalanced,
            [
                addr_to_idx(&input[0], input_sorted_addrs),
                addr_to_idx(&input[1], input_sorted_addrs),
                addr_to_idx(remainder, input_sorted_addrs),
                0,
            ],
        ),
        R::AggregateLookupRationalPair { input, .. } => (
            SimpleGateType::LookupAggregatePair,
            [
                addr_to_idx(&input[0][0], input_sorted_addrs),
                addr_to_idx(&input[0][1], input_sorted_addrs),
                addr_to_idx(&input[1][0], input_sorted_addrs),
                addr_to_idx(&input[1][1], input_sorted_addrs),
            ],
        ),
        R::LookupWithCachedDensAndSetup { input, setup, .. } => (
            SimpleGateType::LookupInitialWithCachedDenominators,
            [
                addr_to_idx(&input[0], input_sorted_addrs),
                addr_to_idx(&input[1], input_sorted_addrs),
                addr_to_idx(&setup[0], input_sorted_addrs),
                addr_to_idx(&setup[1], input_sorted_addrs),
            ],
        ),
        _ => unreachable!("emit_simple_gate called with non-simple gate"),
    };
    simple_group.push(desc);
}

fn generate_simple_gate_loop<MW: FieldWrapper>(
    descs: &[(SimpleGateType, [usize; 4])],
) -> TokenStream {
    let field_one = MW::field_one();
    let mul_batch = MW::mul_assign(quote! { current_batch }, quote! { batch_base });

    let mul_contrib = MW::mul_assign(quote! { contrib }, quote! { val });
    let add_acc = MW::add_assign(quote! { acc[j] }, quote! { contrib });

    let mul_c0 = MW::mul_assign(quote! { c0 }, quote! { out0 });
    let mul_c1 = MW::mul_assign(quote! { c1 }, quote! { out1 });
    let add_c0 = MW::add_assign(quote! { acc[j] }, quote! { c0 });
    let add_c1 = MW::add_assign(quote! { acc[j] }, quote! { c1 });

    let mul_ab = MW::mul_assign(quote! { val }, quote! { vb });
    let sub_one = MW::sub_assign_base(quote! { val }, field_one.clone());
    let mul_mask = MW::mul_assign(quote! { val }, quote! { mask_val });
    let add_one = MW::add_assign_base(quote! { val }, field_one);
    let mul_si = MW::mul_assign(quote! { val }, quote! { vi });

    let add_gamma_bg = MW::add_assign(quote! { bg }, quote! { lookup_additive_challenge });
    let add_gamma_dg = MW::add_assign(quote! { dg }, quote! { lookup_additive_challenge });
    let add_bd = MW::add_assign(quote! { num }, quote! { dg });
    let mul_den = MW::mul_assign(quote! { den }, quote! { dg });

    let mul_cb = MW::mul_assign(quote! { cb }, quote! { bg });
    let sub_cb = MW::sub_assign(quote! { num }, quote! { cb });

    let add_gamma_r = MW::add_assign(quote! { r_g }, quote! { lookup_additive_challenge });
    let mul_ar = MW::mul_assign(quote! { num }, quote! { r_g });
    let add_b_unbal = MW::add_assign(quote! { num }, quote! { b_val });
    let mul_br = MW::mul_assign(quote! { den }, quote! { r_g });

    let mul_ad = MW::mul_assign(quote! { num }, quote! { d_val });
    let mul_cb_agg = MW::mul_assign(quote! { cb_tmp }, quote! { b_val });
    let add_cb_agg = MW::add_assign(quote! { num }, quote! { cb_tmp });
    let mul_bd_agg = MW::mul_assign(quote! { den }, quote! { d_val });

    let add_gamma_b_cd = MW::add_assign(quote! { b_cd }, quote! { lookup_additive_challenge });
    let add_gamma_d_cd = MW::add_assign(quote! { d_cd }, quote! { lookup_additive_challenge });
    let mul_ad_cd = MW::mul_assign(quote! { ad_cd }, quote! { d_cd });
    let mul_cb_cd = MW::mul_assign(quote! { cb_cd }, quote! { b_cd });
    let sub_cb_cd = MW::sub_assign(quote! { ad_cd }, quote! { cb_cd });
    let mul_bd_cd = MW::mul_assign(quote! { den }, quote! { d_cd });

    let num_descs = descs.len();
    let desc_gt: Vec<SimpleGateType> = descs.iter().map(|(gt, _)| *gt).collect();
    let desc_i0: Vec<usize> = descs.iter().map(|(_, idx)| idx[0]).collect();
    let desc_i1: Vec<usize> = descs.iter().map(|(_, idx)| idx[1]).collect();
    let desc_i2: Vec<usize> = descs.iter().map(|(_, idx)| idx[2]).collect();
    let desc_i3: Vec<usize> = descs.iter().map(|(_, idx)| idx[3]).collect();

    quote! {
        {
            const SIMPLE_GATES: [(SimpleGateType, [usize; 4]); #num_descs] = [
                #( (#desc_gt, [#desc_i0, #desc_i1, #desc_i2, #desc_i3]), )*
            ];
            let mut _sg = 0;
            while _sg < #num_descs {
                let (gt, idx) = unsafe { *SIMPLE_GATES.get_unchecked(_sg) };
                match gt {
                    SimpleGateType::Copy => {
                        let bc = current_batch;
                        #mul_batch;
                        for j in 0..2 {
                            let val = evals.get_unchecked(idx[0])[j];
                            let mut contrib = bc;
                            #mul_contrib;
                            #add_acc;
                        }
                    }
                    SimpleGateType::Product => {
                        let bc = current_batch;
                        #mul_batch;
                        for j in 0..2 {
                            let mut val = evals.get_unchecked(idx[0])[j];
                            let vb = evals.get_unchecked(idx[1])[j];
                            #mul_ab;
                            let mut contrib = bc;
                            #mul_contrib;
                            #add_acc;
                        }
                    }
                    SimpleGateType::MaskToIdentity => {
                        let bc = current_batch;
                        #mul_batch;
                        for j in 0..2 {
                            let mut val = evals.get_unchecked(idx[0])[j];
                            let mask_val = evals.get_unchecked(idx[1])[j];
                            #sub_one;
                            #mul_mask;
                            #add_one;
                            let mut contrib = bc;
                            #mul_contrib;
                            #add_acc;
                        }
                    }
                    SimpleGateType::UnbalancedProduct => {
                        let bc = current_batch;
                        #mul_batch;
                        for j in 0..2 {
                            let mut val = evals.get_unchecked(idx[0])[j];
                            let vi = evals.get_unchecked(idx[1])[j];
                            #mul_si;
                            let mut contrib = bc;
                            #mul_contrib;
                            #add_acc;
                        }
                    }
                    SimpleGateType::LookupInitialPair => {
                        let bc0 = current_batch;
                        #mul_batch;
                        let bc1 = current_batch;
                        #mul_batch;
                        for j in 0..2 {
                            let mut bg = evals.get_unchecked(idx[0])[j];
                            let mut dg = evals.get_unchecked(idx[1])[j];
                            #add_gamma_bg;
                            #add_gamma_dg;
                            let mut num = bg;
                            #add_bd;
                            let mut den = bg;
                            #mul_den;
                            let out0 = num;
                            let out1 = den;
                            let mut c0 = bc0; #mul_c0; #add_c0;
                            let mut c1 = bc1; #mul_c1; #add_c1;
                        }
                    }
                    SimpleGateType::LookupWithSetup => {
                        let bc0 = current_batch;
                        #mul_batch;
                        let bc1 = current_batch;
                        #mul_batch;
                        for j in 0..2 {
                            let mut bg = evals.get_unchecked(idx[0])[j];
                            let mut dg = evals.get_unchecked(idx[2])[j];
                            let mut cb = evals.get_unchecked(idx[1])[j];
                            #add_gamma_bg;
                            #add_gamma_dg;
                            #mul_cb;
                            let mut num = dg;
                            #sub_cb;
                            let mut den = bg;
                            #mul_den;
                            let out0 = num;
                            let out1 = den;
                            let mut c0 = bc0; #mul_c0; #add_c0;
                            let mut c1 = bc1; #mul_c1; #add_c1;
                        }
                    }
                    SimpleGateType::LookupUnbalanced => {
                        let bc0 = current_batch;
                        #mul_batch;
                        let bc1 = current_batch;
                        #mul_batch;
                        for j in 0..2 {
                            let a_val = evals.get_unchecked(idx[0])[j];
                            let b_val = evals.get_unchecked(idx[1])[j];
                            let mut r_g = evals.get_unchecked(idx[2])[j];
                            #add_gamma_r;
                            let mut num = a_val;
                            #mul_ar;
                            #add_b_unbal;
                            let mut den = b_val;
                            #mul_br;
                            let out0 = num;
                            let out1 = den;
                            let mut c0 = bc0; #mul_c0; #add_c0;
                            let mut c1 = bc1; #mul_c1; #add_c1;
                        }
                    }
                    SimpleGateType::LookupAggregatePair => {
                        let bc0 = current_batch;
                        #mul_batch;
                        let bc1 = current_batch;
                        #mul_batch;
                        for j in 0..2 {
                            let a_val = evals.get_unchecked(idx[0])[j];
                            let b_val = evals.get_unchecked(idx[1])[j];
                            let c_val = evals.get_unchecked(idx[2])[j];
                            let d_val = evals.get_unchecked(idx[3])[j];
                            let mut num = a_val;
                            #mul_ad;
                            let mut cb_tmp = c_val;
                            #mul_cb_agg;
                            #add_cb_agg;
                            let mut den = b_val;
                            #mul_bd_agg;
                            let out0 = num;
                            let out1 = den;
                            let mut c0 = bc0; #mul_c0; #add_c0;
                            let mut c1 = bc1; #mul_c1; #add_c1;
                        }
                    }
                    SimpleGateType::LookupInitialWithCachedDenominators => {
                        let bc0 = current_batch;
                        #mul_batch;
                        let bc1 = current_batch;
                        #mul_batch;
                        for j in 0..2 {
                            let a_val = evals.get_unchecked(idx[0])[j];
                            let mut b_cd = evals.get_unchecked(idx[1])[j];
                            let c_val = evals.get_unchecked(idx[2])[j];
                            let mut d_cd = evals.get_unchecked(idx[3])[j];
                            #add_gamma_b_cd;
                            #add_gamma_d_cd;
                            let mut ad_cd = a_val;
                            #mul_ad_cd;
                            let mut cb_cd = c_val;
                            #mul_cb_cd;
                            #sub_cb_cd;
                            let mut den = b_cd;
                            #mul_bd_cd;
                            let out0 = ad_cd;
                            let out1 = den;
                            let mut c0 = bc0; #mul_c0; #add_c0;
                            let mut c1 = bc1; #mul_c1; #add_c1;
                        }
                    }
                }
                _sg += 1;
            }
        }
    }
}

fn emit_single_output_value<MW: FieldWrapper, F: PrimeField>(
    gate: &prover::cs::gkr_compiler::GateArtifacts,
    input_sorted_addrs: &[GKRAddress],
) -> Option<TokenStream> {
    use NoFieldGKRRelation as R;
    match &gate.enforced_relation {
        R::EnforceSingleMaxQuadraticConstraint { input } => Some(emit_max_quadratic_eval::<F>(
            input,
            "val",
            input_sorted_addrs,
        )),
        R::EnforceConstraintsMaxQuadratic { .. } => {
            unimplemented!(
                "EnforceConstraintsMaxQuadratic is not supported; use individual EnforceSingleMaxQuadraticConstraint gates"
            );
        }
        R::LinearBaseFieldRelation { input, .. } => Some(emit_linear_relation_eval::<MW, F>(
            input,
            "val",
            input_sorted_addrs,
        )),
        R::MaxQuadratic { input, .. } => Some(emit_max_quadratic_eval::<F>(
            input,
            "val",
            input_sorted_addrs,
        )),
        R::MaterializeSingleLookupInput { input, .. } => Some(emit_linear_relation_eval::<MW, F>(
            &input.input,
            "val",
            input_sorted_addrs,
        )),
        R::MaterializedVectorLookupInput { input, .. } => Some(emit_vector_lookup_eval::<MW, F>(
            input,
            "val",
            input_sorted_addrs,
        )),
        R::InitialGrandProductWithoutCaches { input, .. } => {
            let mem_a = emit_memory_expression_eval::<F>(&input[0], "mem_a", input_sorted_addrs);
            let mem_b = emit_memory_expression_eval::<F>(&input[1], "mem_b", input_sorted_addrs);
            let mul_ab = MW::mul_assign(quote! { mem_a }, quote! { mem_b });
            Some(quote! { #mem_a #mem_b #mul_ab; let val = mem_a; })
        }
        R::MaterializeGrandProductTermExpression { input, .. } => Some(
            emit_memory_expression_eval::<F>(input, "val", input_sorted_addrs),
        ),
        _ => None,
    }
}

fn emit_dual_output_for_relation<MW: FieldWrapper, F: PrimeField>(
    body: &mut TokenStream,
    mul_batch: &TokenStream,
    gate: &prover::cs::gkr_compiler::GateArtifacts,
    input_sorted_addrs: &[GKRAddress],
) -> bool {
    use NoFieldGKRRelation as R;

    let standard_lookup_pair =
        |body: &mut TokenStream, comp_a: TokenStream, comp_b: TokenStream| {
            generate_two_output_body::<MW>(
                body,
                mul_batch,
                quote! { #comp_a #comp_b },
                |_, mw_add| {
                    let add_ga = mw_add(quote! { a_val }, quote! { lookup_additive_challenge });
                    let add_gb = mw_add(quote! { b_val }, quote! { lookup_additive_challenge });
                    let add_ab = mw_add(quote! { num }, quote! { b_val });
                    quote! { #add_ga; #add_gb; let mut num = a_val; #add_ab; num }
                },
                |mw_mul, _| {
                    let mul_ab = mw_mul(quote! { den }, quote! { b_val });
                    quote! { let mut den = a_val; #mul_ab; den }
                },
            );
        };

    match &gate.enforced_relation {
        R::LookupPairFromBaseInputs { input, .. } => {
            let comp_a =
                emit_linear_relation_eval::<MW, F>(&input[0].input, "a_val", input_sorted_addrs);
            let comp_b =
                emit_linear_relation_eval::<MW, F>(&input[1].input, "b_val", input_sorted_addrs);
            standard_lookup_pair(body, comp_a, comp_b);
            true
        }
        R::LookupPairFromVectorInputs { input, .. } => {
            let comp_a = emit_vector_lookup_eval::<MW, F>(&input[0], "a_val", input_sorted_addrs);
            let comp_b = emit_vector_lookup_eval::<MW, F>(&input[1], "b_val", input_sorted_addrs);
            standard_lookup_pair(body, comp_a, comp_b);
            true
        }
        R::LookupWithDensAndSetupExpressions { input, setup, .. } => {
            let a_idx = addr_to_idx(&input.0, input_sorted_addrs);
            let c_idx = addr_to_idx(&setup.0, input_sorted_addrs);
            let comp_b = emit_vector_lookup_eval::<MW, F>(&input.1, "b_val", input_sorted_addrs);
            let comp_d = emit_setup_horner_eval::<F>(&setup.1, "d_val", input_sorted_addrs);
            let add_gamma_b =
                MW::add_assign(quote! { b_val }, quote! { lookup_additive_challenge });
            let add_gamma_d =
                MW::add_assign(quote! { d_val }, quote! { lookup_additive_challenge });
            generate_two_output_body::<MW>(
                body,
                mul_batch,
                quote! {
                    let a_val = evals.get_unchecked(#a_idx)[j];
                    let c_val = evals.get_unchecked(#c_idx)[j];
                    #comp_b #add_gamma_b;
                    #comp_d #add_gamma_d;
                },
                |mw_mul, _| {
                    let mul_ad = mw_mul(quote! { num }, quote! { d_val });
                    let mul_cb = mw_mul(quote! { cb_tmp }, quote! { b_val });
                    let sub_cb = MW::sub_assign(quote! { num }, quote! { cb_tmp });
                    quote! {
                        let mut num = a_val; #mul_ad;
                        let mut cb_tmp = c_val; #mul_cb; #sub_cb;
                        num
                    }
                },
                |mw_mul, _| {
                    let mul_bd = mw_mul(quote! { den }, quote! { d_val });
                    quote! { let mut den = b_val; #mul_bd; den }
                },
            );
            true
        }
        R::LookupUnbalancedPairWithVectorInputs {
            input, remainder, ..
        } => {
            let a_idx = addr_to_idx(&input[0], input_sorted_addrs);
            let b_idx = addr_to_idx(&input[1], input_sorted_addrs);
            let comp_c = emit_vector_lookup_eval::<MW, F>(remainder, "c_val", input_sorted_addrs);
            let add_gamma_c =
                MW::add_assign(quote! { c_val }, quote! { lookup_additive_challenge });
            generate_two_output_body::<MW>(
                body,
                mul_batch,
                quote! {
                    let a_val = evals.get_unchecked(#a_idx)[j];
                    let b_val = evals.get_unchecked(#b_idx)[j];
                    #comp_c #add_gamma_c;
                },
                |mw_mul, mw_add| {
                    let mul_ac = mw_mul(quote! { num }, quote! { c_val });
                    let add_b = mw_add(quote! { num }, quote! { b_val });
                    quote! { let mut num = a_val; #mul_ac; #add_b; num }
                },
                |mw_mul, _| {
                    let mul_bc = mw_mul(quote! { den }, quote! { c_val });
                    quote! { let mut den = b_val; #mul_bc; den }
                },
            );
            true
        }
        R::LookupFromVectorInputWithSetup { input, setup, .. } => {
            let comp_a = emit_vector_lookup_eval::<MW, F>(input, "a_val", input_sorted_addrs);
            let c_idx = addr_to_idx(&setup.0, input_sorted_addrs);
            let comp_d = emit_setup_horner_eval::<F>(&setup.1, "d_val", input_sorted_addrs);
            let add_gamma_a =
                MW::add_assign(quote! { a_val }, quote! { lookup_additive_challenge });
            let add_gamma_d =
                MW::add_assign(quote! { d_val }, quote! { lookup_additive_challenge });
            generate_two_output_body::<MW>(
                body,
                mul_batch,
                quote! {
                    #comp_a #add_gamma_a;
                    let c_val = evals.get_unchecked(#c_idx)[j];
                    #comp_d #add_gamma_d;
                },
                |mw_mul, _| {
                    let mul_ca = mw_mul(quote! { cb_tmp }, quote! { a_val });
                    let sub_ca = MW::sub_assign(quote! { num }, quote! { cb_tmp });
                    quote! {
                        let mut num = d_val;
                        let mut cb_tmp = c_val; #mul_ca; #sub_ca;
                        num
                    }
                },
                |mw_mul, _| {
                    let mul_ad = mw_mul(quote! { den }, quote! { d_val });
                    quote! { let mut den = a_val; #mul_ad; den }
                },
            );
            true
        }
        _ => false,
    }
}

fn emit_inits_teardowns<MW: FieldWrapper, F: PrimeField>(
    body: &mut TokenStream,
    mul_batch: &TokenStream,
    gate: &prover::cs::gkr_compiler::GateArtifacts,
    input_sorted_addrs: &[GKRAddress],
) {
    use NoFieldGKRRelation as R;
    let R::InitsOrTeardownsInitialPair {
        timestamp_and_value,
        setup,
        set_idxes,
        ..
    } = &gate.enforced_relation
    else {
        unreachable!()
    };

    let setup_lo_idx = addr_to_idx(&setup[0], input_sorted_addrs);
    let setup_hi_idx = addr_to_idx(&setup[1], input_sorted_addrs);

    let mul_t_base = MW::mul_assign_by_base(quote! { t }, quote! { base });
    let add_result_t = MW::add_assign(quote! { result }, quote! { t });
    let add_result_ram = MW::add_assign_base(quote! { result }, quote! { ram_constant_el });
    let add_addr_set = MW::add_assign_base(quote! { addr_hi }, quote! { set_field });
    let mul_t_addr = MW::mul_assign_by_base(quote! { t }, quote! { addr_hi });

    let mut val_comp = TokenStream::new();

    for (side, set_idx) in ["lhs", "rhs"].iter().zip(set_idxes.iter()) {
        let var = syn::Ident::new(side, proc_macro2::Span::call_site());
        let set_idx_val = *set_idx;

        let ts_val_terms = match timestamp_and_value {
            InitsOrTeardownsTimestampAndValue::Init => {
                quote! {}
            }
            InitsOrTeardownsTimestampAndValue::Teardown {
                lhs_timestamp,
                lhs_value,
                rhs_timestamp,
                rhs_value,
            } => {
                let (ts, value) = if *side == "lhs" {
                    (lhs_timestamp, lhs_value)
                } else {
                    (rhs_timestamp, rhs_value)
                };
                let ts_lo_idx =
                    addr_to_idx(&GKRAddress::BaseLayerMemory(ts[0]), input_sorted_addrs);
                let ts_hi_idx =
                    addr_to_idx(&GKRAddress::BaseLayerMemory(ts[1]), input_sorted_addrs);
                let val_lo_idx =
                    addr_to_idx(&GKRAddress::BaseLayerMemory(value[0]), input_sorted_addrs);
                let val_hi_idx =
                    addr_to_idx(&GKRAddress::BaseLayerMemory(value[1]), input_sorted_addrs);
                quote! {
                    {
                        let mut t = linearization_challenges[#PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                        let base = evals.get_unchecked(#ts_lo_idx)[j];
                        #mul_t_base;
                        #add_result_t;
                    }
                    {
                        let mut t = linearization_challenges[#PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
                        let base = evals.get_unchecked(#ts_hi_idx)[j];
                        #mul_t_base;
                        #add_result_t;
                    }
                    {
                        let mut t = linearization_challenges[#PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                        let base = evals.get_unchecked(#val_lo_idx)[j];
                        #mul_t_base;
                        #add_result_t;
                    }
                    {
                        let mut t = linearization_challenges[#PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                        let base = evals.get_unchecked(#val_hi_idx)[j];
                        #mul_t_base;
                        #add_result_t;
                    }
                }
            }
        };

        let field_struct_local = MW::field_struct();
        let ram_constant = coeff_to_internal_repr::<F>(1) as u32;
        val_comp.extend(quote! {
            let mut #var = {
                let mut result = permutation_argument_additive_part;
                let ram_constant_el = #field_struct_local::from_reduced_raw_repr(#ram_constant);
                #add_result_ram;
                {
                    let mut t = linearization_challenges[#PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                    let base = evals.get_unchecked(#setup_lo_idx)[j];
                    #mul_t_base;
                    #add_result_t;
                }
                {
                    let mut t = linearization_challenges[#PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
                    let mut addr_hi = evals.get_unchecked(#setup_hi_idx)[j];
                    let set_bits = (#set_idx_val as u32) << address_high_bits_shift;
                    if set_bits != 0 {
                        let set_field = #field_struct_local::from_u32_unchecked(set_bits);
                        #add_addr_set;
                    }
                    #mul_t_addr;
                    #add_result_t;
                }
                #ts_val_terms
                result
            };
        });
    }

    let mul_lr = MW::mul_assign(quote! { lhs }, quote! { rhs });
    val_comp.extend(quote! { #mul_lr; let val = lhs; });
    emit_single_output_gate::<MW>(body, mul_batch, val_comp);
}

pub fn generate_layer_final_step_accumulator<MW: FieldWrapper, F: PrimeField>(
    layer: &GKRLayerDescription,
    layer_idx: usize,
    input_sorted_addrs: &[GKRAddress],
) -> TokenStream {
    let fn_name = quote::format_ident!("layer_{}_final_step_accumulator", layer_idx);
    let quartic_zero = MW::quartic_zero();
    let quartic_one = MW::quartic_one();
    let quartic_struct = MW::quartic_struct();
    let mul_batch = MW::mul_assign(quote! { current_batch }, quote! { batch_base });

    let mut body = quote! {
        let mut acc = [#quartic_zero; 2];
        let mut current_batch = #quartic_one;
    };

    let mut simple_group: Vec<(SimpleGateType, [usize; 4])> = Vec::new();

    let gates: Vec<_> = layer
        .gates
        .iter()
        .chain(layer.gates_with_external_connections.iter())
        .collect();

    let flush_simple = |body: &mut TokenStream, group: &mut Vec<(SimpleGateType, [usize; 4])>| {
        if !group.is_empty() {
            body.extend(generate_simple_gate_loop::<MW>(group));
            group.clear();
        }
    };

    for gate in &gates {
        use NoFieldGKRRelation as R;
        match &gate.enforced_relation {
            // Simple gates — batched into a const-array-driven runtime dispatch loop
            R::CopyInBaseField { .. }
            | R::CopyInExtensionField { .. }
            | R::InitialGrandProductFromCaches { .. }
            | R::TrivialProduct { .. }
            | R::MaskIntoIdentityProduct { .. }
            | R::UnbalancedGrandProductWithCache { .. }
            | R::LookupPairFromMaterializedBaseInputs { .. }
            | R::LookupPairFromMaterializedVectorInputs { .. }
            | R::LookupPairFromCachedVectorInputs { .. }
            | R::LookupFromMaterializedBaseInputWithSetup { .. }
            | R::LookupFromMaterializedVectorInputWithSetup { .. }
            | R::LookupUnbalancedPairWithMaterializedBaseInputs { .. }
            | R::LookupUnbalancedPairWithMaterializedVectorInputs { .. }
            | R::AggregateLookupRationalPair { .. }
            | R::LookupWithCachedDensAndSetup { .. } => {
                emit_simple_gate(gate, input_sorted_addrs, &mut simple_group);
            }

            // Single-output gates — each needs expression evaluation
            R::EnforceSingleMaxQuadraticConstraint { .. }
            | R::LinearBaseFieldRelation { .. }
            | R::MaxQuadratic { .. }
            | R::MaterializeSingleLookupInput { .. }
            | R::MaterializedVectorLookupInput { .. }
            | R::InitialGrandProductWithoutCaches { .. }
            | R::MaterializeGrandProductTermExpression { .. } => {
                flush_simple(&mut body, &mut simple_group);
                let val = emit_single_output_value::<MW, F>(gate, input_sorted_addrs)
                    .expect("matched single-output gate must produce value");
                emit_single_output_gate::<MW>(&mut body, &mul_batch, val);
            }

            // Dual-output lookup gates — need numerator/denominator expressions
            R::LookupPairFromBaseInputs { .. }
            | R::LookupPairFromVectorInputs { .. }
            | R::LookupWithDensAndSetupExpressions { .. }
            | R::LookupUnbalancedPairWithVectorInputs { .. }
            | R::LookupFromVectorInputWithSetup { .. } => {
                flush_simple(&mut body, &mut simple_group);
                emit_dual_output_for_relation::<MW, F>(
                    &mut body,
                    &mul_batch,
                    gate,
                    input_sorted_addrs,
                );
            }

            // Init/teardown — unique structure
            R::InitsOrTeardownsInitialPair { .. } => {
                flush_simple(&mut body, &mut simple_group);
                emit_inits_teardowns::<MW, F>(&mut body, &mul_batch, gate, input_sorted_addrs);
            }

            _ => {
                panic!(
                    "Unimplemented relation variant in GKR inlining generator: {:?}",
                    gate.enforced_relation
                );
            }
        }
    }

    if !simple_group.is_empty() {
        body.extend(generate_simple_gate_loop::<MW>(&simple_group));
    }

    body.extend(quote! { acc });

    quote! {
        #[inline(always)]
        #[allow(unused_variables, unused_mut, unused_unsafe)]
        unsafe fn #fn_name(
            evals: &[[#quartic_struct; 2]],
            batch_base: #quartic_struct,
            lookup_additive_challenge: #quartic_struct,
            lookup_alpha: #quartic_struct,
            linearization_challenges: &[#quartic_struct],
            permutation_argument_additive_part: #quartic_struct,
            address_high_bits_shift: u32,
        ) -> [#quartic_struct; 2] {
            #body
        }
    }
}

fn generate_two_output_body<MW: FieldWrapper>(
    body: &mut TokenStream,
    mul_batch: &TokenStream,
    setup_vars: TokenStream,
    gen_num: impl FnOnce(
        fn(TokenStream, TokenStream) -> TokenStream,
        fn(TokenStream, TokenStream) -> TokenStream,
    ) -> TokenStream,
    gen_den: impl FnOnce(
        fn(TokenStream, TokenStream) -> TokenStream,
        fn(TokenStream, TokenStream) -> TokenStream,
    ) -> TokenStream,
) {
    let num_expr = gen_num(MW::mul_assign, MW::add_assign);
    let den_expr = gen_den(MW::mul_assign, MW::add_assign);
    let mul_c0 = MW::mul_assign(quote! { c0 }, quote! { out0 });
    let mul_c1 = MW::mul_assign(quote! { c1 }, quote! { out1 });
    let add_c0 = MW::add_assign(quote! { acc[j] }, quote! { c0 });
    let add_c1 = MW::add_assign(quote! { acc[j] }, quote! { c1 });
    body.extend(quote! {
        {
            let bc0 = current_batch;
            #mul_batch;
            let bc1 = current_batch;
            #mul_batch;
            for j in 0..2 {
                #setup_vars
                let out0 = { #num_expr };
                let out1 = { #den_expr };
                let mut c0 = bc0;
                #mul_c0;
                let mut c1 = bc1;
                #mul_c1;
                #add_c0;
                #add_c1;
            }
        }
    });
}
