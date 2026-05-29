use std::collections::{BTreeMap, BTreeSet};

use ::field::*;
use cs::{
    definitions::GKRAddress,
    gkr_compiler::{GKRCircuitArtifact, GKRLayerDescription, NoFieldGKRRelation},
    utils::slice_to_token_array,
};
use proc_macro2::{Ident, Span, TokenStream};
use quote::quote;

pub mod kernels;

pub(crate) fn serialize_to_file<T: serde::Serialize>(el: &T, filename: &str) {
    let mut dst = std::fs::File::create(filename).unwrap();
    serde_json::to_writer_pretty(&mut dst, el).unwrap();
}

pub(crate) fn deserialize_from_file<T: serde::de::DeserializeOwned>(filename: &str) -> T {
    let src = std::fs::File::open(filename).unwrap();
    serde_json::from_reader(src).unwrap()
}

fn write_and_fmt(path: &str, content: &proc_macro2::TokenStream) {
    use std::io::Write;
    let mut dst = std::fs::File::create(path).unwrap();
    dst.write_all(content.to_string().as_bytes()).unwrap();
    drop(dst);
    std::process::Command::new("rustfmt")
        .arg(path)
        .status()
        .ok();
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SumcheckAddressState {
    pub first_read: bool,
    pub cache_pos: usize,
}

pub fn generate_layer<F: PrimeField, E: FieldExtension<F> + Field>(
    layer_idx: usize,
    layer: &GKRLayerDescription,
) -> TokenStream {
    let mut all_vars_at_layer = BTreeSet::new();
    let mut base_inputs = BTreeSet::new();
    let mut extension_inputs = BTreeSet::new();
    let mut base_outputs = BTreeSet::new();
    let mut extension_outputs = BTreeSet::new();
    let mut num_challenges = 0usize;

    // we do not dump from cached relations, as we will only use outputs
    for gate in layer
        .gates
        .iter()
        .chain(layer.gates_with_external_connections.iter())
    {
        let t = all_vars_at_layer.len();
        gate.enforced_relation.dump_inputs(&mut all_vars_at_layer);
        let diff_total = all_vars_at_layer.len() - t;
        num_challenges += gate.enforced_relation.num_challenges();
        let t = base_inputs.len();
        gate.enforced_relation
            .dump_base_field_inputs(&mut base_inputs);
        let diff_base_field = base_inputs.len() - t;
        let t = extension_inputs.len();
        gate.enforced_relation
            .dump_ext_field_inputs(&mut extension_inputs);
        let diff_ext_field = extension_inputs.len() - t;
        assert_eq!(diff_total, diff_base_field + diff_ext_field, "total number of inputs diverged for {:?}: {} total diff, {} base field inputs, {} ext field inputs", gate, diff_total, diff_base_field, diff_ext_field);
        gate.enforced_relation
            .dump_base_field_outputs(&mut base_outputs);
        gate.enforced_relation
            .dump_ext_field_outputs(&mut extension_outputs);
    }
    let num_inputs = all_vars_at_layer.len();
    let num_base_field_inputs = base_inputs.len();
    let num_ext_field_inputs = extension_inputs.len();
    let num_base_field_outputs = base_outputs.len();
    let num_ext_field_outputs = extension_outputs.len();

    assert_eq!(num_inputs, num_base_field_inputs + num_ext_field_inputs);

    let base_field_scratch_space_size = num_base_field_inputs;
    let ext_field_scratch_space_size = num_ext_field_inputs;

    let mut challenge_idx = 0;

    let mut state = BTreeMap::new();
    let mut initial_round_seq = quote! {};
    let mut initial_round_calls = quote! {};
    let mut round_seq = quote! {};
    let mut round_calls = quote! {};
    for (gate_idx, gate) in layer
        .gates
        .iter()
        .chain(layer.gates_with_external_connections.iter())
        .enumerate()
    {
        let fetch_fn_initial_round_id = Ident::new(
            &format!("fetch_layer_{}_gate_{}_initial_round", layer_idx, gate_idx),
            Span::call_site(),
        );
        let fetch_fn_id = Ident::new(
            &format!("fetch_layer_{}_gate_{}", layer_idx, gate_idx),
            Span::call_site(),
        );
        let compute_fn_initial_round_id = Ident::new(
            &format!(
                "compute_layer_{}_gate_{}_initial_round",
                layer_idx, gate_idx
            ),
            Span::call_site(),
        );
        let compute_fn_id = Ident::new(
            &format!("compute_layer_{}_gate_{}", layer_idx, gate_idx),
            Span::call_site(),
        );
        let [(initial_round_fetch, initial_compute), (fetch, compute)] = generate_gate::<F, E>(
            &gate.enforced_relation,
            gate_idx,
            layer_idx,
            &mut state,
            base_field_scratch_space_size,
            ext_field_scratch_space_size,
            num_base_field_inputs,
            num_ext_field_inputs,
            &base_inputs,
            &extension_inputs,
            &base_outputs,
            &extension_outputs,
            num_challenges,
            &mut challenge_idx,
        );

        initial_round_seq.extend(quote! {
            #initial_round_fetch

            #initial_compute

        });

        initial_round_calls.extend(quote! {
            #fetch_fn_initial_round_id::<F, E, S>(&mut base_field_scratch, &mut ext_field_scratch, all_base_inputs, all_ext_inputs, row_index);
            let [e0, e1] = #compute_fn_initial_round_id::<F, E, S>(
                &base_field_scratch,
                &ext_field_scratch,
                all_base_outputs,
                all_ext_outputs,
                sumcheck_challenges,
                external_challenges,
                lookup_alpha_powers,
                lookup_gamma,
                base_repr_ctx,
                ext_repr_ctx,
                row_index,
            );
            result[0].add_assign(&e0);
            result[1].add_assign(&e1);
        });

        round_seq.extend(quote! {
            #fetch

            #compute

        });

        round_calls.extend(quote! {
            #fetch_fn_id::<F, E, S, EXPLICIT_FORM>(&mut base_field_scratch, &mut ext_field_scratch, all_base_inputs, all_ext_inputs, row_index);
            let [e0, e1] = #compute_fn_id::<F, E, S, EXPLICIT_FORM>(
                &base_field_scratch,
                &ext_field_scratch,
                sumcheck_challenges,
                external_challenges,
                lookup_alpha_powers,
                lookup_gamma,
                base_repr_ctx,
                ext_repr_ctx,
            );
            result[0].add_assign(&e0);
            result[1].add_assign(&e1);
        });
    }

    let initial_round_id = Ident::new(
        &format!("layer_{}_initial_round", layer_idx),
        Span::call_site(),
    );
    let round_id = Ident::new(&format!("layer_{}", layer_idx), Span::call_site());

    quote! {
        #initial_round_seq

        #round_seq

        pub fn #initial_round_id<F: PrimeField, E: FieldExtension<F> + Field, S: SumcheckRoundSource<F, E>, C: GKRExternalChallengesProvider<F, E>>(
            all_base_inputs: &[S::BaseInputAccessor; #num_base_field_inputs],
            all_ext_inputs: &[S::ExtInputAccessor; #num_ext_field_inputs],
            all_base_outputs: &[S::BaseInputAccessor; #num_base_field_outputs],
            all_ext_outputs: &[S::ExtInputAccessor; #num_ext_field_outputs],
            sumcheck_challenges: &[E; #num_challenges],
            external_challenges: &C,
            lookup_alpha_powers: &[E],
            lookup_gamma: &E,
            base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
            ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
            eq_poly_precomputed: &[E],
            row_range: core::ops::Range<usize>,
            row_index: usize,
        ) -> [E; 2] {
            let mut base_field_scratch: [_; #base_field_scratch_space_size] = std::array::from_fn(|_| S::BaseFieldInput::zero());
            let mut ext_field_scratch: [_; #ext_field_scratch_space_size] = std::array::from_fn(|_| S::ExtFieldInput::zero());

            let mut accumulated = [E::ZERO; 2];

            for row_index in row_range {
                let mut result = [E::ZERO; 2];
                #initial_round_calls

                let eq = eq_poly_precomputed[row_index];
                result[0].mul_assign(&eq);
                result[1].mul_assign(&eq);

                accumulated[0].add_assign(&result[0]);
                accumulated[1].add_assign(&result[1]);
            }

            accumulated
        }

        pub fn #round_id<F: PrimeField, E: FieldExtension<F> + Field, S: SumcheckRoundSource<F, E>, C: GKRExternalChallengesProvider<F, E>, const EXPLICIT_FORM: bool>(
            all_base_inputs: &[S::BaseInputAccessor; #num_base_field_inputs],
            all_ext_inputs: &[S::ExtInputAccessor; #num_ext_field_inputs],
            sumcheck_challenges: &[E; #num_challenges],
            external_challenges: &C,
            lookup_alpha_powers: &[E],
            lookup_gamma: &E,
            base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
            ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
            eq_poly_precomputed: &[E],
            row_range: core::ops::Range<usize>,
        ) -> [E; 2] {
            let mut base_field_scratch: [_; #base_field_scratch_space_size] = std::array::from_fn(|_| [S::BaseFieldInput::zero(); 2]);
            let mut ext_field_scratch: [_; #ext_field_scratch_space_size] = std::array::from_fn(|_| [S::ExtFieldInput::zero(); 2]);
            let mut accumulated = [E::ZERO; 2];

            for row_index in row_range {
                let mut result = [E::ZERO; 2];
                #round_calls

                let eq = eq_poly_precomputed[row_index];
                result[0].mul_assign(&eq);
                result[1].mul_assign(&eq);

                accumulated[0].add_assign(&result[0]);
                accumulated[1].add_assign(&result[1]);
            }

            accumulated
        }
    }
}

fn generate_gate<F: PrimeField, E: FieldExtension<F> + Field>(
    relation: &NoFieldGKRRelation,
    gate_idx: usize,
    layer_idx: usize,
    pos_state: &mut BTreeMap<GKRAddress, SumcheckAddressState>,
    base_field_scratch_space_size: usize,
    ext_field_scratch_space_size: usize,
    num_base_field_inputs: usize,
    num_ext_field_inputs: usize,
    all_base_inputs: &BTreeSet<GKRAddress>,
    all_ext_inputs: &BTreeSet<GKRAddress>,
    all_base_outputs: &BTreeSet<GKRAddress>,
    all_ext_outputs: &BTreeSet<GKRAddress>,
    num_challenges: usize,
    challenge_idx: &mut usize,
) -> [(TokenStream, TokenStream); 2] {
    let mut base_inputs = BTreeSet::new();
    let mut extension_inputs = BTreeSet::new();
    relation.dump_base_field_inputs(&mut base_inputs);
    relation.dump_ext_field_inputs(&mut extension_inputs);

    let base_field_mapping_size = base_inputs.len();
    let ext_field_mapping_size = extension_inputs.len();

    let num_required_challenges = relation.num_challenges();
    let mut challenges = vec![];
    for _ in 0..num_required_challenges {
        challenges.push(*challenge_idx);
        *challenge_idx += 1;
    }

    let mut base_field_inputs_to_cache_pos = BTreeMap::new();
    let mut ext_field_inputs_to_cache_pos = BTreeMap::new();

    let mut fetch_seq_initial_round = quote! {};
    let mut fetch_seq = quote! {};
    for input in base_inputs.iter() {
        let all_inputs_idx = all_base_inputs
            .iter()
            .position(|el| *el == *input)
            .expect("pos");
        let var_state = pos_state.entry(*input).or_insert(SumcheckAddressState {
            first_read: true,
            cache_pos: all_inputs_idx,
        });
        let assume_folded = var_state.first_read == false;
        var_state.first_read = false;
        let cache_pos = var_state.cache_pos;

        base_field_inputs_to_cache_pos.insert(*input, cache_pos);

        if assume_folded == false {
            fetch_seq_initial_round.extend(
                quote! {
                    base_field_scratch[#cache_pos] = all_base_inputs[#all_inputs_idx].get_f1_minus_f0_only::<#assume_folded>(row_index);
                }
            );
            fetch_seq.extend(
                quote! {
                    base_field_scratch[#cache_pos] = all_base_inputs[#all_inputs_idx].get_two_points::<#assume_folded, EXPLICIT_FORM>(row_index);
                }
            );
        }
    }
    for input in extension_inputs.iter() {
        let all_inputs_idx = all_ext_inputs
            .iter()
            .position(|el| *el == *input)
            .expect("pos");
        let var_state = pos_state.entry(*input).or_insert(SumcheckAddressState {
            first_read: true,
            cache_pos: all_inputs_idx,
        });
        let assume_folded = var_state.first_read == false;
        var_state.first_read = false;
        let cache_pos = var_state.cache_pos;

        ext_field_inputs_to_cache_pos.insert(*input, cache_pos);

        if assume_folded == false {
            fetch_seq_initial_round.extend(
                quote! {
                    ext_field_scratch[#cache_pos] = all_ext_inputs[#all_inputs_idx].get_f1_minus_f0_only::<#assume_folded>(row_index);
                }
            );
            fetch_seq.extend(
                quote! {
                    ext_field_scratch[#cache_pos] = all_ext_inputs[#all_inputs_idx].get_two_points::<#assume_folded, EXPLICIT_FORM>(row_index);
                }
            );
        }
    }

    let fetch_fn_initial_round_id = Ident::new(
        &format!("fetch_layer_{}_gate_{}_initial_round", layer_idx, gate_idx),
        Span::call_site(),
    );
    let fetch_fn_id = Ident::new(
        &format!("fetch_layer_{}_gate_{}", layer_idx, gate_idx),
        Span::call_site(),
    );

    let fetch_fn_initial_round = quote! {
        #[inline(always)]
        pub fn #fetch_fn_initial_round_id<F: PrimeField, E: FieldExtension<F> + Field, S: SumcheckRoundSource<F, E>>(
            base_field_scratch: &mut [S::BaseFieldInput; #base_field_scratch_space_size],
            ext_field_scratch: &mut [S::ExtFieldInput; #ext_field_scratch_space_size],
            all_base_inputs: &[S::BaseInputAccessor; #num_base_field_inputs],
            all_ext_inputs: &[S::ExtInputAccessor; #num_ext_field_inputs],
            row_index: usize,
        ) {
            #fetch_seq_initial_round
        }
    };

    let fetch_fn = quote! {
        #[inline(always)]
        pub fn #fetch_fn_id<F: PrimeField, E: FieldExtension<F> + Field, S: SumcheckRoundSource<F, E>, const EXPLICIT_FORM: bool>(
            base_field_scratch: &mut [[S::BaseFieldInput; 2]; #base_field_scratch_space_size],
            ext_field_scratch: &mut [[S::ExtFieldInput; 2]; #ext_field_scratch_space_size],
            all_base_inputs: &[S::BaseInputAccessor; #num_base_field_inputs],
            all_ext_inputs: &[S::ExtInputAccessor; #num_ext_field_inputs],
            row_index: usize,
        ) {
            #fetch_seq
        }
    };

    let (compute_fn_initial_round, compute_fn) = kernels::generate_compute_fns_for_relation::<F, E>(
        relation,
        gate_idx,
        layer_idx,
        num_challenges,
        base_field_scratch_space_size,
        ext_field_scratch_space_size,
        all_base_outputs,
        all_ext_outputs,
        pos_state,
        challenges,
    );

    [
        (fetch_fn_initial_round, compute_fn_initial_round),
        (fetch_fn, compute_fn),
    ]
}

#[test]
fn test_generation() {
    use ::field::baby_bear::base::BabyBearField;
    use ::field::baby_bear::ext4::BabyBearExt4;

    let circuit: GKRCircuitArtifact<BabyBearField> = deserialize_from_file(
        "../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_no_caches_gkr.json",
    );

    let layer_idx = 0;
    let layer = &circuit.layers[layer_idx];
    let generated = generate_layer::<BabyBearField, BabyBearExt4>(layer_idx, layer);
    write_and_fmt("generated.rs", &generated);
}
