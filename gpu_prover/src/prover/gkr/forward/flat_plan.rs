use std::collections::BTreeMap;

use era_cudart::result::CudaResult;

use super::super::setup::GpuGKRForwardSetup;
use super::super::stage1::GpuGKRStage1Output;
use super::super::{GpuBaseFieldSourceKind, GpuGKRStorage};
use super::cache_relation::build_memory_expr;
use super::kernels::*;
use super::{
    materialize_inits_and_teardowns_initial_pair_into, single_column_lookup_mapping_ptr,
    vector_lookup_mapping_ptr,
};
use crate::ops::simple::{Add, BinaryOp, Mul, SetByVal};
use crate::primitives::context::ProverContext;
use crate::primitives::field::BF;
use crate::upstream::{
    high_bits_offset_for_inits_and_teardowns, Field, FieldExtension, GKRAddress,
    GKRCircuitArtifact, GKRExternalChallenges, NoFieldGKRCacheRelation, NoFieldGKRRelation,
};

struct FlatBuilder<E> {
    descs: Vec<Box<GpuFlatForwardStaticDesc<E>>>,
    src_map: std::collections::HashMap<usize, u16>,
}

impl<E: Field> FlatBuilder<E> {
    fn new() -> Self {
        Self {
            descs: vec![Box::new(GpuFlatForwardStaticDesc::default())],
            src_map: std::collections::HashMap::new(),
        }
    }

    fn desc(&self) -> &GpuFlatForwardStaticDesc<E> {
        self.descs
            .last()
            .expect("flat forward builder always has a descriptor")
    }

    fn desc_mut(&mut self) -> &mut GpuFlatForwardStaticDesc<E> {
        self.descs
            .last_mut()
            .expect("flat forward builder always has a descriptor")
    }

    fn rotate(&mut self) {
        if !super::kernels::flat_desc_has_work(self.desc()) {
            self.src_map.clear();
            return;
        }
        self.descs
            .push(Box::new(GpuFlatForwardStaticDesc::default()));
        self.src_map.clear();
    }

    fn ensure_sources_capacity(&mut self, additional: usize) {
        if self.desc().num_sources as usize + additional > FLAT_FWD_MAX_SOURCES {
            self.rotate();
        }
    }

    fn ensure_category_capacity(&mut self, count: u32) {
        if count as usize >= FLAT_FWD_MAX_PER_CATEGORY {
            self.rotate();
        }
    }

    fn add_src(&mut self, ptr: *const u8) -> u16 {
        let key = ptr as usize;
        if let Some(&idx) = self.src_map.get(&key) {
            return idx;
        }
        self.ensure_sources_capacity(1);
        let idx = self.desc().num_sources;
        assert!(
            (idx as usize) < FLAT_FWD_MAX_SOURCES,
            "flat forward: source table overflow ({idx} >= {FLAT_FWD_MAX_SOURCES})"
        );
        self.desc_mut().sources[idx as usize] = ptr;
        self.desc_mut().num_sources = idx + 1;
        let idx = idx as u16;
        self.src_map.insert(key, idx);
        idx
    }

    fn into_descs(self) -> Vec<Box<GpuFlatForwardStaticDesc<E>>> {
        self.descs
            .into_iter()
            .filter(|desc| super::kernels::flat_desc_has_work(desc))
            .collect()
    }
}

/// Low-3-bits-tagged null pointer encoding for virtual base sources; mirrors
/// `flat_fwd_load_bf` in native/prover/gkr/forward/flat.cuh.
fn encode_virtual_source(kind: GpuBaseFieldSourceKind) -> *const u8 {
    (kind as usize) as *const u8
}

pub(super) fn build_flat_forward_plan<E>(
    layer_idx: usize,
    gates: &[cs::gkr_compiler::GateArtifacts],
    gates_with_external_connections: &[cs::gkr_compiler::GateArtifacts],
    stage1: &GpuGKRStage1Output,
    forward_setup: &GpuGKRForwardSetup<E>,
    decoder_predicate_address: Option<GKRAddress>,
    scratch_space_mapping: &BTreeMap<GKRAddress, usize>,
    storage: &mut GpuGKRStorage<BF, E>,
    external_challenges: &GKRExternalChallenges<BF, E>,
    trace_len: usize,
    context: &ProverContext,
) -> CudaResult<FlatForwardPlan<E>>
where
    E: Field + FieldExtension<BF> + crate::prover::gkr::GpuKernels + SetByVal,
    Add: BinaryOp<E, E, E>,
    Mul: BinaryOp<BF, E, E>,
    Mul: BinaryOp<E, E, E>,
{
    let expected_output_layer = layer_idx + 1;

    let mut builder = FlatBuilder::new();

    let mut computed_extension_outputs = Vec::new();
    let mut aliased_base_outputs = Vec::new();
    let mut aliased_extension_outputs = Vec::new();

    for gate in gates.iter().chain(gates_with_external_connections.iter()) {
        assert_eq!(gate.output_layer, expected_output_layer);
        match &gate.enforced_relation {
            NoFieldGKRRelation::CopyInBaseField { input, output }
            | NoFieldGKRRelation::CopyInExtensionField { input, output } => {
                if let Some(source) = storage.try_get_base_poly(*input) {
                    aliased_base_outputs.push((*output, source.clone_shared()));
                } else {
                    aliased_extension_outputs
                        .push((*output, storage.get_ext_poly(*input).clone_shared()));
                }
            }
            NoFieldGKRRelation::InitialGrandProductFromCaches { input, output }
            | NoFieldGKRRelation::TrivialProduct { input, output } => {
                let lhs = storage.get_ext_poly(input[0]).as_ptr();
                let rhs = storage.get_ext_poly(input[1]).as_ptr();
                let dst_view =
                    storage.allocate_ext_view(expected_output_layer, *output, context)?;
                let dst_ptr = dst_view.as_mut_ptr();
                computed_extension_outputs.push((*output, dst_view));
                builder.ensure_category_capacity(builder.desc().num_products);
                builder.ensure_sources_capacity(2);
                let src_a = builder.add_src(lhs as *const u8);
                let src_b = builder.add_src(rhs as *const u8);
                let i = builder.desc_mut().num_products as usize;
                assert!(
                    i < FLAT_FWD_MAX_PER_CATEGORY,
                    "flat forward: products overflow"
                );
                builder.desc_mut().products[i] = GpuFlatFwdProductEntry {
                    src_a,
                    src_b,
                    dst: dst_ptr,
                };
                builder.desc_mut().num_products = (i + 1) as u32;
            }
            NoFieldGKRRelation::MaskIntoIdentityProduct {
                input,
                mask,
                output,
            } => {
                let input_ptr = storage.get_ext_poly(*input).as_ptr();
                let mask_ptr = storage.get_base_layer(*mask).as_ptr();
                let dst_view =
                    storage.allocate_ext_view(expected_output_layer, *output, context)?;
                let dst_ptr = dst_view.as_mut_ptr();
                computed_extension_outputs.push((*output, dst_view));
                builder.ensure_category_capacity(builder.desc().num_masks);
                builder.ensure_sources_capacity(2);
                let src_mask = builder.add_src(mask_ptr as *const u8);
                let src_input = builder.add_src(input_ptr as *const u8);
                let i = builder.desc_mut().num_masks as usize;
                assert!(
                    i < FLAT_FWD_MAX_PER_CATEGORY,
                    "flat forward: masks overflow"
                );
                builder.desc_mut().masks[i] = GpuFlatFwdMaskEntry {
                    src_mask,
                    src_input,
                    dst: dst_ptr,
                };
                builder.desc_mut().num_masks = (i + 1) as u32;
            }
            NoFieldGKRRelation::AggregateLookupRationalPair { input, output } => {
                let [a, b] = input[0].map(|addr| storage.get_ext_poly(addr).as_ptr());
                let [c, d] = input[1].map(|addr| storage.get_ext_poly(addr).as_ptr());
                let num_view =
                    storage.allocate_ext_view(expected_output_layer, output[0], context)?;
                let den_view =
                    storage.allocate_ext_view(expected_output_layer, output[1], context)?;
                let num_ptr = num_view.as_mut_ptr();
                let den_ptr = den_view.as_mut_ptr();
                computed_extension_outputs.push((output[0], num_view));
                computed_extension_outputs.push((output[1], den_view));
                builder.ensure_category_capacity(builder.desc().num_lookup4s);
                builder.ensure_sources_capacity(4);
                let src_a = builder.add_src(a as *const u8);
                let src_b = builder.add_src(b as *const u8);
                let src_c = builder.add_src(c as *const u8);
                let src_d = builder.add_src(d as *const u8);
                let i = builder.desc_mut().num_lookup4s as usize;
                assert!(
                    i < FLAT_FWD_MAX_PER_CATEGORY,
                    "flat forward: lookup4s overflow"
                );
                builder.desc_mut().lookup4s[i] = GpuFlatFwdLookup4Entry {
                    src_a,
                    src_b,
                    src_c,
                    src_d,
                    num: num_ptr,
                    den: den_ptr,
                };
                builder.desc_mut().num_lookup4s = (i + 1) as u32;
            }
            NoFieldGKRRelation::LookupWithCachedDensAndSetup {
                input,
                setup,
                output,
            } => {
                let a = storage.get_base_layer(input[0]).as_ptr();
                let b = storage.get_ext_poly(input[1]).as_ptr();
                let c = storage.get_base_layer(setup[0]).as_ptr();
                let d = storage.get_ext_poly(setup[1]).as_ptr();
                let num_view =
                    storage.allocate_ext_view(expected_output_layer, output[0], context)?;
                let den_view =
                    storage.allocate_ext_view(expected_output_layer, output[1], context)?;
                let num_ptr = num_view.as_mut_ptr();
                let den_ptr = den_view.as_mut_ptr();
                computed_extension_outputs.push((output[0], num_view));
                computed_extension_outputs.push((output[1], den_view));
                builder.ensure_category_capacity(builder.desc().num_cached_denses);
                builder.ensure_sources_capacity(4);
                let src_a = builder.add_src(a as *const u8);
                let src_b = builder.add_src(b as *const u8);
                let src_c = builder.add_src(c as *const u8);
                let src_d = builder.add_src(d as *const u8);
                let i = builder.desc_mut().num_cached_denses as usize;
                assert!(
                    i < FLAT_FWD_MAX_PER_CATEGORY,
                    "flat forward: cached_denses overflow"
                );
                builder.desc_mut().cached_denses[i] = GpuFlatFwdCachedDensEntry {
                    src_a,
                    src_b,
                    src_c,
                    src_d,
                    num: num_ptr,
                    den: den_ptr,
                };
                builder.desc_mut().num_cached_denses = (i + 1) as u32;
            }
            NoFieldGKRRelation::LookupPairFromMaterializedBaseInputs { input, output } => {
                let lhs = storage.get_base_layer(input[0]).as_ptr();
                let rhs = storage.get_base_layer(input[1]).as_ptr();
                let num_view =
                    storage.allocate_ext_view(expected_output_layer, output[0], context)?;
                let den_view =
                    storage.allocate_ext_view(expected_output_layer, output[1], context)?;
                let num_ptr = num_view.as_mut_ptr();
                let den_ptr = den_view.as_mut_ptr();
                computed_extension_outputs.push((output[0], num_view));
                computed_extension_outputs.push((output[1], den_view));
                builder.ensure_category_capacity(builder.desc().num_bf_pairs);
                builder.ensure_sources_capacity(2);
                let src_b = builder.add_src(lhs as *const u8);
                let src_d = builder.add_src(rhs as *const u8);
                let i = builder.desc_mut().num_bf_pairs as usize;
                assert!(
                    i < FLAT_FWD_MAX_PER_CATEGORY,
                    "flat forward: bf_pairs overflow"
                );
                builder.desc_mut().bf_pairs[i] = GpuFlatFwdBfPairEntry {
                    src_b,
                    src_d,
                    num: num_ptr,
                    den: den_ptr,
                };
                builder.desc_mut().num_bf_pairs = (i + 1) as u32;
            }
            NoFieldGKRRelation::LookupPairFromMaterializedVectorInputs { input, output }
            | NoFieldGKRRelation::LookupPairFromCachedVectorInputs { input, output } => {
                let lhs = storage.get_ext_poly(input[0]).as_ptr();
                let rhs = storage.get_ext_poly(input[1]).as_ptr();
                let num_view =
                    storage.allocate_ext_view(expected_output_layer, output[0], context)?;
                let den_view =
                    storage.allocate_ext_view(expected_output_layer, output[1], context)?;
                let num_ptr = num_view.as_mut_ptr();
                let den_ptr = den_view.as_mut_ptr();
                computed_extension_outputs.push((output[0], num_view));
                computed_extension_outputs.push((output[1], den_view));
                builder.ensure_category_capacity(builder.desc().num_e4_pairs);
                builder.ensure_sources_capacity(2);
                let src_b = builder.add_src(lhs as *const u8);
                let src_d = builder.add_src(rhs as *const u8);
                let i = builder.desc_mut().num_e4_pairs as usize;
                assert!(
                    i < FLAT_FWD_MAX_PER_CATEGORY,
                    "flat forward: e4_pairs overflow"
                );
                builder.desc_mut().e4_pairs[i] = GpuFlatFwdE4PairEntry {
                    src_b,
                    src_d,
                    num: num_ptr,
                    den: den_ptr,
                };
                builder.desc_mut().num_e4_pairs = (i + 1) as u32;
            }
            NoFieldGKRRelation::LookupFromMaterializedBaseInputWithSetup {
                input,
                setup,
                output,
            } => {
                let b = storage.get_base_layer(*input).as_ptr();
                let c = storage.get_base_layer(setup[0]).as_ptr();
                let d_ptr: *const u8 =
                    if let Some(kind) = GpuBaseFieldSourceKind::from_address(setup[1]) {
                        encode_virtual_source(kind)
                    } else {
                        storage.get_base_layer(setup[1]).as_ptr() as *const u8
                    };
                let num_view =
                    storage.allocate_ext_view(expected_output_layer, output[0], context)?;
                let den_view =
                    storage.allocate_ext_view(expected_output_layer, output[1], context)?;
                let num_ptr = num_view.as_mut_ptr();
                let den_ptr = den_view.as_mut_ptr();
                computed_extension_outputs.push((output[0], num_view));
                computed_extension_outputs.push((output[1], den_view));
                builder.ensure_category_capacity(builder.desc().num_bf_minus_mults);
                builder.ensure_sources_capacity(3);
                let src_b = builder.add_src(b as *const u8);
                let src_c = builder.add_src(c as *const u8);
                let src_d = builder.add_src(d_ptr);
                let i = builder.desc_mut().num_bf_minus_mults as usize;
                assert!(
                    i < FLAT_FWD_MAX_PER_CATEGORY,
                    "flat forward: bf_minus_mults overflow"
                );
                builder.desc_mut().bf_minus_mults[i] = GpuFlatFwdBfMinusMultEntry {
                    src_b,
                    src_c,
                    src_d,
                    _pad: 0,
                    num: num_ptr,
                    den: den_ptr,
                };
                builder.desc_mut().num_bf_minus_mults = (i + 1) as u32;
            }
            NoFieldGKRRelation::LookupFromMaterializedVectorInputWithSetup {
                input,
                setup,
                output,
            } => {
                let b = storage.get_ext_poly(*input).as_ptr();
                let c = storage.get_base_layer(setup[0]).as_ptr();
                let d = storage.get_ext_poly(setup[1]).as_ptr();
                let num_view =
                    storage.allocate_ext_view(expected_output_layer, output[0], context)?;
                let den_view =
                    storage.allocate_ext_view(expected_output_layer, output[1], context)?;
                let num_ptr = num_view.as_mut_ptr();
                let den_ptr = den_view.as_mut_ptr();
                computed_extension_outputs.push((output[0], num_view));
                computed_extension_outputs.push((output[1], den_view));
                builder.ensure_category_capacity(builder.desc().num_e4_minus_mults);
                builder.ensure_sources_capacity(3);
                let src_b = builder.add_src(b as *const u8);
                let src_c = builder.add_src(c as *const u8);
                let src_d = builder.add_src(d as *const u8);
                let i = builder.desc_mut().num_e4_minus_mults as usize;
                assert!(
                    i < FLAT_FWD_MAX_PER_CATEGORY,
                    "flat forward: e4_minus_mults overflow"
                );
                builder.desc_mut().e4_minus_mults[i] = GpuFlatFwdE4MinusMultEntry {
                    src_b,
                    src_c,
                    src_d,
                    _pad: 0,
                    num: num_ptr,
                    den: den_ptr,
                };
                builder.desc_mut().num_e4_minus_mults = (i + 1) as u32;
            }
            NoFieldGKRRelation::LookupUnbalancedPairWithMaterializedBaseInputs {
                input,
                remainder,
                output,
            } => {
                let [a, b] = input.map(|addr| storage.get_ext_poly(addr).as_ptr());
                let remainder = storage.get_base_layer(*remainder).as_ptr();
                let num_view =
                    storage.allocate_ext_view(expected_output_layer, output[0], context)?;
                let den_view =
                    storage.allocate_ext_view(expected_output_layer, output[1], context)?;
                let num_ptr = num_view.as_mut_ptr();
                let den_ptr = den_view.as_mut_ptr();
                computed_extension_outputs.push((output[0], num_view));
                computed_extension_outputs.push((output[1], den_view));
                builder.ensure_category_capacity(builder.desc().num_bf_unbalanceds);
                builder.ensure_sources_capacity(3);
                let src_a = builder.add_src(a as *const u8);
                let src_b = builder.add_src(b as *const u8);
                let src_d = builder.add_src(remainder as *const u8);
                let i = builder.desc_mut().num_bf_unbalanceds as usize;
                assert!(
                    i < FLAT_FWD_MAX_PER_CATEGORY,
                    "flat forward: bf_unbalanceds overflow"
                );
                builder.desc_mut().bf_unbalanceds[i] = GpuFlatFwdBfUnbalancedEntry {
                    src_a,
                    src_b,
                    src_d,
                    _pad: 0,
                    num: num_ptr,
                    den: den_ptr,
                };
                builder.desc_mut().num_bf_unbalanceds = (i + 1) as u32;
            }
            NoFieldGKRRelation::LookupUnbalancedPairWithMaterializedVectorInputs {
                input,
                remainder,
                output,
            } => {
                let [a, b] = input.map(|addr| storage.get_ext_poly(addr).as_ptr());
                let remainder = storage.get_ext_poly(*remainder).as_ptr();
                let num_view =
                    storage.allocate_ext_view(expected_output_layer, output[0], context)?;
                let den_view =
                    storage.allocate_ext_view(expected_output_layer, output[1], context)?;
                let num_ptr = num_view.as_mut_ptr();
                let den_ptr = den_view.as_mut_ptr();
                computed_extension_outputs.push((output[0], num_view));
                computed_extension_outputs.push((output[1], den_view));
                builder.ensure_category_capacity(builder.desc().num_e4_unbalanceds);
                builder.ensure_sources_capacity(3);
                let src_a = builder.add_src(a as *const u8);
                let src_b = builder.add_src(b as *const u8);
                let src_d = builder.add_src(remainder as *const u8);
                let i = builder.desc_mut().num_e4_unbalanceds as usize;
                assert!(
                    i < FLAT_FWD_MAX_PER_CATEGORY,
                    "flat forward: e4_unbalanceds overflow"
                );
                builder.desc_mut().e4_unbalanceds[i] = GpuFlatFwdE4UnbalancedEntry {
                    src_a,
                    src_b,
                    src_d,
                    _pad: 0,
                    num: num_ptr,
                    den: den_ptr,
                };
                builder.desc_mut().num_e4_unbalanceds = (i + 1) as u32;
            }
            NoFieldGKRRelation::LookupPairFromBaseInputs {
                input,
                output,
                range_check_width,
            } => {
                builder.ensure_category_capacity(builder.desc().num_mapped_bf_pairs);
                let mapping_b =
                    single_column_lookup_mapping_ptr(stage1, &input[0], *range_check_width);
                let mapping_d =
                    single_column_lookup_mapping_ptr(stage1, &input[1], *range_check_width);
                let num_view =
                    storage.allocate_ext_view(expected_output_layer, output[0], context)?;
                let den_view =
                    storage.allocate_ext_view(expected_output_layer, output[1], context)?;
                let num_ptr = num_view.as_mut_ptr();
                let den_ptr = den_view.as_mut_ptr();
                computed_extension_outputs.push((output[0], num_view));
                computed_extension_outputs.push((output[1], den_view));
                let i = builder.desc().num_mapped_bf_pairs as usize;
                builder.desc_mut().mapped_bf_pairs[i] = GpuFlatFwdMappedBfPairEntry {
                    mapping_b,
                    mapping_d,
                    num: num_ptr,
                    den: den_ptr,
                };
                builder.desc_mut().num_mapped_bf_pairs = (i + 1) as u32;
            }
            NoFieldGKRRelation::LookupPairFromVectorInputs { input, output } => {
                builder.ensure_category_capacity(builder.desc().num_mapped_e4_pairs);
                let mapping_b = vector_lookup_mapping_ptr(stage1, &input[0]);
                let mapping_d = vector_lookup_mapping_ptr(stage1, &input[1]);
                let generic_lookup = forward_setup.generic_lookup().as_ptr();
                let num_view =
                    storage.allocate_ext_view(expected_output_layer, output[0], context)?;
                let den_view =
                    storage.allocate_ext_view(expected_output_layer, output[1], context)?;
                let num_ptr = num_view.as_mut_ptr();
                let den_ptr = den_view.as_mut_ptr();
                computed_extension_outputs.push((output[0], num_view));
                computed_extension_outputs.push((output[1], den_view));
                let i = builder.desc().num_mapped_e4_pairs as usize;
                builder.desc_mut().mapped_e4_pairs[i] = GpuFlatFwdMappedE4PairEntry {
                    mapping_b,
                    mapping_d,
                    generic_lookup,
                    num: num_ptr,
                    den: den_ptr,
                };
                builder.desc_mut().num_mapped_e4_pairs = (i + 1) as u32;
            }
            NoFieldGKRRelation::LookupWithDensAndSetupExpressions {
                input,
                setup,
                output,
            } => {
                assert_eq!(
                    Some(input.0),
                    decoder_predicate_address,
                    "GPU no-cache decoder lookup expects the decoder predicate input"
                );
                builder.ensure_category_capacity(builder.desc().num_mapped_cached_denses);
                builder.ensure_sources_capacity(2);
                let mapping_b = vector_lookup_mapping_ptr(stage1, &input.1);
                let generic_lookup = forward_setup.generic_lookup().as_ptr();
                let decoder_mask = storage.get_base_layer(input.0).as_ptr();
                let decoder_fill_value = forward_setup.decoder_lookup_fill_value_device().as_ptr();
                let a = storage.get_base_layer(input.0).as_ptr();
                let c = storage.get_base_layer(setup.0).as_ptr();
                let num_view =
                    storage.allocate_ext_view(expected_output_layer, output[0], context)?;
                let den_view =
                    storage.allocate_ext_view(expected_output_layer, output[1], context)?;
                let num_ptr = num_view.as_mut_ptr();
                let den_ptr = den_view.as_mut_ptr();
                computed_extension_outputs.push((output[0], num_view));
                computed_extension_outputs.push((output[1], den_view));
                let src_a = builder.add_src(a as *const u8);
                let src_c = builder.add_src(c as *const u8);
                let i = builder.desc().num_mapped_cached_denses as usize;
                builder.desc_mut().mapped_cached_denses[i] = GpuFlatFwdMappedCachedDensEntry {
                    mapping_b,
                    generic_lookup,
                    decoder_mask,
                    decoder_fill_value,
                    src_a,
                    src_c,
                    generic_lookup_len: forward_setup.generic_lookup_len() as u32,
                    _pad: 0,
                    num: num_ptr,
                    den: den_ptr,
                };
                builder.desc_mut().num_mapped_cached_denses = (i + 1) as u32;
            }
            NoFieldGKRRelation::LookupFromVectorInputWithSetup {
                input,
                setup,
                output,
            } => {
                builder.ensure_category_capacity(builder.desc().num_mapped_e4_minus_mults);
                builder.ensure_sources_capacity(1);
                let mapping_b = vector_lookup_mapping_ptr(stage1, input);
                let generic_lookup = forward_setup.generic_lookup().as_ptr();
                let c = storage.get_base_layer(setup.0).as_ptr();
                let num_view =
                    storage.allocate_ext_view(expected_output_layer, output[0], context)?;
                let den_view =
                    storage.allocate_ext_view(expected_output_layer, output[1], context)?;
                let num_ptr = num_view.as_mut_ptr();
                let den_ptr = den_view.as_mut_ptr();
                computed_extension_outputs.push((output[0], num_view));
                computed_extension_outputs.push((output[1], den_view));
                let src_c = builder.add_src(c as *const u8);
                let i = builder.desc().num_mapped_e4_minus_mults as usize;
                builder.desc_mut().mapped_e4_minus_mults[i] = GpuFlatFwdMappedE4MinusMultEntry {
                    mapping_b,
                    generic_lookup,
                    src_c,
                    _pad: 0,
                    generic_lookup_len: forward_setup.generic_lookup_len() as u32,
                    num: num_ptr,
                    den: den_ptr,
                };
                builder.desc_mut().num_mapped_e4_minus_mults = (i + 1) as u32;
            }
            NoFieldGKRRelation::LookupUnbalancedPairWithVectorInputs {
                input,
                remainder,
                output,
            } => {
                builder.ensure_category_capacity(builder.desc().num_mapped_e4_unbalanceds);
                builder.ensure_sources_capacity(2);
                let [a, b] = input.map(|addr| storage.get_ext_poly(addr).as_ptr());
                let mapping_d = vector_lookup_mapping_ptr(stage1, remainder);
                let generic_lookup = forward_setup.generic_lookup().as_ptr();
                let num_view =
                    storage.allocate_ext_view(expected_output_layer, output[0], context)?;
                let den_view =
                    storage.allocate_ext_view(expected_output_layer, output[1], context)?;
                let num_ptr = num_view.as_mut_ptr();
                let den_ptr = den_view.as_mut_ptr();
                computed_extension_outputs.push((output[0], num_view));
                computed_extension_outputs.push((output[1], den_view));
                let src_a = builder.add_src(a as *const u8);
                let src_b = builder.add_src(b as *const u8);
                let i = builder.desc().num_mapped_e4_unbalanceds as usize;
                builder.desc_mut().mapped_e4_unbalanceds[i] = GpuFlatFwdMappedE4UnbalancedEntry {
                    src_a,
                    src_b,
                    _pad: 0,
                    mapping_d,
                    generic_lookup,
                    num: num_ptr,
                    den: den_ptr,
                };
                builder.desc_mut().num_mapped_e4_unbalanceds = (i + 1) as u32;
            }
            NoFieldGKRRelation::InitialGrandProductWithoutCaches { input, output } => {
                builder.ensure_category_capacity(builder.desc().num_memory_products);
                let dst_view =
                    storage.allocate_ext_view(expected_output_layer, *output, context)?;
                let dst_ptr = dst_view.as_mut_ptr();
                computed_extension_outputs.push((*output, dst_view));
                let lhs = build_memory_expr(&input[0], storage, external_challenges);
                let rhs = build_memory_expr(&input[1], storage, external_challenges);
                let i = builder.desc().num_memory_products as usize;
                builder.desc_mut().memory_products[i] = GpuFlatFwdMemoryProductEntry {
                    lhs,
                    rhs,
                    dst: dst_ptr,
                };
                builder.desc_mut().num_memory_products = (i + 1) as u32;
            }
            NoFieldGKRRelation::MaterializeGrandProductTermExpression { input, output } => {
                builder.ensure_category_capacity(builder.desc().num_memory_materializes);
                let dst_view =
                    storage.allocate_ext_view(expected_output_layer, *output, context)?;
                let dst_ptr = dst_view.as_mut_ptr();
                computed_extension_outputs.push((*output, dst_view));
                let expr = build_memory_expr(input, storage, external_challenges);
                let i = builder.desc().num_memory_materializes as usize;
                builder.desc_mut().memory_materializes[i] =
                    GpuFlatFwdMemoryMaterializeEntry { expr, dst: dst_ptr };
                builder.desc_mut().num_memory_materializes = (i + 1) as u32;
            }
            NoFieldGKRRelation::EnforceConstraintsMaxQuadratic { .. } => {}
            NoFieldGKRRelation::MaterializedVectorLookupInput { output, .. } => {
                assert!(
                    storage.try_get_ext_poly(*output).is_some(),
                    "materialized vector lookup output {:?} must be precomputed before forward dispatch",
                    output
                );
            }
            NoFieldGKRRelation::MaterializeSingleLookupInput { output, .. } => {
                assert!(
                    storage.try_get_base_poly(*output).is_some(),
                    "materialized single lookup output {:?} must be precomputed before forward dispatch",
                    output
                );
            }
            NoFieldGKRRelation::LinearBaseFieldRelation { output, .. } => {
                assert!(
                    storage.try_get_base_poly(*output).is_some(),
                    "materialized linear base output {:?} must be precomputed before forward dispatch",
                    output
                );
            }
            NoFieldGKRRelation::MaxQuadratic { output, .. }
                if matches!(*output, GKRAddress::ScratchSpace(_))
                    || scratch_space_mapping.contains_key(output)
                    || storage.try_get_base_poly(*output).is_some() => {}
            NoFieldGKRRelation::EnforceSingleMaxQuadraticConstraint { .. } => {}
            NoFieldGKRRelation::InitsOrTeardownsInitialPair {
                timestamp_and_value,
                setup,
                output,
                set_idxes,
            } => {
                let dst_view =
                    storage.allocate_ext_view(expected_output_layer, *output, context)?;
                materialize_inits_and_teardowns_initial_pair_into(
                    storage,
                    &dst_view,
                    timestamp_and_value,
                    *setup,
                    set_idxes.map(|idx| idx as u32),
                    high_bits_offset_for_inits_and_teardowns::<2>(trace_len),
                    external_challenges,
                    trace_len,
                    context,
                )?;
                computed_extension_outputs.push((*output, dst_view));
            }
            NoFieldGKRRelation::MaxQuadratic { .. }
            | NoFieldGKRRelation::UnbalancedGrandProductWithCache { .. } => {
                unimplemented!(
                    "unsupported GPU forward relation: {:?}",
                    gate.enforced_relation
                )
            }
        }
    }

    Ok(FlatForwardPlan {
        descs: builder.into_descs(),
        computed_extension_outputs,
        aliased_base_outputs,
        aliased_extension_outputs,
    })
}

pub(super) fn commit_flat_forward_plan<E>(
    expected_output_layer: usize,
    storage: &mut GpuGKRStorage<BF, E>,
    plan: FlatForwardPlan<E>,
) {
    let FlatForwardPlan {
        descs: _,
        computed_extension_outputs,
        aliased_base_outputs,
        aliased_extension_outputs,
    } = plan;

    for (address, poly) in computed_extension_outputs {
        storage.insert_extension_at_layer(expected_output_layer, address, poly);
    }
    for (address, poly) in aliased_base_outputs {
        storage.insert_base_field_at_layer(expected_output_layer, address, poly);
    }
    for (address, poly) in aliased_extension_outputs {
        storage.insert_extension_at_layer(expected_output_layer, address, poly);
    }
}

pub(super) fn analyze_forward_lookup_usage(
    compiled_circuit: &GKRCircuitArtifact<BF>,
) -> ForwardLookupUsage {
    let mut usage = ForwardLookupUsage::default();
    for (layer_idx, layer) in compiled_circuit.layers.iter().enumerate() {
        for relation in layer.cached_relations.values() {
            match relation {
                NoFieldGKRCacheRelation::SingleColumnLookup {
                    range_check_width, ..
                } => {
                    if *range_check_width == 16 {
                        usage.last_range_mapping_layer = Some(layer_idx);
                    } else {
                        usage.last_timestamp_mapping_layer = Some(layer_idx);
                    }
                }
                NoFieldGKRCacheRelation::VectorizedLookup(_) => {
                    usage.last_generic_mapping_layer = Some(layer_idx);
                    usage.last_generic_lookup_layer = Some(layer_idx);
                }
                NoFieldGKRCacheRelation::VectorizedLookupSetup(_) => {
                    usage.last_generic_lookup_layer = Some(layer_idx);
                }
                NoFieldGKRCacheRelation::MemoryTuple(_) => {}
            }
        }
        for gate in layer
            .gates
            .iter()
            .chain(layer.gates_with_external_connections.iter())
        {
            match &gate.enforced_relation {
                NoFieldGKRRelation::MaterializedVectorLookupInput { .. }
                | NoFieldGKRRelation::LookupWithDensAndSetupExpressions { .. }
                | NoFieldGKRRelation::LookupPairFromVectorInputs { .. }
                | NoFieldGKRRelation::LookupFromVectorInputWithSetup { .. }
                | NoFieldGKRRelation::LookupUnbalancedPairWithVectorInputs { .. } => {
                    usage.last_generic_mapping_layer = Some(layer_idx);
                    usage.last_generic_lookup_layer = Some(layer_idx);
                }
                NoFieldGKRRelation::LookupPairFromBaseInputs {
                    range_check_width, ..
                } => {
                    if *range_check_width == 16 {
                        usage.last_range_mapping_layer = Some(layer_idx);
                    } else {
                        usage.last_timestamp_mapping_layer = Some(layer_idx);
                    }
                }
                _ => {}
            }
        }
    }
    usage
}

pub(super) fn release_forward_lookup_resources_after_layer<E>(
    layer_idx: usize,
    usage: &ForwardLookupUsage,
    stage1: &mut GpuGKRStage1Output,
    forward_setup: &mut GpuGKRForwardSetup<E>,
) {
    if usage.last_generic_mapping_layer == Some(layer_idx) {
        stage1.lookup_mappings.release_generic_family();
    }
    if usage.last_range_mapping_layer == Some(layer_idx) {
        stage1.lookup_mappings.release_range_check_16();
    }
    if usage.last_timestamp_mapping_layer == Some(layer_idx) {
        stage1.lookup_mappings.release_timestamp();
    }
    if usage.last_generic_lookup_layer == Some(layer_idx) {
        forward_setup.release_generic_lookup();
    }
}

pub(super) fn cache_relation_layer(layer_idx: usize, address: GKRAddress) -> usize {
    let GKRAddress::Cached { layer, .. } = address else {
        panic!(
            "forward cache scheduler expects cached address, got {:?}",
            address
        );
    };
    assert_eq!(
        layer, layer_idx,
        "cached relation address {:?} does not belong to scheduled layer {}",
        address, layer_idx
    );
    layer
}
