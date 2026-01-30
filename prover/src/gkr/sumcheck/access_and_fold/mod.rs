use std::ptr::null_mut;
use std::{collections::BTreeMap, mem::MaybeUninit};

use crate::gkr::sumcheck::evaluation_kernels::BaseFieldFoldedOnceRepresentation;
use crate::gkr::sumcheck::evaluation_kernels::EvaluationFormStorage;
use crate::gkr::sumcheck::evaluation_kernels::EvaluationRepresentation;
use crate::gkr::sumcheck::evaluation_kernels::ExtensionFieldRepresentation;
use crate::gkr::sumcheck::evaluation_kernels::{BaseFieldRepresentation, GKRInputs};
use cs::definitions::GKRAddress;
use field::{Field, FieldExtension, PrimeField};

pub mod input_in_base;
pub mod input_in_extension;

pub use self::input_in_base::*;
pub use self::input_in_extension::*;

#[derive(Default)]
pub struct GKRLayerSource<F: PrimeField, E: FieldExtension<F> + Field> {
    pub layer_idx: usize,
    pub base_field_inputs: BTreeMap<GKRAddress, BaseFieldPoly<F>>,
    pub extension_field_inputs: BTreeMap<GKRAddress, ExtensionFieldPoly<F, E>>,
    pub intermediate_storage_for_folder_base_field_inputs:
        BTreeMap<GKRAddress, (usize, BaseFieldPolyIntermediateFoldingStorage<F, E>)>,
    pub intermediate_storage_for_folder_extension_field_inputs:
        BTreeMap<GKRAddress, (usize, ExtensionFieldPolyIntermediateFoldingStorage<F, E>)>,
}

#[derive(Default)]
pub struct GKRStorage<F: PrimeField, E: FieldExtension<F> + Field> {
    pub layers: Vec<GKRLayerSource<F, E>>,
}

impl<F: PrimeField, E: FieldExtension<F> + Field> GKRStorage<F, E> {
    pub(crate) fn get_base_layer_mem(&self, offset: usize) -> &[F] {
        unsafe {
            debug_assert!(self.layers.len() > 0);
            let layer = self.layers.get_unchecked(0);
            debug_assert!(layer
                .base_field_inputs
                .contains_key(&GKRAddress::BaseLayerMemory(offset)));
            &layer
                .base_field_inputs
                .get(&GKRAddress::BaseLayerMemory(offset))
                .unwrap_unchecked()
                .values[..]
        }
    }

    pub(crate) fn get_base_layer(&self, address: GKRAddress) -> &[F] {
        unsafe {
            debug_assert!(self.layers.len() > 0);
            let layer = self.layers.get_unchecked(0);
            debug_assert!(layer.base_field_inputs.contains_key(&address));
            &layer
                .base_field_inputs
                .get(&address)
                .unwrap_unchecked()
                .values[..]
        }
    }

    pub(crate) fn insert_base_field_at_layer(
        &mut self,
        layer: usize,
        address: GKRAddress,
        value: BaseFieldPoly<F>,
    ) {
        if layer >= self.layers.len() {
            self.layers
                .resize_with(layer + 1, || GKRLayerSource::default());
        }
        let existing = self.layers[layer].base_field_inputs.insert(address, value);
        assert!(
            existing.is_none(),
            "trying to insert another value for layer {}, address {:?}",
            layer,
            address
        );
    }

    pub(crate) fn insert_extension_at_layer(
        &mut self,
        layer: usize,
        address: GKRAddress,
        value: ExtensionFieldPoly<F, E>,
    ) {
        if layer >= self.layers.len() {
            self.layers
                .resize_with(layer + 1, || GKRLayerSource::default());
        }
        let existing = self.layers[layer]
            .extension_field_inputs
            .insert(address, value);
        assert!(
            existing.is_none(),
            "trying to insert another value for layer {}, address {:?}",
            layer,
            address
        );
    }

    pub(crate) fn make_ext_source_for_rounds_two_and_beyond(
        &mut self,
        poly: GKRAddress,
        folding_challenges: &[E],
    ) -> ExtensionFieldPolyContinuingSource<F, E> {
        let layer = match poly {
            GKRAddress::InnerLayer { layer, .. } | GKRAddress::Cached { layer, .. } => layer,
            GKRAddress::BaseLayerMemory(..) | GKRAddress::BaseLayerWitness(..) => 0,
            _ => {
                unreachable!()
            }
        };
        let sumcheck_step = folding_challenges.len();
        if sumcheck_step == 1
            && self.layers[layer]
                .intermediate_storage_for_folder_extension_field_inputs
                .contains_key(&poly)
                == false
        {
            // create intermediate storage
            let p = self.layers[layer]
                .extension_field_inputs
                .get_mut(&poly)
                .expect("must be present");
            let size = p.values.len();
            let mut buffer =
                ExtensionFieldPolyIntermediateFoldingStorage::<F, E>::new_for_extension_poly_size(
                    size,
                );
            let buffer_pointer = buffer.pointer_for_sumcheck_after_one_fold();
            let input_pointer = p.values.as_mut_ptr();
            #[allow(dropping_references)]
            drop(p);
            self.layers[layer]
                .intermediate_storage_for_folder_extension_field_inputs
                .insert(poly, (1, buffer));
            let folding_challenge = *folding_challenges.last().expect("must be present");

            ExtensionFieldPolyContinuingSource {
                previous_layer_start: input_pointer,
                this_layer_start: buffer_pointer,
                this_layer_size: size / 2,
                next_layer_size: size / 4,
                folding_challenge,
                first_access: true,
                _marker: core::marker::PhantomData,
            }
        } else {
            let (last_used_for_layer, buffer) = self.layers[layer]
                .intermediate_storage_for_folder_extension_field_inputs
                .get_mut(&poly)
                .expect("must be present");
            assert!(
                *last_used_for_layer == sumcheck_step || *last_used_for_layer == sumcheck_step - 1
            );
            let (previous_layer_start, this_layer_start) =
                buffer.pointer_for_sumcheck_continuation(sumcheck_step);
            let this_layer_size = buffer.size_after_one_fold >> (sumcheck_step - 2);
            let next_layer_size = this_layer_size / 2;
            #[allow(dropping_references)]
            drop(buffer);
            let folding_challenge = *folding_challenges.last().expect("must be present");
            if *last_used_for_layer == sumcheck_step {
                // we can reuse those values
                ExtensionFieldPolyContinuingSource {
                    previous_layer_start,
                    this_layer_start,
                    this_layer_size,
                    next_layer_size,
                    folding_challenge,
                    first_access: false,
                    _marker: core::marker::PhantomData,
                }
            } else {
                // first access will perform computations
                *last_used_for_layer = sumcheck_step;
                ExtensionFieldPolyContinuingSource {
                    previous_layer_start,
                    this_layer_start,
                    this_layer_size,
                    next_layer_size,
                    folding_challenge,
                    first_access: true,
                    _marker: core::marker::PhantomData,
                }
            }
        }
    }

    pub fn get_for_sumcheck_round_0(
        &mut self,
        inputs: &GKRInputs,
    ) -> FirstSumcheckRoundSelectedStorage<F, E> {
        let mut storage = FirstSumcheckRoundSelectedStorage::default();
        for input in inputs.inputs_in_base.iter() {
            if *input == GKRAddress::placeholder() {
                storage
                    .base_field_inputs
                    .push(<BaseFieldPolySource<F> as EvaluationFormStorage<
                        F,
                        E,
                        BaseFieldRepresentation<F>,
                    >>::dummy());
            } else {
                let layer = match *input {
                    GKRAddress::OptimizedOut(..) => {
                        unreachable!()
                    }
                    GKRAddress::Cached { layer, .. }   => {
                        assert_eq!(layer, 0);
                        0
                    }
                    GKRAddress::InnerLayer { layer, .. } => {
                        layer
                    },
                    GKRAddress::BaseLayerMemory(..) | GKRAddress::BaseLayerWitness(..) | GKRAddress::Setup(..) => {
                        0
                    }
                };
                let Some(source) = self.layers[layer].base_field_inputs.get(input) else {
                    panic!("Polynomial with address {:?} is missing from input sources for base field polys", input);
                };
                let accessor = source.accessor();
                storage.base_field_inputs.push(accessor);
            }
        }
        for input in inputs.inputs_in_extension.iter() {
            if *input == GKRAddress::placeholder() {
                storage
                    .extension_field_inputs
                    .push(ExtensionFieldPolyInitialSource::dummy());
            } else {
                let layer = match *input {
                    GKRAddress::OptimizedOut(..) => {
                        unreachable!()
                    }
                    GKRAddress::Cached { layer, .. }   => {
                        assert_eq!(layer, 0);
                        0
                    }
                    GKRAddress::InnerLayer { layer, .. } => {
                        layer
                    },
                    GKRAddress::BaseLayerMemory(..) | GKRAddress::BaseLayerWitness(..) | GKRAddress::Setup(..) => {
                        0
                    }
                };
                let Some(source) = self.layers[layer].extension_field_inputs.get(input) else {
                    panic!("Polynomial with address {:?} is missing from input sources for extension field polys", input);
                };
                let accessor = source.accessor();
                storage.extension_field_inputs.push(accessor);
            }
        }

        for output in inputs.outputs_in_extension.iter() {
            if *output == GKRAddress::placeholder() {
                storage
                    .extension_field_outputs
                    .push(ExtensionFieldPolyInitialSource::dummy());
            } else {
                let layer = match *output {
                    GKRAddress::OptimizedOut(..)
                    | GKRAddress::BaseLayerMemory(..)
                    | GKRAddress::BaseLayerWitness(..) | GKRAddress::Setup(..) => {
                        unreachable!()
                    }
                    GKRAddress::Cached { layer, .. } => {
                        unreachable!()
                        // assert_eq!(layer, 1);
                        // 1
                    }
                    GKRAddress::InnerLayer { layer, .. } => {
                        layer
                    }
                };
                let Some(source) = self.layers[layer].extension_field_inputs.get(output) else {
                    panic!("Polynomial with address {:?} is missing from output sources for extension field polys", output);
                };
                let accessor = source.accessor();
                storage.extension_field_outputs.push(accessor);
            }
        }

        // dbg!(&storage);

        storage
    }

    pub fn get_for_sumcheck_round_1(
        &mut self,
        inputs: &GKRInputs,
        folding_challenges: &[E],
    ) -> SecondSumcheckRoundSelectedStorage<F, E> {
        let mut storage = SecondSumcheckRoundSelectedStorage::default();
        for input in inputs.inputs_in_base.iter() {
            todo!()
        }
        for input in inputs.inputs_in_extension.iter() {
            if *input == GKRAddress::placeholder() {
                storage
                    .extension_field_inputs
                    .push(ExtensionFieldPolyContinuingSource::dummy());
            } else {
                let source =
                    self.make_ext_source_for_rounds_two_and_beyond(*input, folding_challenges);
                storage.extension_field_inputs.push(source);
            }
        }

        storage
    }

    pub fn get_for_sumcheck_round_2(
        &mut self,
        inputs: &GKRInputs,
        folding_challenges: &[E],
    ) -> ThirdSumcheckRoundSelectedStorage<F, E> {
        todo!()
    }

    pub fn get_for_sumcheck_round_3_and_beyond(
        &mut self,
        inputs: &GKRInputs,
        folding_challenges: &[E],
    ) -> ThirdSumcheckRoundSelectedStorage<F, E> {
        todo!()
    }
}

#[derive(Default, Debug)]
pub struct FirstSumcheckRoundSelectedStorage<F: PrimeField, E: FieldExtension<F> + Field> {
    pub base_field_inputs: Vec<BaseFieldPolySource<F>>,
    pub extension_field_inputs: Vec<ExtensionFieldPolyInitialSource<F, E>>,
    pub base_field_outputs: Vec<BaseFieldPolySource<F>>,
    pub extension_field_outputs: Vec<ExtensionFieldPolyInitialSource<F, E>>,
    _marker: core::marker::PhantomData<E>,
}

#[derive(Default, Debug)]
pub struct SecondSumcheckRoundSelectedStorage<F: PrimeField, E: FieldExtension<F> + Field> {
    pub base_field_inputs: Vec<BaseFieldPolySourceAfterOneFolding<F, E>>,
    pub extension_field_inputs: Vec<ExtensionFieldPolyContinuingSource<F, E>>,
}

impl<F: PrimeField, E: FieldExtension<F> + Field> SecondSumcheckRoundSelectedStorage<F, E> {
    pub fn collect_last_values(
        &self,
        inputs: &GKRInputs,
        last_evaluations: &mut BTreeMap<GKRAddress, [E; 2]>,
    ) {
        for input in inputs.inputs_in_base.iter() {
            todo!()
        }
        let mut idx = 0;
        for input in inputs.inputs_in_extension.iter() {
            if *input == GKRAddress::placeholder() {
                // nothing
            } else {
                if last_evaluations.contains_key(input) == false {
                    let current_values = self.extension_field_inputs[idx].current_values();
                    assert_eq!(current_values.len(), 2);
                    // let [f0, f1] = self.extension_field_inputs[idx].get_f0_and_f1(0);

                    last_evaluations.insert(*input, [current_values[0], current_values[1]]);
                }
            }
            idx += 1;
        }
    }
}

#[derive(Default, Debug)]
pub struct ThirdSumcheckRoundSelectedStorage<F: PrimeField, E: FieldExtension<F> + Field> {
    pub base_field_inputs: Vec<BaseFieldPolySourceAfterTwoFoldings<F, E>>,
    pub extension_field_inputs: Vec<ExtensionFieldPolyContinuingSource<F, E>>,
}

#[derive(Default, Debug)]
pub struct FourthAndBeyondSumcheckRoundSelectedStorage<F: PrimeField, E: FieldExtension<F> + Field>
{
    pub base_field_inputs: Vec<()>,
    pub extension_field_inputs: Vec<()>,
    pub base_field_outputs: Vec<()>,
    pub extension_field_outputs: Vec<()>,
    _marker: core::marker::PhantomData<(F, E)>,
}
