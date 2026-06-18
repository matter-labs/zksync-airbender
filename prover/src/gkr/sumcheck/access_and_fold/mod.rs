use std::ptr::null_mut;
use std::sync::Arc;
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
mod layer_sources;

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

    pub(crate) fn try_get_base_poly(&self, address: GKRAddress) -> Option<&[F]> {
        match address {
            GKRAddress::InnerLayer { layer, .. } | GKRAddress::Cached { layer, .. } => {
                let source = &self.layers.get(layer)?;
                source
                    .base_field_inputs
                    .get(&address)
                    .map(|el| &el.values[..])
            }
            GKRAddress::BaseLayerMemory(..)
            | GKRAddress::BaseLayerWitness(..)
            | GKRAddress::Setup(..)
            | GKRAddress::VirtualSetup(..) => {
                let source = &self.layers.get(0)?;
                source
                    .base_field_inputs
                    .get(&address)
                    .map(|el| &el.values[..])
            }
            a @ _ => {
                unreachable!("trying to get poly for address {:?}", a);
            }
        }
    }

    pub(crate) fn try_get_base_poly_arc_cloned(
        &self,
        address: GKRAddress,
    ) -> Option<BaseFieldPoly<F>> {
        match address {
            GKRAddress::InnerLayer { layer, .. } | GKRAddress::Cached { layer, .. } => {
                let source = self.layers.get(layer)?;
                source
                    .base_field_inputs
                    .get(&address)
                    .map(|el| el.arc_clone())
            }
            GKRAddress::BaseLayerMemory(..)
            | GKRAddress::BaseLayerWitness(..)
            | GKRAddress::Setup(..)
            | GKRAddress::VirtualSetup(..) => {
                let source = self.layers.get(0)?;
                source
                    .base_field_inputs
                    .get(&address)
                    .map(|el| el.arc_clone())
            }
            a @ _ => {
                unreachable!("trying to get poly for address {:?}", a);
            }
        }
    }

    pub(crate) fn try_get_ext_poly(&self, address: GKRAddress) -> Option<&[E]> {
        match address {
            GKRAddress::InnerLayer { layer, .. } | GKRAddress::Cached { layer, .. } => {
                let source = self.layers.get(layer)?;
                source
                    .extension_field_inputs
                    .get(&address)
                    .map(|el| &el.values[..])
            }
            GKRAddress::BaseLayerMemory(..)
            | GKRAddress::BaseLayerWitness(..)
            | GKRAddress::Setup(..)
            | GKRAddress::VirtualSetup(..) => {
                unreachable!("base layer or setup is only in base field");
            }
            a @ _ => {
                unreachable!("trying to gey poly for address {:?}", a);
            }
        }
    }

    pub(crate) fn try_get_ext_poly_arc_cloned(
        &self,
        address: GKRAddress,
    ) -> Option<ExtensionFieldPoly<F, E>> {
        match address {
            GKRAddress::InnerLayer { layer, .. } | GKRAddress::Cached { layer, .. } => {
                let source = self.layers.get(layer)?;
                source
                    .extension_field_inputs
                    .get(&address)
                    .map(|el| el.arc_clone())
            }
            GKRAddress::BaseLayerMemory(..)
            | GKRAddress::BaseLayerWitness(..)
            | GKRAddress::Setup(..)
            | GKRAddress::VirtualSetup(..) => {
                unreachable!("base layer or setup is only in base field");
            }
            a @ _ => {
                unreachable!("trying to gey poly for address {:?}", a);
            }
        }
    }

    pub(crate) fn purge_up_to_layer(&mut self, layer: usize) {
        self.layers.truncate(layer + 1);
    }

    #[track_caller]
    pub(crate) fn get_ext_poly(&self, address: GKRAddress) -> &[E] {
        match address {
            GKRAddress::InnerLayer { layer, .. } => {
                let source = &self.layers[layer];
                &source
                    .extension_field_inputs
                    .get(&address)
                    .expect("must exist")
                    .values[..]
            }
            _ => {
                todo!()
            }
        }
    }

    #[track_caller]
    pub(crate) fn insert_base_field_at_layer(
        &mut self,
        layer: usize,
        address: GKRAddress,
        value: BaseFieldPoly<F>,
    ) {
        // println!(
        //     "Adding base field poly at address {:?} at {:?}",
        //     address,
        //     core::panic::Location::caller()
        // );
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

    #[track_caller]
    pub(crate) fn insert_extension_at_layer(
        &mut self,
        layer: usize,
        address: GKRAddress,
        value: ExtensionFieldPoly<F, E>,
    ) {
        // println!("Adding extension field poly at address {:?}", address);
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

    #[track_caller]
    pub(crate) fn make_base_source_for_round_1(
        &mut self,
        poly: GKRAddress,
        folding_challenges: &[E],
    ) -> BaseFieldPolySourceAfterOneFolding<F, E> {
        assert_eq!(folding_challenges.len(), 1);

        let layer = match poly {
            GKRAddress::InnerLayer { layer, .. } | GKRAddress::Cached { layer, .. } => layer,
            GKRAddress::BaseLayerMemory(..)
            | GKRAddress::BaseLayerWitness(..)
            | GKRAddress::Setup(..)
            | GKRAddress::VirtualSetup(..) => 0,
            GKRAddress::ScratchSpace(..) => {
                unreachable!()
            }
        };
        let (base_poly_len, base_poly_ptr) = {
            let poly = self.layers[layer]
                .base_field_inputs
                .get(&poly)
                .expect("must exist");
            let base_poly_ptr = poly.values.as_ptr();
            let base_poly_len = poly.values.len();

            (base_poly_len, base_poly_ptr)
        };

        let challenge = folding_challenges[0];
        let mut challenge_squared = challenge;
        challenge_squared.square();

        BaseFieldPolySourceAfterOneFolding {
            base_layer_half_size: base_poly_len / 2,
            next_layer_size: base_poly_len / 4,
            base_input_start: base_poly_ptr,
            first_folding_challenge_and_squared: (challenge, challenge_squared),
        }
    }

    #[track_caller]
    pub(crate) fn make_base_source_for_round_2(
        &mut self,
        poly: GKRAddress,
        folding_challenges: &[E],
    ) -> BaseFieldPolySourceAfterTwoFoldings<F, E> {
        assert_eq!(folding_challenges.len(), 2);

        let layer = match poly {
            GKRAddress::InnerLayer { layer, .. } | GKRAddress::Cached { layer, .. } => layer,
            GKRAddress::BaseLayerMemory(..)
            | GKRAddress::BaseLayerWitness(..)
            | GKRAddress::Setup(..)
            | GKRAddress::VirtualSetup(..) => 0,
            GKRAddress::ScratchSpace(..) => {
                unreachable!()
            }
        };
        let sumcheck_step = folding_challenges.len();
        let (base_poly_len, base_poly_ptr) = {
            let poly = self.layers[layer]
                .base_field_inputs
                .get(&poly)
                .expect("must exist");
            let base_poly_ptr = poly.values.as_ptr();
            let base_poly_len = poly.values.len();

            (base_poly_len, base_poly_ptr)
        };

        let first_folding_challenge = folding_challenges[0];
        let second_folding_challenge = folding_challenges[1];

        if self.layers[layer]
            .intermediate_storage_for_folder_base_field_inputs
            .contains_key(&poly)
            == false
        {
            // create intermediate storage
            let buffer = BaseFieldPolyIntermediateFoldingStorage::<F, E>::new_for_base_poly_size(
                base_poly_len,
            );
            self.layers[layer]
                .intermediate_storage_for_folder_base_field_inputs
                .insert(poly, (1, buffer)); // formally - in the past
        }

        let (last_used_for_layer, buffer) = self.layers[layer]
            .intermediate_storage_for_folder_base_field_inputs
            .get_mut(&poly)
            .expect("must be present");
        assert!(*last_used_for_layer == sumcheck_step || *last_used_for_layer == sumcheck_step - 1);
        let this_layer_start = buffer.initial_pointer();
        #[allow(dropping_references)]
        drop(buffer);
        let mut combined_challenges = first_folding_challenge;
        combined_challenges.mul_assign(&second_folding_challenge);

        if *last_used_for_layer == sumcheck_step {
            // we can reuse those values
            BaseFieldPolySourceAfterTwoFoldings {
                base_input_start: base_poly_ptr,
                this_layer_cache_start: this_layer_start,
                base_layer_half_size: base_poly_len / 2,
                base_quarter_size: base_poly_len / 4,
                next_layer_size: base_poly_len / 8,
                first_folding_challenge,
                second_folding_challenge,
                combined_challenges,
                first_access: false,
            }
        } else {
            // first access will perform computations
            *last_used_for_layer = sumcheck_step;
            BaseFieldPolySourceAfterTwoFoldings {
                base_input_start: base_poly_ptr,
                this_layer_cache_start: this_layer_start,
                base_layer_half_size: base_poly_len / 2,
                base_quarter_size: base_poly_len / 4,
                next_layer_size: base_poly_len / 8,
                first_folding_challenge,
                second_folding_challenge,
                combined_challenges,
                first_access: true,
            }
        }
    }

    #[track_caller]
    pub(crate) fn make_base_source_for_rounds_3_and_beyond(
        &mut self,
        poly: GKRAddress,
        folding_challenges: &[E],
    ) -> ExtensionFieldPolyContinuingSource<F, E> {
        assert!(folding_challenges.len() >= 3);

        let layer = match poly {
            GKRAddress::InnerLayer { layer, .. } | GKRAddress::Cached { layer, .. } => layer,
            GKRAddress::BaseLayerMemory(..)
            | GKRAddress::BaseLayerWitness(..)
            | GKRAddress::Setup(..)
            | GKRAddress::VirtualSetup(..) => 0,
            GKRAddress::ScratchSpace(..) => {
                unreachable!()
            }
        };
        let sumcheck_step = folding_challenges.len();
        let (last_used_for_layer, buffer) = self.layers[layer]
            .intermediate_storage_for_folder_base_field_inputs
            .get_mut(&poly)
            .expect("must be present");
        assert!(*last_used_for_layer == sumcheck_step || *last_used_for_layer == sumcheck_step - 1);
        let (previous_layer_start, this_layer_start) =
            buffer.pointers_for_sumcheck_accessor_step(sumcheck_step);
        let this_layer_size = buffer.size_after_two_folds >> (sumcheck_step - 2);
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

    #[track_caller]
    pub(crate) fn make_ext_source_for_rounds_1_and_beyond(
        &mut self,
        poly: GKRAddress,
        folding_challenges: &[E],
    ) -> ExtensionFieldPolyContinuingSource<F, E> {
        assert!(folding_challenges.len() >= 1);
        let layer = match poly {
            GKRAddress::InnerLayer { layer, .. } | GKRAddress::Cached { layer, .. } => layer,
            GKRAddress::BaseLayerMemory(..) | GKRAddress::BaseLayerWitness(..) => 0,
            GKRAddress::Setup(..) | GKRAddress::VirtualSetup(..) | GKRAddress::ScratchSpace(..) => {
                unreachable!()
            }
        };
        let sumcheck_step = folding_challenges.len();
        if sumcheck_step == 1 {
            if self.layers[layer]
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
                let input_pointer = p.values.as_ptr();
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
                // maybe it was created before, just reuse it
                let p = self.layers[layer]
                    .extension_field_inputs
                    .get(&poly)
                    .expect("must be present");
                let size = p.values.len();
                let input_pointer = p.values.as_ptr();

                let (last_used_at_layer, buffer) = self.layers[layer]
                    .intermediate_storage_for_folder_extension_field_inputs
                    .get_mut(&poly)
                    .expect("must be present");
                assert_eq!(*last_used_at_layer, 1);

                let buffer_pointer = buffer.pointer_for_sumcheck_after_one_fold();

                let folding_challenge = *folding_challenges.last().expect("must be present");

                ExtensionFieldPolyContinuingSource {
                    previous_layer_start: input_pointer,
                    this_layer_start: buffer_pointer,
                    this_layer_size: size / 2,
                    next_layer_size: size / 4,
                    folding_challenge,
                    first_access: false,
                    _marker: core::marker::PhantomData,
                }
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

    #[track_caller]
    pub fn get_for_sumcheck_round_0(
        &mut self,
        inputs: &GKRInputs,
    ) -> SumcheckRound0SelectedStorage<F, E> {
        let mut storage = SumcheckRound0SelectedStorage::default();
        for input in inputs.inputs_in_base.iter() {
            if *input == GKRAddress::placeholder() {
                storage
                    .base_field_inputs
                    .push(BaseFieldPolySource::<F>::empty());
            } else {
                let layer = match *input {
                    GKRAddress::ScratchSpace(..) => {
                        unreachable!()
                    }
                    GKRAddress::Cached { layer, .. } => layer,
                    GKRAddress::InnerLayer { layer, .. } => layer,
                    GKRAddress::BaseLayerMemory(..)
                    | GKRAddress::BaseLayerWitness(..)
                    | GKRAddress::Setup(..)
                    | GKRAddress::VirtualSetup(..) => 0,
                };
                let Some(source) = self.layers[layer].base_field_inputs.get(input) else {
                    panic!("Polynomial with address {:?} is missing from input sources for base field polys for evaluating caller {:?}", input, core::panic::Location::caller());
                };
                let accessor = source.accessor();
                storage.base_field_inputs.push(accessor);
            }
        }
        for input in inputs.inputs_in_extension.iter() {
            if *input == GKRAddress::placeholder() {
                storage
                    .extension_field_inputs
                    .push(ExtensionFieldPolyInitialSource::empty());
            } else {
                let layer = match *input {
                    GKRAddress::ScratchSpace(..) => {
                        unreachable!()
                    }
                    GKRAddress::Cached { layer, .. } => layer,
                    GKRAddress::InnerLayer { layer, .. } => layer,
                    GKRAddress::BaseLayerMemory(..)
                    | GKRAddress::BaseLayerWitness(..)
                    | GKRAddress::Setup(..)
                    | GKRAddress::VirtualSetup(..) => 0,
                };
                let Some(source) = self.layers[layer].extension_field_inputs.get(input) else {
                    panic!("Polynomial with address {:?} is missing from input sources for extension field polys for evaluating caller {:?}", input, core::panic::Location::caller());
                };
                let accessor = source.accessor();
                storage.extension_field_inputs.push(accessor);
            }
        }
        for output in inputs.outputs_in_base.iter() {
            if *output == GKRAddress::placeholder() {
                storage
                    .base_field_outputs
                    .push(BaseFieldPolySource::empty());
            } else {
                let layer = match *output {
                    GKRAddress::ScratchSpace(..)
                    | GKRAddress::BaseLayerMemory(..)
                    | GKRAddress::BaseLayerWitness(..)
                    | GKRAddress::Setup(..)
                    | GKRAddress::VirtualSetup(..) => {
                        unreachable!()
                    }
                    GKRAddress::Cached { .. } => {
                        unreachable!()
                    }
                    GKRAddress::InnerLayer { layer, .. } => layer,
                };
                let Some(source) = self.layers[layer].base_field_inputs.get(output) else {
                    panic!("Polynomial with address {:?} is missing from output sources for base field polys for evaluating caller {:?}", output, core::panic::Location::caller());
                };
                let accessor = source.accessor();
                storage.base_field_outputs.push(accessor);
            }
        }
        for output in inputs.outputs_in_extension.iter() {
            if *output == GKRAddress::placeholder() {
                storage
                    .extension_field_outputs
                    .push(ExtensionFieldPolyInitialSource::empty());
            } else {
                let layer = match *output {
                    GKRAddress::ScratchSpace(..)
                    | GKRAddress::BaseLayerMemory(..)
                    | GKRAddress::BaseLayerWitness(..)
                    | GKRAddress::Setup(..)
                    | GKRAddress::VirtualSetup(..) => {
                        unreachable!()
                    }
                    GKRAddress::Cached { .. } => {
                        unreachable!()
                    }
                    GKRAddress::InnerLayer { layer, .. } => layer,
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

    #[track_caller]
    pub fn get_for_sumcheck_round_1(
        &mut self,
        inputs: &GKRInputs,
        folding_challenges: &[E],
    ) -> SumcheckRound1SelectedStorage<F, E> {
        let mut storage = SumcheckRound1SelectedStorage::default();
        for input in inputs.inputs_in_base.iter() {
            if *input == GKRAddress::placeholder() {
                let folding_challenge = folding_challenges[0];
                storage.base_field_inputs.push(
                    BaseFieldPolySourceAfterOneFolding::empty_with_folding_context(
                        folding_challenge,
                    ),
                );
            } else {
                let source = self.make_base_source_for_round_1(*input, folding_challenges);
                storage.base_field_inputs.push(source);
            }
        }
        for input in inputs.inputs_in_extension.iter() {
            if *input == GKRAddress::placeholder() {
                let folding_challenge = folding_challenges[0];
                storage.extension_field_inputs.push(
                    ExtensionFieldPolyContinuingSource::empty_with_folding_context(
                        folding_challenge,
                    ),
                );
            } else {
                let source =
                    self.make_ext_source_for_rounds_1_and_beyond(*input, folding_challenges);
                storage.extension_field_inputs.push(source);
            }
        }

        storage
    }

    #[track_caller]
    pub fn get_for_sumcheck_round_2(
        &mut self,
        inputs: &GKRInputs,
        folding_challenges: &[E],
    ) -> SumcheckRound2SelectedStorage<F, E> {
        assert_eq!(folding_challenges.len(), 2);
        let mut storage = SumcheckRound2SelectedStorage::default();
        for input in inputs.inputs_in_base.iter() {
            if *input == GKRAddress::placeholder() {
                let first_folding_challenge = folding_challenges[0];
                let second_folding_challenge = folding_challenges[1];
                storage.base_field_inputs.push(
                    BaseFieldPolySourceAfterTwoFoldings::empty_with_folding_context(
                        first_folding_challenge,
                        second_folding_challenge,
                    ),
                );
            } else {
                let source = self.make_base_source_for_round_2(*input, folding_challenges);
                storage.base_field_inputs.push(source);
            }
        }
        for input in inputs.inputs_in_extension.iter() {
            if *input == GKRAddress::placeholder() {
                let folding_challenge = *folding_challenges.last().expect("must be present");
                storage.extension_field_inputs.push(
                    ExtensionFieldPolyContinuingSource::empty_with_folding_context(
                        folding_challenge,
                    ),
                );
            } else {
                let source =
                    self.make_ext_source_for_rounds_1_and_beyond(*input, folding_challenges);
                storage.extension_field_inputs.push(source);
            }
        }

        storage
    }

    #[track_caller]
    pub fn get_for_sumcheck_round_3_and_beyond(
        &mut self,
        inputs: &GKRInputs,
        folding_challenges: &[E],
    ) -> SumcheckRound3AndBeyondSelectedStorage<F, E> {
        assert!(folding_challenges.len() >= 3);
        let mut storage = SumcheckRound3AndBeyondSelectedStorage::default();
        for input in inputs.inputs_in_base.iter() {
            if *input == GKRAddress::placeholder() {
                let folding_challenge = *folding_challenges.last().expect("must be present");
                storage.base_field_inputs.push(
                    ExtensionFieldPolyContinuingSource::empty_with_folding_context(
                        folding_challenge,
                    ),
                );
            } else {
                let source =
                    self.make_base_source_for_rounds_3_and_beyond(*input, folding_challenges);
                storage.base_field_inputs.push(source);
            }
        }
        for input in inputs.inputs_in_extension.iter() {
            if *input == GKRAddress::placeholder() {
                let folding_challenge = *folding_challenges.last().expect("must be present");
                storage.extension_field_inputs.push(
                    ExtensionFieldPolyContinuingSource::empty_with_folding_context(
                        folding_challenge,
                    ),
                );
            } else {
                let source =
                    self.make_ext_source_for_rounds_1_and_beyond(*input, folding_challenges);
                storage.extension_field_inputs.push(source);
            }
        }

        storage
    }
}

#[derive(Default, Debug)]
pub struct SumcheckRound0SelectedStorage<F: PrimeField, E: FieldExtension<F> + Field> {
    pub base_field_inputs: Vec<BaseFieldPolySource<F>>,
    pub extension_field_inputs: Vec<ExtensionFieldPolyInitialSource<F, E>>,
    pub base_field_outputs: Vec<BaseFieldPolySource<F>>,
    pub extension_field_outputs: Vec<ExtensionFieldPolyInitialSource<F, E>>,
    _marker: core::marker::PhantomData<E>,
}

#[derive(Default, Debug)]
pub struct SumcheckRound1SelectedStorage<F: PrimeField, E: FieldExtension<F> + Field> {
    pub base_field_inputs: Vec<BaseFieldPolySourceAfterOneFolding<F, E>>,
    pub extension_field_inputs: Vec<ExtensionFieldPolyContinuingSource<F, E>>,
}

// impl<F: PrimeField, E: FieldExtension<F> + Field> SumcheckRound1SelectedStorage<F, E> {
//     pub fn collect_last_values(
//         &self,
//         inputs: &GKRInputs,
//         last_evaluations: &mut BTreeMap<GKRAddress, [E; 2]>,
//     ) {
//         for input in inputs.inputs_in_base.iter() {
//             todo!()
//         }
//         let mut idx = 0;
//         for input in inputs.inputs_in_extension.iter() {
//             if *input == GKRAddress::placeholder() {
//                 // nothing
//             } else {
//                 if last_evaluations.contains_key(input) == false {
//                     let current_values = self.extension_field_inputs[idx].current_values();
//                     assert_eq!(current_values.len(), 2);
//                     // let [f0, f1] = self.extension_field_inputs[idx].get_f0_and_f1(0);

//                     last_evaluations.insert(*input, [current_values[0], current_values[1]]);
//                 }
//             }
//             idx += 1;
//         }
//     }
// }

#[derive(Default, Debug)]
pub struct SumcheckRound2SelectedStorage<F: PrimeField, E: FieldExtension<F> + Field> {
    pub base_field_inputs: Vec<BaseFieldPolySourceAfterTwoFoldings<F, E>>,
    pub extension_field_inputs: Vec<ExtensionFieldPolyContinuingSource<F, E>>,
}

#[derive(Default, Debug)]
pub struct SumcheckRound3AndBeyondSelectedStorage<F: PrimeField, E: FieldExtension<F> + Field> {
    pub base_field_inputs: Vec<ExtensionFieldPolyContinuingSource<F, E>>,
    pub extension_field_inputs: Vec<ExtensionFieldPolyContinuingSource<F, E>>,
    _marker: core::marker::PhantomData<(F, E)>,
}

impl<F: PrimeField, E: FieldExtension<F> + Field> SumcheckRound3AndBeyondSelectedStorage<F, E> {
    pub fn collect_last_values<const N: usize>(
        &self,
        inputs: &GKRInputs,
        last_evaluations: &mut BTreeMap<GKRAddress, [E; N]>,
    ) {
        {
            let mut idx = 0;
            for input in inputs.inputs_in_base.iter() {
                if *input == GKRAddress::placeholder() {
                    // nothing
                } else {
                    if let Some(existing_evals) = last_evaluations.get(input).copied() {
                        let current_values = self.base_field_inputs[idx].current_values();
                        assert_eq!(current_values.len(), N);
                        assert_eq!(existing_evals, current_values);
                    } else {
                        let current_values = self.base_field_inputs[idx].current_values();
                        assert_eq!(current_values.len(), N);
                        // let [f0, f1] = self.extension_field_inputs[idx].get_f0_and_f1(0);
                        // println!("Inserting evaluations for {:?}", input);
                        last_evaluations.insert(*input, current_values.try_into().unwrap());
                    }
                }
                idx += 1;
            }
        }
        {
            let mut idx = 0;
            for input in inputs.inputs_in_extension.iter() {
                if *input == GKRAddress::placeholder() {
                    // nothing
                } else {
                    if let Some(existing_evals) = last_evaluations.get(input).copied() {
                        let current_values = self.extension_field_inputs[idx].current_values();
                        assert_eq!(current_values.len(), N);
                        assert_eq!(existing_evals, current_values);
                    } else {
                        let current_values = self.extension_field_inputs[idx].current_values();
                        assert_eq!(current_values.len(), N);
                        // let [f0, f1] = self.extension_field_inputs[idx].get_f0_and_f1(0);
                        // println!("Inserting evaluations for {:?}", input);
                        last_evaluations.insert(*input, current_values.try_into().unwrap());
                    }
                }
                idx += 1;
            }
        }
    }
}
