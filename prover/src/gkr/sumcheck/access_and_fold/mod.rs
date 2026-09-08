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

#[derive(Clone, Copy, Debug)]
pub(crate) struct DisjointAccessQuasiSlice<T: Send + Sync, const INITIAL_ACCESS: bool> {
    pub(crate) ptr: *mut T,
    pub(crate) len: usize,
}

unsafe impl<T: Send + Sync, const INITIAL_ACCESS: bool> Send
    for DisjointAccessQuasiSlice<T, INITIAL_ACCESS>
{
}
unsafe impl<T: Send + Sync, const INITIAL_ACCESS: bool> Sync
    for DisjointAccessQuasiSlice<T, INITIAL_ACCESS>
{
}

impl<T: Send + Sync, const INITIAL_ACCESS: bool> DisjointAccessQuasiSlice<T, INITIAL_ACCESS> {
    #[inline(always)]
    pub(crate) fn write(&mut self, idx: usize, value: T) {
        debug_assert!(idx < self.len);
        unsafe {
            self.ptr.add(idx).write(value);
        }
    }

    pub(crate) fn from_init_slice_mut(src: &mut [T]) -> Self {
        assert!(src.len().is_power_of_two());
        let (ptr, len) = (src.as_mut_ptr(), src.len());
        Self { ptr, len }
    }

    pub(crate) fn from_init_slice(src: &[T]) -> Self {
        assert!(src.len().is_power_of_two());
        let (ptr, len) = (src.as_ptr(), src.len());
        Self {
            ptr: ptr.cast_mut(),
            len,
        }
    }

    pub(crate) fn from_uninit_slice_mut(src: &mut [MaybeUninit<T>]) -> Self {
        assert!(src.len().is_power_of_two());
        let (ptr, len) = (src.as_mut_ptr(), src.len());
        Self {
            ptr: ptr.cast(),
            len,
        }
    }

    pub(crate) fn from_uninit_slice(src: &[MaybeUninit<T>]) -> Self {
        assert!(src.len().is_power_of_two());
        let (ptr, len) = (src.as_ptr(), src.len());
        Self {
            ptr: ptr.cast_mut().cast(),
            len,
        }
    }
}

impl<T: Send + Sync> DisjointAccessQuasiSlice<T, false> {
    #[inline(always)]
    pub(crate) fn read(&self, idx: usize) -> T {
        debug_assert!(idx < self.len);
        unsafe { self.ptr.add(idx).read() }
    }
}

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

/// Cross-proof recycling pool for the extension-field polys that live in
/// [`GKRStorage`] (forward layer outputs, cache relations, dimension-
/// reduction outputs): exact-length free lists, filled lazily — the first
/// proof allocates (and pays the first-touch page faults), every later
/// proof of the same shape reuses. Buffers come back when the storage purges
/// a layer or is dropped. Attached to the storage by the GKR backend.
pub struct ExtPolyPool<E> {
    free: std::sync::Mutex<BTreeMap<usize, Vec<Box<[MaybeUninit<E>]>>>>,
    hits: std::sync::atomic::AtomicUsize,
    misses: std::sync::atomic::AtomicUsize,
    /// elements currently held by the free lists
    pooled: std::sync::atomic::AtomicUsize,
    /// base-poly buffers carved out of this pool (by pointer); they come
    /// back through `recycle_layer` like the extension polys
    base_owned: std::sync::Mutex<std::collections::BTreeSet<usize>>,
}

impl<E> ExtPolyPool<E> {
    pub fn new() -> Self {
        Self {
            free: std::sync::Mutex::new(BTreeMap::new()),
            hits: Default::default(),
            misses: Default::default(),
            pooled: Default::default(),
            base_owned: Default::default(),
        }
    }
    pub fn take(&self, len: usize) -> Box<[MaybeUninit<E>]> {
        use std::sync::atomic::Ordering::Relaxed;
        if let Some(b) = self.free.lock().unwrap().get_mut(&len).and_then(|v| v.pop()) {
            self.hits.fetch_add(1, Relaxed);
            self.pooled.fetch_sub(len, Relaxed);
            return b;
        }
        self.misses.fetch_add(1, Relaxed);
        Box::new_uninit_slice(len)
    }
    pub fn give(&self, b: Box<[E]>) {
        // the elements are plain field values: forgetting them is fine
        let raw: Box<[MaybeUninit<E>]> =
            unsafe { Box::from_raw(Box::into_raw(b) as *mut [MaybeUninit<E>]) };
        self.give_uninit(raw);
    }
    pub fn give_uninit(&self, b: Box<[MaybeUninit<E>]>) {
        use std::sync::atomic::Ordering::Relaxed;
        let len = b.len();
        self.pooled.fetch_add(len, Relaxed);
        self.free.lock().unwrap().entry(len).or_default().push(b);
    }
    fn register_base(&self, ptr: usize) {
        self.base_owned.lock().unwrap().insert(ptr);
    }
    fn unregister_base(&self, ptr: usize) -> bool {
        self.base_owned.lock().unwrap().remove(&ptr)
    }
    /// `(hits, misses, pooled elements)` since creation.
    pub fn stats(&self) -> (usize, usize, usize) {
        use std::sync::atomic::Ordering::Relaxed;
        (
            self.hits.load(Relaxed),
            self.misses.load(Relaxed),
            self.pooled.load(Relaxed),
        )
    }
}

#[derive(Default)]
pub struct GKRStorage<F: PrimeField, E: FieldExtension<F> + Field> {
    pub layers: Vec<GKRLayerSource<F, E>>,
    /// recycling pool for the extension polys (None: plain allocations)
    pub pool: Option<std::sync::Arc<ExtPolyPool<E>>>,
}

impl<F: PrimeField, E: FieldExtension<F> + Field> Drop for GKRStorage<F, E> {
    fn drop(&mut self) {
        let layers = core::mem::take(&mut self.layers);
        for layer in layers {
            self.recycle_layer(layer);
        }
    }
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

    pub fn get_base_layer(&self, address: GKRAddress) -> &[F] {
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

    pub fn try_get_base_poly(&self, address: GKRAddress) -> Option<&[F]> {
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

    pub fn try_get_ext_poly(&self, address: GKRAddress) -> Option<&[E]> {
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
        if self.layers.len() > layer + 1 {
            let removed = self.layers.split_off(layer + 1);
            for l in removed {
                self.recycle_layer(l);
            }
        }
    }

    /// Uninit buffer for an extension poly of `len` values: from the pool
    /// when one is attached, a fresh allocation otherwise.
    pub fn alloc_ext_uninit(&self, len: usize) -> Box<[MaybeUninit<E>]> {
        match &self.pool {
            Some(pool) => pool.take(len),
            None => Box::new_uninit_slice(len),
        }
    }

    /// Return a purged layer's uniquely owned extension polys (and the base
    /// polys carved out of the pool by `alloc_base_uninit`) to the pool.
    fn recycle_layer(&self, layer: GKRLayerSource<F, E>) {
        let Some(pool) = &self.pool else {
            return;
        };
        for (_, poly) in layer.extension_field_inputs.into_iter() {
            if let Ok(values) = std::sync::Arc::try_unwrap(poly.values) {
                pool.give(values);
            }
        }
        for (_, poly) in layer.base_field_inputs.into_iter() {
            if let Ok(values) = std::sync::Arc::try_unwrap(poly.values) {
                if pool.unregister_base(values.as_ptr() as usize) {
                    // same Layout as the E buffer it was carved from
                    let len = values.len() / 4;
                    let raw = Box::into_raw(values) as *mut F as *mut MaybeUninit<E>;
                    pool.give_uninit(unsafe {
                        Box::from_raw(core::ptr::slice_from_raw_parts_mut(raw, len))
                    });
                }
            }
        }
    }

    /// Uninit buffer for a base poly of `len` values: carved out of the
    /// extension pool when one is attached and the layouts line up (E is
    /// four F limbs), a fresh allocation otherwise.
    pub fn alloc_base_uninit(&self, len: usize) -> Box<[MaybeUninit<F>]> {
        if let Some(pool) = &self.pool {
            if len % 4 == 0
                && core::mem::size_of::<E>() == 4 * core::mem::size_of::<F>()
                && core::mem::align_of::<E>() == core::mem::align_of::<F>()
            {
                let b = pool.take(len / 4);
                let ptr = Box::into_raw(b) as *mut MaybeUninit<E> as *mut MaybeUninit<F>;
                pool.register_base(ptr as usize);
                return unsafe { Box::from_raw(core::ptr::slice_from_raw_parts_mut(ptr, len)) };
            }
        }
        Box::new_uninit_slice(len)
    }

    #[track_caller]
    pub fn get_ext_poly(&self, address: GKRAddress) -> &[E] {
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

impl<F: PrimeField, E: FieldExtension<F> + Field> SumcheckRound1SelectedStorage<F, E> {
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
                        assert_eq!(&existing_evals[..], &current_values[..]);
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

    // pub fn collect_last_values(
    //     &self,
    //     inputs: &GKRInputs,
    //     last_evaluations: &mut BTreeMap<GKRAddress, [E; 2]>,
    // ) {
    //     for input in inputs.inputs_in_base.iter() {
    //         panic!("for model that collect from such sources base field inputs are unexpected");
    //     }
    //     let mut idx = 0;
    //     for input in inputs.inputs_in_extension.iter() {
    //         if *input == GKRAddress::placeholder() {
    //             // nothing
    //         } else {
    //             if last_evaluations.contains_key(input) == false {
    //                 let current_values = self.extension_field_inputs[idx].current_values();
    //                 assert_eq!(current_values.len(), 2);
    //                 // let [f0, f1] = self.extension_field_inputs[idx].get_f0_and_f1(0);

    //                 last_evaluations.insert(*input, [current_values[0], current_values[1]]);
    //             }
    //         }
    //         idx += 1;
    //     }
    // }
}

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
