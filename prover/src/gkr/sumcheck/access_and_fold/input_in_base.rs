use field::Field;

use super::*;

pub struct BaseFieldPoly<F: PrimeField> {
    pub(crate) values: Box<[F]>,
}

impl<F: PrimeField> BaseFieldPoly<F> {
    pub fn new(values: Box<[F]>) -> Self {
        assert!(values.len().is_power_of_two());
        Self { values }
    }

    pub fn accessor(&self) -> BaseFieldPolySource<F> {
        BaseFieldPolySource {
            start: self.values.as_ptr(),
            next_layer_size: self.values.len() / 2,
        }
    }
}

#[derive(Debug)]
pub struct BaseFieldPolySource<F: PrimeField> {
    start: *const F,
    next_layer_size: usize,
}

unsafe impl<F: PrimeField> Send for BaseFieldPolySource<F> {}
unsafe impl<F: PrimeField> Sync for BaseFieldPolySource<F> {}

impl<F: PrimeField, E: FieldExtension<F> + Field>
    EvaluationFormStorage<F, E, BaseFieldRepresentation<F>> for BaseFieldPolySource<F>
{
    const SHOULD_ACCESS_TO_PREPARE_FOR_NEXT_STEP: bool = false;

    fn dummy() -> Self {
        Self {
            start: null_mut(),
            next_layer_size: 0,
        }
    }
    #[inline(always)]
    fn get_collapse_context(
        &self,
    ) -> &<BaseFieldRepresentation<F> as EvaluationRepresentation<F, E>>::CollapseContext {
        &()
    }
    #[inline(always)]
    fn get_at_index(&self, index: usize) -> BaseFieldRepresentation<F> {
        debug_assert!(index < self.next_layer_size * 2);
        unsafe {
            let f0 = self.start.add(index).read();

            BaseFieldRepresentation(f0)
        }
    }
    #[inline(always)]
    fn get_f0_and_f1(&self, index: usize) -> [BaseFieldRepresentation<F>; 2] {
        debug_assert!(index < self.next_layer_size);
        [
            EvaluationFormStorage::<F, E, _>::get_at_index(self, index),
            EvaluationFormStorage::<F, E, _>::get_at_index(self, self.next_layer_size + index),
        ]
    }
}

#[derive(Debug)]
pub struct BaseFieldPolySourceAfterOneFolding<F: PrimeField, E: FieldExtension<F> + Field> {
    pub(crate) base_layer_half_size: usize,
    pub(crate) next_layer_size: usize,
    pub(crate) base_input_start: *const F,
    pub(crate) first_folding_challenge_and_squared: (E, E),
}

unsafe impl<F: PrimeField, E: FieldExtension<F> + Field> Send
    for BaseFieldPolySourceAfterOneFolding<F, E>
{
}
unsafe impl<F: PrimeField, E: FieldExtension<F> + Field> Sync
    for BaseFieldPolySourceAfterOneFolding<F, E>
{
}

impl<F: PrimeField, E: FieldExtension<F> + Field>
    EvaluationFormStorage<F, E, BaseFieldFoldedOnceRepresentation<F>>
    for BaseFieldPolySourceAfterOneFolding<F, E>
{
    const SHOULD_ACCESS_TO_PREPARE_FOR_NEXT_STEP: bool = false;

    fn dummy() -> Self {
        Self {
            base_input_start: null_mut(),
            first_folding_challenge_and_squared: (E::ZERO, E::ZERO),
            base_layer_half_size: 0,
            next_layer_size: 0,
        }
    }
    #[inline(always)]
    fn get_collapse_context(
        &self,
    ) -> &<BaseFieldFoldedOnceRepresentation<F> as EvaluationRepresentation<F, E>>::CollapseContext
    {
        &self.first_folding_challenge_and_squared
    }
    #[inline(always)]
    fn get_at_index(&self, index: usize) -> BaseFieldFoldedOnceRepresentation<F> {
        debug_assert!(index < self.next_layer_size * 2);
        todo!();
    }
    #[inline(always)]
    fn get_f0_and_f1(&self, index: usize) -> [BaseFieldFoldedOnceRepresentation<F>; 2] {
        // our representation is "lazy" - it is a poly over `r` with coefficients f'(X) = (f(0, X), f(1, X) - f(0, X)).
        // Now we need to output:
        // - f'(0, Y) = (f(0, 0, Y), f(1, 0, Y) - f(0, 0, Y))
        // - f'(1, Y) = (f(0, 1, Y), f(1, 1, Y) - f(0, 1, Y))
        // we take a decision to trade memory consumption for speed, and so we access input array at 4 values and recompute
        debug_assert!(index < self.next_layer_size);
        unsafe {
            // we take computation
            let f00 = self.base_input_start.add(index).read();
            let f01 = self
                .base_input_start
                .add(self.base_layer_half_size + index)
                .read();
            let f10 = self
                .base_input_start
                .add(self.next_layer_size + index)
                .read();
            let f11 = self
                .base_input_start
                .add(self.base_layer_half_size + self.next_layer_size + index)
                .read();
            let f0_c0 = f00;
            let mut f0_c1 = f01;
            f0_c1.sub_assign(&f00);

            let f1_c0 = f10;
            let mut f1_c1 = f11;
            f1_c1.sub_assign(&f10);

            [
                BaseFieldFoldedOnceRepresentation::new(f0_c0, f0_c1),
                BaseFieldFoldedOnceRepresentation::new(f1_c0, f1_c1),
            ]
        }
    }
}

pub struct BaseFieldPolyIntermediateFoldingStorage<F: PrimeField, E: FieldExtension<F> + Field> {
    pub(crate) continuous_buffer: Box<[MaybeUninit<E>]>,
    pub(crate) size_after_two_folds: usize,
    pub(crate) _marker: core::marker::PhantomData<F>,
}

impl<F: PrimeField, E: FieldExtension<F> + Field> BaseFieldPolyIntermediateFoldingStorage<F, E> {
    pub fn new_for_base_poly_size(base_poly_size: usize) -> Self {
        assert!(base_poly_size.is_power_of_two());
        assert!(base_poly_size > 4);
        let size_after_two_folds = base_poly_size / 4;
        let buffer_size = size_after_two_folds * 2; // coarse
        let continuous_buffer = Box::new_uninit_slice(buffer_size);
        Self {
            continuous_buffer,
            size_after_two_folds,
            _marker: core::marker::PhantomData,
        }
    }

    pub fn pointers_for_sumcheck_accessor_step(&mut self, step: usize) -> (*mut E, *mut E) {
        unsafe {
            assert!(step >= 2);
            let mut input_offset = self.continuous_buffer.as_mut_ptr();
            let mut input_size = self.size_after_two_folds;
            let mut next_step_offset = input_offset.add(input_size);
            for _ in 2..step {
                input_offset = next_step_offset;
                input_size /= 2;
                next_step_offset = next_step_offset.add(input_size);
            }

            (input_offset.cast(), next_step_offset.cast())
        }
    }
}

#[derive(Debug)]
pub struct BaseFieldPolySourceAfterTwoFoldings<F: PrimeField, E: FieldExtension<F> + Field> {
    pub(crate) base_input_start: *const F,
    pub(crate) this_layer_cache_start: *mut E,
    pub(crate) base_layer_half_size: usize,
    pub(crate) base_quarter_size: usize,
    pub(crate) next_layer_size: usize,
    pub(crate) first_folding_challenge: E,
    pub(crate) second_folding_challenge: E,
    pub(crate) first_access: bool,
}

unsafe impl<F: PrimeField, E: FieldExtension<F> + Field> Send
    for BaseFieldPolySourceAfterTwoFoldings<F, E>
{
}
unsafe impl<F: PrimeField, E: FieldExtension<F> + Field> Sync
    for BaseFieldPolySourceAfterTwoFoldings<F, E>
{
}

impl<F: PrimeField, E: FieldExtension<F> + Field>
    EvaluationFormStorage<F, E, ExtensionFieldRepresentation<F, E>>
    for BaseFieldPolySourceAfterTwoFoldings<F, E>
{
    const SHOULD_ACCESS_TO_PREPARE_FOR_NEXT_STEP: bool = true;

    fn dummy() -> Self {
        Self {
            base_input_start: null_mut(),
            this_layer_cache_start: null_mut(),
            base_layer_half_size: 0,
            base_quarter_size: 0,
            next_layer_size: 0,
            first_folding_challenge: E::ZERO,
            second_folding_challenge: E::ZERO,
            first_access: false,
        }
    }
    #[inline(always)]
    fn get_collapse_context(
        &self,
    ) -> &<ExtensionFieldRepresentation<F, E> as EvaluationRepresentation<F, E>>::CollapseContext
    {
        &()
    }

    #[inline(always)]
    fn get_at_index(&self, index: usize) -> ExtensionFieldRepresentation<F, E> {
        todo!();
    }

    #[inline(always)]
    fn get_f0_and_f1(&self, index: usize) -> [ExtensionFieldRepresentation<F, E>; 2] {
        // Same recomputation logic as in the previous implementation, but we also fold by using folding challenges,
        // and save computed extension elements

        todo!();

        // debug_assert!(index < self.next_layer_size);
        // unsafe {
        //     if self.first_access {
        //         let t = [index, index + self.next_layer_size].map(|index| {
        //             // we take computation
        //             let f00 = self.base_input_start.add(index).read();
        //             let f01 = self
        //                 .base_input_start
        //                 .add(self.base_quarter_size + index)
        //                 .read();
        //             let f10 = self
        //                 .base_input_start
        //                 .add(self.base_layer_half_size + index)
        //                 .read();
        //             let f11 = self
        //                 .base_input_start
        //                 .add(self.base_layer_half_size + self.base_quarter_size + index)
        //                 .read();
        //             let f0_c0 = f00;
        //             let mut f0_c1 = f10;
        //             f0_c1.sub_assign(&f00);

        //             let mut f1_c0 = f01;
        //             f1_c0.sub_assign(&f00);
        //             let mut f1_c1 = f11;
        //             f1_c1.sub_assign(&f01);
        //             f1_c1.sub_assign(&f0_c0);

        //             let mut f0 = self.first_folding_challenge;
        //             f0.mul_assign_by_base(&f0_c1);
        //             f0.add_assign_base(&f0_c0);

        //             let mut f1_minus_f0 = self.first_folding_challenge;
        //             f1_minus_f0.mul_assign_by_base(&f1_c1);
        //             f1_minus_f0.add_assign_base(&f1_c0);

        //             (f0, f1_minus_f0)
        //         });
        //         let [f0, f1] = t.map(|(f0, f1_minus_f0)| {
        //             let mut result = self.second_folding_challenge;
        //             result.mul_assign(&f1_minus_f0);
        //             result.sub_assign(&f0);

        //             result
        //         });

        //         // we do not want to recompute f0 and f1, so we want to memorize f0, and write f1 - f0 into next poly cache
        //         self.this_layer_cache_start.add(index).write(f0);
        //         self.this_layer_cache_start
        //             .add(self.next_layer_size + index)
        //             .write(f1);

        //         [
        //             ExtensionFieldRepresentation {
        //                 value: f0,
        //                 _marker: core::marker::PhantomData,
        //             },
        //             ExtensionFieldRepresentation {
        //                 value: f1,
        //                 _marker: core::marker::PhantomData,
        //             },
        //         ]
        //     } else {
        //         let f0 = self.this_layer_cache_start.add(index).read();
        //         let f1 = self.this_layer_cache_start.add(self.next_layer_size + index).read();

        //         [
        //             ExtensionFieldRepresentation {
        //                 value: f0,
        //                 _marker: core::marker::PhantomData,
        //             },
        //             ExtensionFieldRepresentation {
        //                 value: f1,
        //                 _marker: core::marker::PhantomData,
        //             },
        //         ]
        //     }
        // }
    }
}
