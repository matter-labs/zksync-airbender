use field::Field;

use super::*;

#[derive(Debug)]
pub struct BaseFieldPoly<F: PrimeField> {
    pub(crate) values: Arc<Box<[F]>>,
}

impl<F: PrimeField> BaseFieldPoly<F> {
    pub fn new(values: Box<[F]>) -> Self {
        assert!(values.len().is_power_of_two());
        Self {
            values: Arc::new(values),
        }
    }

    pub fn from_arc(values: Arc<Box<[F]>>) -> Self {
        assert!(values.len().is_power_of_two());
        Self { values }
    }

    pub fn accessor(&self) -> BaseFieldPolySource<F> {
        BaseFieldPolySource {
            start: self.values.as_ptr(),
            next_layer_size: self.values.len() / 2,
        }
    }

    pub fn arc_clone(&self) -> Self {
        Self {
            values: Arc::clone(&self.values),
        }
    }
}

#[derive(Debug)]
pub struct BaseFieldPolySource<F: PrimeField> {
    start: *const F,
    next_layer_size: usize,
}

impl<F: PrimeField> BaseFieldPolySource<F> {
    pub(crate) fn current_values(&'_ self) -> &'_ [F] {
        unsafe { core::slice::from_raw_parts(self.start, self.next_layer_size * 2) }
    }

    pub(crate) fn empty() -> Self {
        Self {
            start: null_mut(),
            next_layer_size: 0,
        }
    }
}

unsafe impl<F: PrimeField> Send for BaseFieldPolySource<F> {}
unsafe impl<F: PrimeField> Sync for BaseFieldPolySource<F> {}

impl<F: PrimeField, E: FieldExtension<F> + Field>
    EvaluationFormStorage<F, E, BaseFieldRepresentation<F>> for BaseFieldPolySource<F>
{
    const SHOULD_ACCESS_TO_PREPARE_FOR_NEXT_STEP: bool = false;

    #[inline(always)]
    fn get_collapse_context(
        &self,
    ) -> &<BaseFieldRepresentation<F> as EvaluationRepresentation<F, E>>::CollapseContext {
        &()
    }
    #[inline(always)]
    fn get_at_index(&self, index: usize) -> BaseFieldRepresentation<F> {
        assert!(index < self.next_layer_size * 2);
        unsafe {
            let f0 = self.start.add(index).read();

            BaseFieldRepresentation(f0)
        }
    }
    #[inline(always)]
    fn get_f0_and_f1(&self, index: usize) -> [BaseFieldRepresentation<F>; 2] {
        assert!(index < self.next_layer_size);
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

impl<F: PrimeField, E: FieldExtension<F> + Field> BaseFieldPolySourceAfterOneFolding<F, E> {
    pub(crate) fn current_values(&self) -> Vec<E> {
        let mut result_evals = Vec::with_capacity(self.base_layer_half_size);
        unsafe {
            let evals =
                core::slice::from_raw_parts(self.base_input_start, self.base_layer_half_size * 2);
            let (f0s, f1s) = evals.split_at(self.base_layer_half_size);
            for (f0, f1) in f0s.iter().zip(f1s.iter()) {
                let mut diff = *f1;
                diff.sub_assign(f0);
                let mut result = self.first_folding_challenge_and_squared.0;
                result.mul_assign_by_base(&diff);
                result.add_assign_base(f0);
                result_evals.push(result);
            }
        }

        result_evals
    }

    pub(crate) fn empty_with_folding_context(folding_challenge: E) -> Self {
        let mut challenge_squared = folding_challenge;
        challenge_squared.square();
        Self {
            base_input_start: null_mut(),
            first_folding_challenge_and_squared: (folding_challenge, challenge_squared),
            base_layer_half_size: 0,
            next_layer_size: 0,
        }
    }
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

    #[inline(always)]
    fn get_collapse_context(
        &self,
    ) -> &<BaseFieldFoldedOnceRepresentation<F> as EvaluationRepresentation<F, E>>::CollapseContext
    {
        &self.first_folding_challenge_and_squared
    }
    #[inline(always)]
    fn get_at_index(&self, index: usize) -> BaseFieldFoldedOnceRepresentation<F> {
        assert!(index < self.base_layer_half_size);
        unsafe {
            // we take computation
            let f0 = self.base_input_start.add(index).read();
            let f1 = self
                .base_input_start
                .add(self.base_layer_half_size + index)
                .read();
            let c0 = f0;
            let mut c1 = f1;
            c1.sub_assign(&f0);

            BaseFieldFoldedOnceRepresentation::new(c0, c1)
        }
    }
    #[inline(always)]
    fn get_f0_and_f1(&self, index: usize) -> [BaseFieldFoldedOnceRepresentation<F>; 2] {
        assert!(index < self.next_layer_size);
        [
            EvaluationFormStorage::<F, E, _>::get_at_index(self, index),
            EvaluationFormStorage::<F, E, _>::get_at_index(self, self.next_layer_size + index),
        ]
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

    pub fn initial_pointer(&mut self) -> *mut E {
        self.continuous_buffer.as_mut_ptr().cast()
    }

    pub fn pointers_for_sumcheck_accessor_step(&mut self, step: usize) -> (*mut E, *mut E) {
        unsafe {
            assert!(step > 2);
            let mut input_offset = self.continuous_buffer.as_mut_ptr();
            let mut input_size = self.size_after_two_folds;
            let mut next_step_offset = input_offset.add(input_size);
            for _ in 3..step {
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
    pub(crate) combined_challenges: E, // r1 * r2, precomputed to avoid E×E at get_at_index time
    pub(crate) first_access: bool,
}

impl<F: PrimeField, E: FieldExtension<F> + Field> BaseFieldPolySourceAfterTwoFoldings<F, E> {
    pub(crate) fn current_values(&self) -> Vec<E> {
        let mut result_evals = Vec::with_capacity(self.base_layer_half_size);
        unsafe {
            let evals =
                core::slice::from_raw_parts(self.base_input_start, self.base_layer_half_size * 2);
            for i in 0..self.base_quarter_size {
                let mut diff = evals[i + self.base_layer_half_size];
                diff.sub_assign(&evals[i]);
                let mut f0 = self.first_folding_challenge;
                f0.mul_assign_by_base(&diff);
                f0.add_assign_base(&evals[i]);

                let mut diff = evals[i + self.base_quarter_size + self.base_layer_half_size];
                diff.sub_assign(&evals[i + self.base_quarter_size]);
                let mut f1 = self.first_folding_challenge;
                f1.mul_assign_by_base(&diff);
                f1.add_assign_base(&evals[i + self.base_quarter_size]);

                let mut diff = f1;
                diff.sub_assign(&f0);
                let mut result = diff;
                result.mul_assign(&self.second_folding_challenge);
                result.add_assign(&f0);
                result_evals.push(result);
            }
        }

        result_evals
    }

    pub(crate) fn empty_with_folding_context(
        first_folding_challenge: E,
        second_folding_challenge: E,
    ) -> Self {
        let mut combined_challenges = first_folding_challenge;
        combined_challenges.mul_assign(&second_folding_challenge);
        Self {
            base_input_start: null_mut(),
            this_layer_cache_start: null_mut(),
            base_layer_half_size: 0,
            base_quarter_size: 0,
            next_layer_size: 0,
            first_folding_challenge,
            second_folding_challenge,
            combined_challenges,
            first_access: false,
        }
    }
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

    #[inline(always)]
    fn get_collapse_context(
        &self,
    ) -> &<ExtensionFieldRepresentation<F, E> as EvaluationRepresentation<F, E>>::CollapseContext
    {
        &()
    }

    #[inline(always)]
    fn get_at_index(&self, index: usize) -> ExtensionFieldRepresentation<F, E> {
        assert!(index < self.next_layer_size * 2);
        // fold two times
        unsafe {
            if self.first_access {
                // Use the multilinear expansion to avoid an E×E multiplication:
                //   f(r1, r2) = f00 + r1*(f01-f00) + r2*(f10-f00) + r1*r2*(f00-f01-f10+f11)
                // All four coefficients are base-field values, so all multiplications are E×F.

                let f00 = self.base_input_start.add(index).read();
                let f01 = self
                    .base_input_start
                    .add(self.base_layer_half_size + index)
                    .read();
                let f10 = self
                    .base_input_start
                    .add(self.base_quarter_size + index)
                    .read();
                let f11 = self
                    .base_input_start
                    .add(self.base_layer_half_size + self.base_quarter_size + index)
                    .read();

                // c01 = f01 - f00
                let mut c01 = f01;
                c01.sub_assign(&f00);
                // c10 = f10 - f00
                let mut c10 = f10;
                c10.sub_assign(&f00);
                // c11 = f00 - f01 - f10 + f11
                let mut c11 = f00;
                c11.sub_assign(&f01);
                c11.sub_assign(&f10);
                c11.add_assign(&f11);

                // result = f00 + r1*c01 + r2*c10 + (r1*r2)*c11  — all E×F
                let mut term_r1 = self.first_folding_challenge;
                term_r1.mul_assign_by_base(&c01);

                let mut term_r2 = self.second_folding_challenge;
                term_r2.mul_assign_by_base(&c10);

                let mut term_r1r2 = self.combined_challenges;
                term_r1r2.mul_assign_by_base(&c11);

                let mut result = term_r1;
                result.add_assign(&term_r2);
                result.add_assign(&term_r1r2);
                result.add_assign_base(&f00);

                // write down
                self.this_layer_cache_start.add(index).write(result);

                ExtensionFieldRepresentation {
                    value: result,
                    _marker: core::marker::PhantomData,
                }
            } else {
                let result = self.this_layer_cache_start.add(index).read();

                ExtensionFieldRepresentation {
                    value: result,
                    _marker: core::marker::PhantomData,
                }
            }
        }
    }

    #[inline(always)]
    fn get_f0_and_f1(&self, index: usize) -> [ExtensionFieldRepresentation<F, E>; 2] {
        // just read and do NOT cache f1 - f0
        assert!(index < self.next_layer_size);
        [
            self.get_at_index(index),
            self.get_at_index(self.next_layer_size + index),
        ]
    }
}
