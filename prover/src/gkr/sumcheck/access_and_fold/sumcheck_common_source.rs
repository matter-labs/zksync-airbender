use super::*;
use sumcheck_common::representation::EvaluationRepresentaionBase;

// sumcheck round 0

pub struct SumcheckRound0Source<'a, F: PrimeField, E: FieldExtension<F> + Field> {
    storage: &'a mut GKRStorage<F, E>,
}

#[derive(Debug)]
pub struct BaseFieldPolyAccessor<F: PrimeField> {
    start: *const F,
    next_layer_size: usize,
}

unsafe impl<F: PrimeField> Send for BaseFieldPolyAccessor<F> {}
unsafe impl<F: PrimeField> Sync for BaseFieldPolyAccessor<F> {}

impl<F: PrimeField> BaseFieldPolyAccessor<F> {
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

impl<F: PrimeField, E: FieldExtension<F> + Field>
    sumcheck_common::representation::PolyAccessor<F, E> for BaseFieldPolyAccessor<F>
{
    const SHOULD_ACCESS_TO_PREPARE_FOR_NEXT_STEP: bool = false;
    type Representation = sumcheck_common::representation::base::BaseFieldRepresentation<F>;

    #[inline(always)]
    fn get_at_index<const ASSUME_PREFOLDED: bool>(
        &self,
        index: usize,
    ) -> sumcheck_common::representation::base::BaseFieldRepresentation<F> {
        assert!(index < self.next_layer_size * 2);
        unsafe {
            let f0 = self.start.add(index).read();

            sumcheck_common::representation::base::BaseFieldRepresentation::new(f0)
        }
    }
    #[inline(always)]
    fn get_f0_and_f1<const ASSUME_PREFOLDED: bool>(
        &self,
        index: usize,
    ) -> [sumcheck_common::representation::base::BaseFieldRepresentation<F>; 2] {
        assert!(index < self.next_layer_size);
        [
            sumcheck_common::representation::PolyAccessor::<F, E>::get_at_index::<ASSUME_PREFOLDED>(
                self, index,
            ),
            sumcheck_common::representation::PolyAccessor::<F, E>::get_at_index::<ASSUME_PREFOLDED>(
                self,
                self.next_layer_size + index,
            ),
        ]
    }
}

#[derive(Debug)]
pub struct ExtensionFieldPolyInitialAccessor<F: PrimeField, E: FieldExtension<F> + Field> {
    pub(crate) start: *const E,
    pub(crate) next_layer_size: usize,
    pub(crate) _marker: core::marker::PhantomData<F>,
}

unsafe impl<F: PrimeField, E: FieldExtension<F> + Field> Send
    for ExtensionFieldPolyInitialAccessor<F, E>
{
}
unsafe impl<F: PrimeField, E: FieldExtension<F> + Field> Sync
    for ExtensionFieldPolyInitialAccessor<F, E>
{
}

impl<F: PrimeField, E: FieldExtension<F> + Field>
    sumcheck_common::representation::PolyAccessor<F, E>
    for ExtensionFieldPolyInitialAccessor<F, E>
{
    const SHOULD_ACCESS_TO_PREPARE_FOR_NEXT_STEP: bool = false;
    type Representation = sumcheck_common::representation::ext::ExtensionFieldRepresentation<F, E>;

    #[inline(always)]
    fn get_at_index<const ASSUME_PREFOLDED: bool>(
        &self,
        index: usize,
    ) -> sumcheck_common::representation::ext::ExtensionFieldRepresentation<F, E> {
        assert!(index < self.next_layer_size * 2);
        unsafe {
            let f0 = self.start.add(index).read();

            sumcheck_common::representation::ext::ExtensionFieldRepresentation::<F, E>::new(f0)
        }
    }
    #[inline(always)]
    fn get_f0_and_f1<const ASSUME_PREFOLDED: bool>(
        &self,
        index: usize,
    ) -> [sumcheck_common::representation::ext::ExtensionFieldRepresentation<F, E>; 2] {
        assert!(index < self.next_layer_size);
        [
            sumcheck_common::representation::PolyAccessor::<F, E>::get_at_index::<ASSUME_PREFOLDED>(
                self, index,
            ),
            sumcheck_common::representation::PolyAccessor::<F, E>::get_at_index::<ASSUME_PREFOLDED>(
                self,
                self.next_layer_size + index,
            ),
        ]
    }
}

impl<'a, F: PrimeField, E: FieldExtension<F> + Field>
    sumcheck_common::representation::SumcheckRoundSource<F, E> for SumcheckRound0Source<'a, F, E>
{
    type BaseFieldInput = sumcheck_common::representation::base::BaseFieldRepresentation<F>;
    type BaseInputAccessor = BaseFieldPolyAccessor<F>;

    type ExtFieldInput = sumcheck_common::representation::ext::ExtensionFieldRepresentation<F, E>;
    type ExtInputAccessor = ExtensionFieldPolyInitialAccessor<F, E>;

    fn base_field_input_ctx(
        &self,
    ) -> <Self::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX {
        ()
    }
    fn ext_field_input_ctx(
        &self,
    ) -> <Self::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX {
        ()
    }
    fn get_source_for_base_poly(&mut self, address: GKRAddress) -> Self::BaseInputAccessor {
        let base_field_poly = self.storage.get_base_field_initial_source(&address);
        BaseFieldPolyAccessor {
            start: base_field_poly.start,
            next_layer_size: base_field_poly.next_layer_size,
        }
    }
    fn get_source_for_ext_poly(&mut self, address: GKRAddress) -> Self::ExtInputAccessor {
        let ext_field_poly = self.storage.get_extension_field_initial_source(&address);
        ExtensionFieldPolyInitialAccessor {
            start: ext_field_poly.start,
            next_layer_size: ext_field_poly.next_layer_size,
            _marker: core::marker::PhantomData,
        }
    }
}

// sumcheck round 1

pub struct SumcheckRound1Source<'a, F: PrimeField, E: FieldExtension<F> + Field> {
    storage: &'a mut GKRStorage<F, E>,
    folding_challenges: Vec<E>,
    first_folding_challenge_and_squared: (E, E),
}

#[derive(Debug)]
pub struct BaseFieldPolyAccessorAfterOneFolding<F: PrimeField> {
    pub(crate) base_layer_half_size: usize,
    pub(crate) next_layer_size: usize,
    pub(crate) base_input_start: *const F,
    // pub(crate) first_folding_challenge_and_squared: (E, E),
}

unsafe impl<F: PrimeField> Send for BaseFieldPolyAccessorAfterOneFolding<F> {}
unsafe impl<F: PrimeField> Sync for BaseFieldPolyAccessorAfterOneFolding<F> {}

// impl<F: PrimeField, E: FieldExtension<F> + Field> BaseFieldPolyAccessorAfterOneFolding<F, E> {
//     pub(crate) fn current_values(&self) -> Vec<E> {
//         let mut result_evals = Vec::with_capacity(self.base_layer_half_size);
//         unsafe {
//             let evals =
//                 core::slice::from_raw_parts(self.base_input_start, self.base_layer_half_size * 2);
//             let (f0s, f1s) = evals.split_at(self.base_layer_half_size);
//             for (f0, f1) in f0s.iter().zip(f1s.iter()) {
//                 let mut diff = *f1;
//                 diff.sub_assign(f0);
//                 let mut result = self.first_folding_challenge_and_squared.0;
//                 result.mul_assign_by_base(&diff);
//                 result.add_assign_base(f0);
//                 result_evals.push(result);
//             }
//         }

//         result_evals
//     }

//     pub(crate) fn empty_with_folding_context(folding_challenge: E) -> Self {
//         let mut challenge_squared = folding_challenge;
//         challenge_squared.square();
//         Self {
//             base_input_start: null_mut(),
//             first_folding_challenge_and_squared: (folding_challenge, challenge_squared),
//             base_layer_half_size: 0,
//             next_layer_size: 0,
//         }
//     }
// }

impl<F: PrimeField, E: FieldExtension<F> + Field>
    sumcheck_common::representation::PolyAccessor<F, E>
    for BaseFieldPolyAccessorAfterOneFolding<F>
{
    const SHOULD_ACCESS_TO_PREPARE_FOR_NEXT_STEP: bool = false;
    type Representation =
        sumcheck_common::representation::once_folded::BaseFieldFoldedOnceRepresentation<F>;

    #[inline(always)]
    fn get_at_index<const ASSUME_PREFOLDED: bool>(
        &self,
        index: usize,
    ) -> sumcheck_common::representation::once_folded::BaseFieldFoldedOnceRepresentation<F> {
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

            sumcheck_common::representation::once_folded::BaseFieldFoldedOnceRepresentation::<F>::new(c0, c1)
        }
    }
    #[inline(always)]
    fn get_f0_and_f1<const ASSUME_PREFOLDED: bool>(
        &self,
        index: usize,
    ) -> [sumcheck_common::representation::once_folded::BaseFieldFoldedOnceRepresentation<F>; 2]
    {
        assert!(index < self.next_layer_size);
        [
            sumcheck_common::representation::PolyAccessor::<F, E>::get_at_index::<ASSUME_PREFOLDED>(
                self, index,
            ),
            sumcheck_common::representation::PolyAccessor::<F, E>::get_at_index::<ASSUME_PREFOLDED>(
                self,
                self.next_layer_size + index,
            ),
        ]
    }
}

#[derive(Debug)]
pub struct ExtensionFieldPolyContinuingAccessor<F: PrimeField, E: FieldExtension<F> + Field> {
    pub(crate) previous_layer_start: *const E,
    pub(crate) this_layer_start: *mut E,
    pub(crate) this_layer_size: usize,
    pub(crate) next_layer_size: usize,
    pub(crate) folding_challenge: E,
    pub(crate) _marker: core::marker::PhantomData<F>,
}

unsafe impl<F: PrimeField, E: FieldExtension<F> + Field> Send
    for ExtensionFieldPolyContinuingAccessor<F, E>
{
}
unsafe impl<F: PrimeField, E: FieldExtension<F> + Field> Sync
    for ExtensionFieldPolyContinuingAccessor<F, E>
{
}

impl<F: PrimeField, E: FieldExtension<F> + Field> ExtensionFieldPolyContinuingAccessor<F, E> {
    pub(crate) fn previous_values(&'_ self) -> &'_ [E] {
        unsafe { core::slice::from_raw_parts(self.previous_layer_start, self.this_layer_size * 2) }
    }
    pub(crate) fn current_values(&'_ self) -> &'_ [E] {
        unsafe {
            core::slice::from_raw_parts(self.this_layer_start.cast_const(), self.this_layer_size)
        }
    }
}

impl<F: PrimeField, E: FieldExtension<F> + Field>
    sumcheck_common::representation::PolyAccessor<F, E>
    for ExtensionFieldPolyContinuingAccessor<F, E>
{
    const SHOULD_ACCESS_TO_PREPARE_FOR_NEXT_STEP: bool = true;
    type Representation = sumcheck_common::representation::ext::ExtensionFieldRepresentation<F, E>;

    #[inline(always)]
    fn get_at_index<const ASSUME_PREFOLDED: bool>(
        &self,
        index: usize,
    ) -> sumcheck_common::representation::ext::ExtensionFieldRepresentation<F, E> {
        assert!(index < self.next_layer_size * 2);
        assert!(index < self.this_layer_size);
        unsafe {
            if ASSUME_PREFOLDED == false {
                // recompute corresponding input from the previous layer

                let f00 = self.previous_layer_start.add(index).read();
                let f01 = self
                    .previous_layer_start
                    .add(self.this_layer_size + index)
                    .read();

                let f0_c0 = f00;
                let mut f0_c1 = f01;
                f0_c1.sub_assign(&f00);
                let mut f0 = self.folding_challenge;
                f0.mul_assign(&f0_c1);
                f0.add_assign(&f0_c0);

                // write down
                self.this_layer_start.add(index).write(f0);

                sumcheck_common::representation::ext::ExtensionFieldRepresentation::new(f0)
            } else {
                let f0 = self.this_layer_start.add(index).read();
                sumcheck_common::representation::ext::ExtensionFieldRepresentation::new(f0)
            }
        }
    }
    #[inline(always)]
    fn get_f0_and_f1<const ASSUME_PREFOLDED: bool>(
        &self,
        index: usize,
    ) -> [sumcheck_common::representation::ext::ExtensionFieldRepresentation<F, E>; 2] {
        // just read and do NOT cache f1 - f0
        assert!(
            index < self.next_layer_size,
            "tried to access index {} for poly of size {}",
            index,
            self.next_layer_size * 2
        );

        [
            self.get_at_index::<ASSUME_PREFOLDED>(index),
            self.get_at_index::<ASSUME_PREFOLDED>(self.next_layer_size + index),
        ]
    }
}

impl<'a, F: PrimeField, E: FieldExtension<F> + Field>
    sumcheck_common::representation::SumcheckRoundSource<F, E> for SumcheckRound1Source<'a, F, E>
{
    type BaseFieldInput =
        sumcheck_common::representation::once_folded::BaseFieldFoldedOnceRepresentation<F>;
    type BaseInputAccessor = BaseFieldPolyAccessorAfterOneFolding<F>;

    type ExtFieldInput = sumcheck_common::representation::ext::ExtensionFieldRepresentation<F, E>;
    type ExtInputAccessor = ExtensionFieldPolyContinuingAccessor<F, E>;

    fn base_field_input_ctx(
        &self,
    ) -> <Self::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX {
        self.first_folding_challenge_and_squared
    }
    fn ext_field_input_ctx(
        &self,
    ) -> <Self::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX {
        ()
    }
    fn get_source_for_base_poly(&mut self, address: GKRAddress) -> Self::BaseInputAccessor {
        debug_assert_eq!(self.folding_challenges.len(), 1);
        let challenges = [self.folding_challenges[0]];
        let base_field_poly = self
            .storage
            .make_base_source_for_round_1(address, &challenges);
        BaseFieldPolyAccessorAfterOneFolding {
            base_input_start: base_field_poly.base_input_start,
            base_layer_half_size: base_field_poly.base_layer_half_size,
            next_layer_size: base_field_poly.next_layer_size,
        }
    }
    fn get_source_for_ext_poly(&mut self, address: GKRAddress) -> Self::ExtInputAccessor {
        debug_assert_eq!(self.folding_challenges.len(), 1);
        let challenges = [self.folding_challenges[0]];
        let ext_field_poly = self
            .storage
            .make_ext_source_for_rounds_1_and_beyond(address, &challenges);
        ExtensionFieldPolyContinuingAccessor {
            previous_layer_start: ext_field_poly.previous_layer_start,
            this_layer_start: ext_field_poly.this_layer_start,
            this_layer_size: ext_field_poly.this_layer_size,
            next_layer_size: ext_field_poly.next_layer_size,
            folding_challenge: ext_field_poly.folding_challenge,
            _marker: core::marker::PhantomData,
        }
    }
}

// sumcheck round 2

pub struct SumcheckRound2Source<'a, F: PrimeField, E: FieldExtension<F> + Field> {
    storage: &'a mut GKRStorage<F, E>,
    folding_challenges: Vec<E>,
}

#[derive(Debug)]
pub struct BaseFieldPolyAccessorAfterTwoFoldings<F: PrimeField, E: FieldExtension<F> + Field> {
    pub(crate) base_input_start: *const F,
    pub(crate) this_layer_cache_start: *mut E,
    pub(crate) base_layer_half_size: usize,
    pub(crate) base_quarter_size: usize,
    pub(crate) next_layer_size: usize,
    pub(crate) first_folding_challenge: E,
    pub(crate) second_folding_challenge: E,
    pub(crate) combined_challenges: E, // r1 * r2, precomputed to avoid E×E at get_at_index time
}

impl<F: PrimeField, E: FieldExtension<F> + Field> BaseFieldPolyAccessorAfterTwoFoldings<F, E> {
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
}

unsafe impl<F: PrimeField, E: FieldExtension<F> + Field> Send
    for BaseFieldPolyAccessorAfterTwoFoldings<F, E>
{
}
unsafe impl<F: PrimeField, E: FieldExtension<F> + Field> Sync
    for BaseFieldPolyAccessorAfterTwoFoldings<F, E>
{
}

impl<F: PrimeField, E: FieldExtension<F> + Field>
    sumcheck_common::representation::PolyAccessor<F, E>
    for BaseFieldPolyAccessorAfterTwoFoldings<F, E>
{
    const SHOULD_ACCESS_TO_PREPARE_FOR_NEXT_STEP: bool = true;
    type Representation = sumcheck_common::representation::ext::ExtensionFieldRepresentation<F, E>;

    #[inline(always)]
    fn get_at_index<const ASSUME_PREFOLDED: bool>(
        &self,
        index: usize,
    ) -> sumcheck_common::representation::ext::ExtensionFieldRepresentation<F, E> {
        assert!(index < self.next_layer_size * 2);
        // fold two times
        unsafe {
            if ASSUME_PREFOLDED == false {
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

                sumcheck_common::representation::ext::ExtensionFieldRepresentation::<F, E>::new(
                    result,
                )
            } else {
                let result = self.this_layer_cache_start.add(index).read();
                sumcheck_common::representation::ext::ExtensionFieldRepresentation::<F, E>::new(
                    result,
                )
            }
        }
    }

    #[inline(always)]
    fn get_f0_and_f1<const ASSUME_PREFOLDED: bool>(
        &self,
        index: usize,
    ) -> [sumcheck_common::representation::ext::ExtensionFieldRepresentation<F, E>; 2] {
        // just read and do NOT cache f1 - f0
        assert!(index < self.next_layer_size);
        [
            self.get_at_index::<ASSUME_PREFOLDED>(index),
            self.get_at_index::<ASSUME_PREFOLDED>(self.next_layer_size + index),
        ]
    }
}

impl<'a, F: PrimeField, E: FieldExtension<F> + Field>
    sumcheck_common::representation::SumcheckRoundSource<F, E> for SumcheckRound2Source<'a, F, E>
{
    type BaseFieldInput = sumcheck_common::representation::ext::ExtensionFieldRepresentation<F, E>;
    type BaseInputAccessor = BaseFieldPolyAccessorAfterTwoFoldings<F, E>;

    type ExtFieldInput = sumcheck_common::representation::ext::ExtensionFieldRepresentation<F, E>;
    type ExtInputAccessor = ExtensionFieldPolyContinuingAccessor<F, E>;

    fn base_field_input_ctx(
        &self,
    ) -> <Self::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX {
        ()
    }
    fn ext_field_input_ctx(
        &self,
    ) -> <Self::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX {
        ()
    }
    fn get_source_for_base_poly(&mut self, address: GKRAddress) -> Self::BaseInputAccessor {
        debug_assert_eq!(self.folding_challenges.len(), 2);
        let challenges = [self.folding_challenges[0], self.folding_challenges[1]];
        let base_field_poly = self
            .storage
            .make_base_source_for_round_2(address, &challenges);
        BaseFieldPolyAccessorAfterTwoFoldings {
            base_input_start: base_field_poly.base_input_start,
            this_layer_cache_start: base_field_poly.this_layer_cache_start,
            base_layer_half_size: base_field_poly.base_layer_half_size,
            base_quarter_size: base_field_poly.base_quarter_size,
            next_layer_size: base_field_poly.next_layer_size,
            first_folding_challenge: base_field_poly.first_folding_challenge,
            second_folding_challenge: base_field_poly.second_folding_challenge,
            combined_challenges: base_field_poly.combined_challenges,
        }
    }
    fn get_source_for_ext_poly(&mut self, address: GKRAddress) -> Self::ExtInputAccessor {
        debug_assert_eq!(self.folding_challenges.len(), 2);
        let challenges = [self.folding_challenges[0], self.folding_challenges[1]];
        let ext_field_poly = self
            .storage
            .make_ext_source_for_rounds_1_and_beyond(address, &challenges);
        ExtensionFieldPolyContinuingAccessor {
            previous_layer_start: ext_field_poly.previous_layer_start,
            this_layer_start: ext_field_poly.this_layer_start,
            this_layer_size: ext_field_poly.this_layer_size,
            next_layer_size: ext_field_poly.next_layer_size,
            folding_challenge: ext_field_poly.folding_challenge,
            _marker: core::marker::PhantomData,
        }
    }
}

// sumcheck round 3 and beyond

pub struct SumcheckRound3AndBeyondSource<'a, F: PrimeField, E: FieldExtension<F> + Field> {
    storage: &'a mut GKRStorage<F, E>,
    folding_challenges: Vec<E>,
}

impl<'a, F: PrimeField, E: FieldExtension<F> + Field>
    sumcheck_common::representation::SumcheckRoundSource<F, E>
    for SumcheckRound3AndBeyondSource<'a, F, E>
{
    type BaseFieldInput = sumcheck_common::representation::ext::ExtensionFieldRepresentation<F, E>;
    type BaseInputAccessor = ExtensionFieldPolyContinuingAccessor<F, E>;

    type ExtFieldInput = sumcheck_common::representation::ext::ExtensionFieldRepresentation<F, E>;
    type ExtInputAccessor = ExtensionFieldPolyContinuingAccessor<F, E>;

    fn base_field_input_ctx(
        &self,
    ) -> <Self::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX {
        ()
    }
    fn ext_field_input_ctx(
        &self,
    ) -> <Self::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX {
        ()
    }
    fn get_source_for_base_poly(&mut self, address: GKRAddress) -> Self::BaseInputAccessor {
        debug_assert!(self.folding_challenges.len() >= 3);
        let challenges = self.folding_challenges.clone();
        let base_field_poly = self
            .storage
            .make_base_source_for_rounds_3_and_beyond(address, &challenges);
        ExtensionFieldPolyContinuingAccessor {
            previous_layer_start: base_field_poly.previous_layer_start,
            this_layer_start: base_field_poly.this_layer_start,
            this_layer_size: base_field_poly.this_layer_size,
            next_layer_size: base_field_poly.next_layer_size,
            folding_challenge: base_field_poly.folding_challenge,
            _marker: core::marker::PhantomData,
        }
    }
    fn get_source_for_ext_poly(&mut self, address: GKRAddress) -> Self::ExtInputAccessor {
        debug_assert!(self.folding_challenges.len() >= 3);
        let challenges = self.folding_challenges.clone();
        let ext_field_poly = self
            .storage
            .make_ext_source_for_rounds_1_and_beyond(address, &challenges);
        ExtensionFieldPolyContinuingAccessor {
            previous_layer_start: ext_field_poly.previous_layer_start,
            this_layer_start: ext_field_poly.this_layer_start,
            this_layer_size: ext_field_poly.this_layer_size,
            next_layer_size: ext_field_poly.next_layer_size,
            folding_challenge: ext_field_poly.folding_challenge,
            _marker: core::marker::PhantomData,
        }
    }
}
