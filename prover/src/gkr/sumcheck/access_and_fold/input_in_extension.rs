use super::*;

#[derive(Debug)]
pub struct ExtensionFieldPoly<F: PrimeField, E: FieldExtension<F> + Field> {
    pub(crate) values: Arc<crate::allocation_pool::AllocationType<E>>,
    pub(crate) _marker: core::marker::PhantomData<F>,
}

impl<F: PrimeField, E: FieldExtension<F> + Field> ExtensionFieldPoly<F, E> {
    pub fn new(values: Box<[E]>) -> Self {
        Self::from_allocation(crate::allocation_pool::AllocationType::Owned(values))
    }

    pub fn from_allocation(values: crate::allocation_pool::AllocationType<E>) -> Self {
        assert!(values.len().is_power_of_two());
        Self {
            values: Arc::new(values),
            _marker: core::marker::PhantomData,
        }
    }

    /// A pooled buffer whose window is fully written.
    ///
    /// # Safety
    /// Every element of the buffer's window must have been written.
    pub unsafe fn from_pooled(values: crate::allocation_pool::Buffer<E>) -> Self {
        Self::from_allocation(crate::allocation_pool::AllocationType::from_initialized(
            values,
        ))
    }

    pub fn accessor(&self) -> ExtensionFieldPolyInitialSource<F, E> {
        ExtensionFieldPolyInitialSource {
            start: self.values.as_ptr(),
            next_layer_size: self.values.len() / 2,
            _marker: core::marker::PhantomData,
        }
    }

    pub fn arc_clone(&self) -> Self {
        Self {
            values: Arc::clone(&self.values),
            _marker: core::marker::PhantomData,
        }
    }
}

#[derive(Debug)]
pub struct ExtensionFieldPolyInitialSource<F: PrimeField, E: FieldExtension<F> + Field> {
    pub(crate) start: *const E,
    pub(crate) next_layer_size: usize,
    pub(crate) _marker: core::marker::PhantomData<F>,
}

unsafe impl<F: PrimeField, E: FieldExtension<F> + Field> Send
    for ExtensionFieldPolyInitialSource<F, E>
{
}
unsafe impl<F: PrimeField, E: FieldExtension<F> + Field> Sync
    for ExtensionFieldPolyInitialSource<F, E>
{
}

impl<F: PrimeField, E: FieldExtension<F> + Field> ExtensionFieldPolyInitialSource<F, E> {
    pub(crate) fn current_values(&'_ self) -> &'_ [E] {
        unsafe { core::slice::from_raw_parts(self.start, self.next_layer_size * 2) }
    }

    pub(crate) fn empty() -> Self {
        Self {
            start: null_mut(),
            next_layer_size: 0,
            _marker: core::marker::PhantomData,
        }
    }
}

impl<F: PrimeField, E: FieldExtension<F> + Field>
    EvaluationFormStorage<F, E, ExtensionFieldRepresentation<F, E>>
    for ExtensionFieldPolyInitialSource<F, E>
{
    const SHOULD_ACCESS_TO_PREPARE_FOR_NEXT_STEP: bool = false;

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
        unsafe {
            let f0 = self.start.add(index).read();
            ExtensionFieldRepresentation {
                value: f0,
                _marker: core::marker::PhantomData,
            }
        }
    }
    #[inline(always)]
    fn get_f0_and_f1(&self, index: usize) -> [ExtensionFieldRepresentation<F, E>; 2] {
        // LSB binding: adjacent pairs; do NOT cache f1 - f0
        assert!(
            index < self.next_layer_size,
            "tried to access index {} for poly of size {}",
            index,
            self.next_layer_size * 2
        );
        [
            self.get_at_index(2 * index),
            self.get_at_index(2 * index + 1),
        ]
    }
}

pub struct ExtensionFieldPolyIntermediateFoldingStorage<F: PrimeField, E: FieldExtension<F> + Field>
{
    pub(crate) continuous_buffer: Box<[MaybeUninit<E>]>,
    pub(crate) size_after_one_fold: usize,
    pub(crate) _marker: core::marker::PhantomData<F>,
}

impl<F: PrimeField, E: FieldExtension<F> + Field>
    ExtensionFieldPolyIntermediateFoldingStorage<F, E>
{
    pub fn new_for_extension_poly_size(poly_size: usize) -> Self {
        assert!(poly_size.is_power_of_two());
        assert!(poly_size > 2);
        let size_after_one_fold = poly_size / 4;
        // Successive folded layers occupy disjoint, geometrically shrinking
        // regions: poly_size / 2 + poly_size / 4 + ... < poly_size.
        let buffer_size = size_after_one_fold * 4;
        let continuous_buffer = Box::new_uninit_slice(buffer_size);
        Self {
            continuous_buffer,
            size_after_one_fold,
            _marker: core::marker::PhantomData,
        }
    }

    pub fn pointer_for_sumcheck_after_one_fold(&mut self) -> *mut E {
        self.continuous_buffer.as_mut_ptr().cast()
    }

    #[track_caller]
    pub fn pointer_for_sumcheck_continuation(&mut self, step: usize) -> (*mut E, *mut E) {
        // Keep the previous layer immutable while folding. Parallel chunks
        // may finish in any order, and kernels may read an index repeatedly.
        assert!(step >= 2);
        unsafe {
            let mut input = self.continuous_buffer.as_mut_ptr().cast::<E>();
            let mut input_size = self.size_after_one_fold * 2;
            for _ in 2..step {
                input = input.add(input_size);
                input_size /= 2;
            }
            (input, input.add(input_size))
        }
    }
}

#[derive(Debug)]
pub struct ExtensionFieldPolyContinuingSource<F: PrimeField, E: FieldExtension<F> + Field> {
    pub(crate) previous_layer_start: *const E,
    pub(crate) this_layer_start: *mut E,
    pub(crate) this_layer_size: usize,
    pub(crate) next_layer_size: usize,
    pub(crate) folding_challenge: E,
    pub(crate) first_access: bool,
    pub(crate) _marker: core::marker::PhantomData<F>,
}

unsafe impl<F: PrimeField, E: FieldExtension<F> + Field> Send
    for ExtensionFieldPolyContinuingSource<F, E>
{
}
unsafe impl<F: PrimeField, E: FieldExtension<F> + Field> Sync
    for ExtensionFieldPolyContinuingSource<F, E>
{
}

impl<F: PrimeField, E: FieldExtension<F> + Field> ExtensionFieldPolyContinuingSource<F, E> {
    #[allow(dead_code)]
    pub(crate) fn previous_values(&'_ self) -> &'_ [E] {
        unsafe { core::slice::from_raw_parts(self.previous_layer_start, self.this_layer_size * 2) }
    }
    pub(crate) fn current_values(&'_ self) -> &'_ [E] {
        unsafe {
            core::slice::from_raw_parts(self.this_layer_start.cast_const(), self.this_layer_size)
        }
    }

    pub(crate) fn empty_with_folding_context(folding_challenge: E) -> Self {
        Self {
            previous_layer_start: null_mut(),
            this_layer_start: null_mut(),
            this_layer_size: 0,
            next_layer_size: 0,
            folding_challenge,
            first_access: false,
            _marker: core::marker::PhantomData,
        }
    }
}

impl<F: PrimeField, E: FieldExtension<F> + Field>
    EvaluationFormStorage<F, E, ExtensionFieldRepresentation<F, E>>
    for ExtensionFieldPolyContinuingSource<F, E>
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
        assert!(index < self.this_layer_size);
        unsafe {
            if self.first_access {
                // recompute corresponding input from the previous layer

                // LSB binding: adjacent pair of the previous layer
                let f00 = self.previous_layer_start.add(2 * index).read();
                let f01 = self.previous_layer_start.add(2 * index + 1).read();

                let f0_c0 = f00;
                let mut f0_c1 = f01;
                f0_c1.sub_assign(&f00);
                let mut f0 = self.folding_challenge;
                f0.mul_assign(&f0_c1);
                f0.add_assign(&f0_c0);

                // write down
                self.this_layer_start.add(index).write(f0);

                ExtensionFieldRepresentation {
                    value: f0,
                    _marker: core::marker::PhantomData,
                }
            } else {
                let f0 = self.this_layer_start.add(index).read();

                ExtensionFieldRepresentation {
                    value: f0,
                    _marker: core::marker::PhantomData,
                }
            }
        }
    }
    #[inline(always)]
    fn get_f0_and_f1(&self, index: usize) -> [ExtensionFieldRepresentation<F, E>; 2] {
        // just read and do NOT cache f1 - f0
        assert!(
            index < self.next_layer_size,
            "tried to access index {} for poly of size {}",
            index,
            self.next_layer_size * 2
        );

        [
            self.get_at_index(2 * index),
            self.get_at_index(2 * index + 1),
        ]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use field::Proth120;

    #[test]
    fn extension_folds_allow_reverse_chunk_order() {
        type P = Proth120;
        const POLY_SIZE: usize = 256;
        let mut buffer =
            ExtensionFieldPolyIntermediateFoldingStorage::<P, P>::new_for_extension_poly_size(
                POLY_SIZE,
            );
        let mut expected: Vec<_> = (0..POLY_SIZE / 2)
            .map(|i| P::from_u32_with_reduction((i * i + 7) as u32))
            .collect();
        // Materialize the first fold, as round 1 does before continuation.
        unsafe {
            buffer
                .pointer_for_sumcheck_after_one_fold()
                .copy_from_nonoverlapping(expected.as_ptr(), expected.len());
        }
        for step in 2..POLY_SIZE.ilog2() as usize {
            let challenge = P::from_u32_with_reduction(step as u32 + 11);
            expected = expected
                .as_chunks::<2>()
                .0
                .iter()
                .map(|pair| {
                    let mut value = pair[1];
                    value.sub_assign(&pair[0]);
                    value.mul_assign(&challenge);
                    value.add_assign(&pair[0]);
                    value
                })
                .collect();
            let (previous_layer_start, this_layer_start) =
                buffer.pointer_for_sumcheck_continuation(step);
            let source = ExtensionFieldPolyContinuingSource::<P, P> {
                previous_layer_start,
                this_layer_start,
                this_layer_size: expected.len(),
                next_layer_size: expected.len() / 2,
                folding_challenge: challenge,
                first_access: true,
                _marker: core::marker::PhantomData,
            };
            // Complete higher chunks first: a legal worker ordering, forced
            // serially to expose overwritten inputs without a data race in
            // the test itself or a dependency on OS scheduling.
            let chunk_size = expected.len().div_ceil(4);
            let starts: Vec<_> = (0..expected.len()).step_by(chunk_size).collect();
            for start in starts.into_iter().rev() {
                for i in start..(start + chunk_size).min(expected.len()) {
                    assert_eq!(
                        source.get_at_index(i).value,
                        expected[i],
                        "step {step}, index {i}"
                    );
                    assert_eq!(
                        source.get_at_index(i).value,
                        expected[i],
                        "repeated read at step {step}, index {i}"
                    );
                }
            }
            assert_eq!(source.current_values(), expected);
        }
    }
}
