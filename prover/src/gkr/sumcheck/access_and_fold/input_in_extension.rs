use super::*;

pub struct ExtensionFieldPoly<F: PrimeField, E: FieldExtension<F> + Field> {
    pub(crate) values: Box<[E]>,
    pub(crate) _marker: core::marker::PhantomData<F>,
}

impl<F: PrimeField, E: FieldExtension<F> + Field> ExtensionFieldPoly<F, E> {
    pub fn new(values: Box<[E]>) -> Self {
        assert!(values.len().is_power_of_two());
        Self {
            values,
            _marker: core::marker::PhantomData,
        }
    }

    pub fn accessor(&self) -> ExtensionFieldPolyInitialSource<F, E> {
        ExtensionFieldPolyInitialSource {
            start: self.values.as_ptr(),
            next_layer_size: self.values.len() / 2,
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
}

impl<F: PrimeField, E: FieldExtension<F> + Field>
    EvaluationFormStorage<F, E, ExtensionFieldRepresentation<F, E>>
    for ExtensionFieldPolyInitialSource<F, E>
{
    const SHOULD_ACCESS_TO_PREPARE_FOR_NEXT_STEP: bool = false;

    fn dummy() -> Self {
        todo!();
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
        debug_assert!(index < self.next_layer_size * 2);
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
        // just read and do NOT cache f1 - f0
        debug_assert!(index < self.next_layer_size);
        [
            self.get_at_index(index),
            self.get_at_index(self.next_layer_size + index),
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
        let buffer_size = size_after_one_fold * 2; // coarse
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

    pub fn pointer_for_sumcheck_continuation(&mut self, step: usize) -> (*mut E, *mut E) {
        unsafe {
            assert!(step >= 2);
            let mut input_offset = self.continuous_buffer.as_mut_ptr();
            let mut input_size = self.size_after_one_fold;
            let mut next_step_offset = input_offset.add(input_size);
            debug_assert!(input_offset >= self.continuous_buffer.as_mut_ptr_range().start);
            debug_assert!(input_offset < self.continuous_buffer.as_mut_ptr_range().end);
            debug_assert!(next_step_offset > self.continuous_buffer.as_mut_ptr_range().start);
            debug_assert!(next_step_offset < self.continuous_buffer.as_mut_ptr_range().end);
            for _ in 2..step {
                input_offset = next_step_offset;
                input_size /= 2;
                debug_assert!(input_size > 0);
                next_step_offset = next_step_offset.add(input_size);
                debug_assert!(input_offset >= self.continuous_buffer.as_mut_ptr_range().start);
                debug_assert!(input_offset < self.continuous_buffer.as_mut_ptr_range().end);
                debug_assert!(next_step_offset > self.continuous_buffer.as_mut_ptr_range().start);
                debug_assert!(next_step_offset < self.continuous_buffer.as_mut_ptr_range().end);
            }

            (input_offset.cast(), next_step_offset.cast())
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
    EvaluationFormStorage<F, E, ExtensionFieldRepresentation<F, E>>
    for ExtensionFieldPolyContinuingSource<F, E>
{
    const SHOULD_ACCESS_TO_PREPARE_FOR_NEXT_STEP: bool = true;

    fn dummy() -> Self {
        todo!();
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
        debug_assert!(index < self.next_layer_size * 2);
        unsafe {
            if self.first_access {
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
        debug_assert!(index < self.next_layer_size);
        unsafe {
            if self.first_access {
                // recompute corresponding input from the previous layer

                // these fold to f0 of this layer
                let f00 = self.previous_layer_start.add(index).read();
                let f01 = self
                    .previous_layer_start
                    .add(self.this_layer_size + index)
                    .read();

                // these fold to f1 of this layer
                let f10 = self
                    .previous_layer_start
                    .add(self.next_layer_size + index)
                    .read();
                let f11 = self
                    .previous_layer_start
                    .add(self.this_layer_size + self.next_layer_size + index)
                    .read();

                let f0_c0 = f00;
                let mut f0_c1 = f01;
                f0_c1.sub_assign(&f00);
                let mut f0 = self.folding_challenge;
                f0.mul_assign(&f0_c1);
                f0.add_assign(&f0_c0);

                let f1_c0 = f10;
                let mut f1_c1 = f11;
                f1_c1.sub_assign(&f10);
                let mut f1 = self.folding_challenge;
                f1.mul_assign(&f1_c1);
                f1.add_assign(&f1_c0);

                // write down
                self.this_layer_start.add(index).write(f0);
                self.this_layer_start
                    .add(self.next_layer_size + index)
                    .write(f1);

                [
                    ExtensionFieldRepresentation {
                        value: f0,
                        _marker: core::marker::PhantomData,
                    },
                    ExtensionFieldRepresentation {
                        value: f1,
                        _marker: core::marker::PhantomData,
                    },
                ]
            } else {
                let f0 = self.this_layer_start.add(index).read();
                let f1 = self
                    .this_layer_start
                    .add(self.next_layer_size + index)
                    .read();

                [
                    ExtensionFieldRepresentation {
                        value: f0,
                        _marker: core::marker::PhantomData,
                    },
                    ExtensionFieldRepresentation {
                        value: f1,
                        _marker: core::marker::PhantomData,
                    },
                ]
            }
        }
    }
}
