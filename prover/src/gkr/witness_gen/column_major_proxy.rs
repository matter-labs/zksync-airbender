use crate::gkr::witness_gen::witness_proxy::WitnessProxy;
use common_constants::NUM_TIMESTAMP_COLUMNS_FOR_RAM;
use cs::definitions::timestamp_scalar_into_column_values;
use cs::oracle::*;
use cs::tables::TableDriver;
use cs::utils::split_u32_into_pair_u16;
use cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;
use field::{Mersenne31Field, PrimeField};

// NOTE: very unsafe

pub struct ColumnMajorWitnessProxy<'a, O: Oracle<F> + 'a, F: PrimeField = Mersenne31Field> {
    pub(crate) witness_rows_starts: Box<[*mut F]>,
    pub(crate) memory_rows_starts: Box<[*mut F]>,
    pub(crate) scratch_space: Box<[*mut F]>,
    pub(crate) table_driver: &'a TableDriver<F>,
    pub(crate) multiplicity_counting_scratch: &'a mut [u32],
    pub(crate) lookup_mapping_rows_starts: Box<[*mut u32]>,
    pub(crate) oracle: &'a O,
    pub(crate) absolute_row_idx: usize,
}

unsafe impl<'a, O: Oracle<F> + 'a, F: PrimeField> Send for ColumnMajorWitnessProxy<'a, O, F> {}
unsafe impl<'a, O: Oracle<F> + 'a, F: PrimeField> Sync for ColumnMajorWitnessProxy<'a, O, F> {}

impl<'a, O: Oracle<F> + 'a, F: PrimeField> ColumnMajorWitnessProxy<'a, O, F> {
    pub(crate) unsafe fn advance(&mut self) {
        for el in self.memory_rows_starts.iter_mut() {
            *el = el.add(1);
        }
        for el in self.witness_rows_starts.iter_mut() {
            *el = el.add(1);
        }
        for el in self.scratch_space.iter_mut() {
            *el = el.add(1);
        }
        for el in self.lookup_mapping_rows_starts.iter_mut() {
            *el = el.add(1);
        }
        self.absolute_row_idx += 1;
    }

    #[inline]
    pub(crate) fn write_timestamp_placeholder_into_columns(
        &mut self,
        placeholder_columns: [usize; NUM_TIMESTAMP_COLUMNS_FOR_RAM],
        placeholder_type: Placeholder,
    ) {
        let value = Oracle::<F>::get_timestamp_witness_from_placeholder(
            self.oracle,
            placeholder_type,
            self.absolute_row_idx,
        );

        self.write_timestamp_value_into_columns(placeholder_columns, value);
    }

    #[inline]
    pub(crate) fn write_timestamp_value_into_columns(
        &mut self,
        placeholder_columns: [usize; NUM_TIMESTAMP_COLUMNS_FOR_RAM],
        value: u64,
    ) {
        let [offset_low, offset_high] = placeholder_columns;
        debug_assert!(offset_low < self.memory_rows_starts.len());
        debug_assert!(offset_high < self.memory_rows_starts.len());

        let [low, high] = timestamp_scalar_into_column_values(value);
        unsafe {
            self.memory_rows_starts
                .get_unchecked_mut(offset_low)
                .write(F::from_u32_unchecked(low as u32));
            self.memory_rows_starts
                .get_unchecked_mut(offset_high)
                .write(F::from_u32_unchecked(high as u32));
        }
    }

    #[inline]
    pub(crate) fn write_u32_placeholder_into_columns<const USE_MEMORY: bool>(
        &mut self,
        placeholder_columns: [usize; 2],
        placeholder_type: Placeholder,
    ) {
        let value = Oracle::<F>::get_u32_witness_from_placeholder(
            self.oracle,
            placeholder_type,
            self.absolute_row_idx,
        );

        self.write_u32_value_into_columns::<USE_MEMORY>(placeholder_columns, value);
    }

    #[inline]
    pub(crate) fn write_u32_value_into_columns<const USE_MEMORY: bool>(
        &mut self,
        placeholder_columns: [usize; 2],
        value: u32,
    ) {
        let [offset_low, offset_high] = placeholder_columns;
        let (low, high) = split_u32_into_pair_u16(value);

        // if USE_MEMORY == false && self.absolute_row_idx == 0 && (offset_low == 0 || offset_high == 0) {
        //     panic!("debug");
        // }

        if USE_MEMORY {
            debug_assert!(offset_low < self.memory_rows_starts.len());
            debug_assert!(offset_high < self.memory_rows_starts.len());

            unsafe {
                self.memory_rows_starts
                    .get_unchecked_mut(offset_low)
                    .write(F::from_u32_unchecked(low as u32));
                self.memory_rows_starts
                    .get_unchecked_mut(offset_high)
                    .write(F::from_u32_unchecked(high as u32));
            }
        } else {
            debug_assert!(offset_low < self.witness_rows_starts.len());
            debug_assert!(offset_high < self.witness_rows_starts.len());

            unsafe {
                self.witness_rows_starts
                    .get_unchecked_mut(offset_low)
                    .write(F::from_u32_unchecked(low as u32));
                self.witness_rows_starts
                    .get_unchecked_mut(offset_high)
                    .write(F::from_u32_unchecked(high as u32));
            }
        }
    }

    #[inline]
    pub(crate) fn read_u32_value_from_columns<const USE_MEMORY: bool>(
        &self,
        placeholder_columns: [usize; 2],
    ) -> u32 {
        let [offset_low, offset_high] = placeholder_columns;

        let (low, high) = if USE_MEMORY {
            debug_assert!(offset_low < self.memory_rows_starts.len());
            debug_assert!(offset_high < self.memory_rows_starts.len());

            unsafe {
                (
                    self.memory_rows_starts
                        .get_unchecked(offset_low)
                        .read()
                        .as_u32_reduced(),
                    self.memory_rows_starts
                        .get_unchecked(offset_high)
                        .read()
                        .as_u32_reduced(),
                )
            }
        } else {
            debug_assert!(offset_low < self.witness_rows_starts.len());
            debug_assert!(offset_high < self.witness_rows_starts.len());

            unsafe {
                (
                    self.witness_rows_starts
                        .get_unchecked(offset_low)
                        .read()
                        .as_u32_reduced(),
                    self.witness_rows_starts
                        .get_unchecked(offset_high)
                        .read()
                        .as_u32_reduced(),
                )
            }
        };

        debug_assert!(low < 1 << 16);
        debug_assert!(high < 1 << 16);

        (high << 16) | low
    }

    #[inline]
    pub(crate) fn write_u32_placeholder_as_u8_chunks_into_columns<const USE_MEMORY: bool>(
        &mut self,
        placeholder_columns: [usize; 4],
        placeholder_type: Placeholder,
    ) {
        let value = Oracle::<F>::get_u32_witness_from_placeholder(
            self.oracle,
            placeholder_type,
            self.absolute_row_idx,
        );

        self.write_u32_value_as_u8_chunks_into_columns::<USE_MEMORY>(placeholder_columns, value);
    }

    #[inline]
    pub(crate) fn write_u32_value_as_u8_chunks_into_columns<const USE_MEMORY: bool>(
        &mut self,
        placeholder_columns: [usize; 4],
        value: u32,
    ) {
        let bytes = value.to_le_bytes();

        if USE_MEMORY {
            for el in placeholder_columns.iter() {
                debug_assert!(*el < self.memory_rows_starts.len());
            }

            for (value, offset) in bytes.into_iter().zip(placeholder_columns.into_iter()) {
                unsafe {
                    self.memory_rows_starts
                        .get_unchecked_mut(offset)
                        .write(F::from_u32_unchecked(value as u32));
                }
            }
        } else {
            for el in placeholder_columns.iter() {
                debug_assert!(*el < self.witness_rows_starts.len());
            }

            for (value, offset) in bytes.into_iter().zip(placeholder_columns.into_iter()) {
                unsafe {
                    self.witness_rows_starts
                        .get_unchecked_mut(offset)
                        .write(F::from_u32_unchecked(value as u32));
                }
            }
        }
    }

    #[inline]
    pub(crate) fn write_u16_placeholder_into_columns<const USE_MEMORY: bool>(
        &mut self,
        placeholder_columns: usize,
        placeholder_type: Placeholder,
    ) {
        let value = Oracle::<F>::get_u16_witness_from_placeholder(
            self.oracle,
            placeholder_type,
            self.absolute_row_idx,
        );

        self.write_u16_value_into_columns::<USE_MEMORY>(placeholder_columns, value);
    }

    #[inline]
    pub(crate) fn write_u16_value_into_columns<const USE_MEMORY: bool>(
        &mut self,
        column: usize,
        value: u16,
    ) {
        // if USE_MEMORY == false && self.absolute_row_idx == 0 && column == 0 {
        //     panic!("debug");
        // }

        if USE_MEMORY {
            debug_assert!(column < self.memory_rows_starts.len());
            unsafe {
                self.memory_rows_starts
                    .get_unchecked_mut(column)
                    .write(F::from_u32_unchecked(value as u32));
            }
        } else {
            debug_assert!(column < self.witness_rows_starts.len());
            unsafe {
                self.witness_rows_starts
                    .get_unchecked_mut(column)
                    .write(F::from_u32_unchecked(value as u32));
            }
        }
    }

    #[inline]
    pub(crate) fn write_u8_placeholder_into_columns<const USE_MEMORY: bool>(
        &mut self,
        placeholder_columns: usize,
        placeholder_type: Placeholder,
    ) {
        let value = Oracle::<F>::get_u8_witness_from_placeholder(
            self.oracle,
            placeholder_type,
            self.absolute_row_idx,
        );

        self.write_u8_value_into_columns::<USE_MEMORY>(placeholder_columns, value);
    }

    #[inline]
    pub(crate) fn write_u8_value_into_columns<const USE_MEMORY: bool>(
        &mut self,
        column: usize,
        value: u8,
    ) {
        // if USE_MEMORY == false && self.absolute_row_idx == 0 && column == 0 {
        //     panic!("debug");
        // }

        if USE_MEMORY {
            debug_assert!(column < self.memory_rows_starts.len());
            unsafe {
                self.memory_rows_starts
                    .get_unchecked_mut(column)
                    .write(F::from_u32_unchecked(value as u32));
            }
        } else {
            debug_assert!(column < self.witness_rows_starts.len());
            unsafe {
                self.witness_rows_starts
                    .get_unchecked_mut(column)
                    .write(F::from_u32_unchecked(value as u32));
            }
        }
    }

    #[inline]
    pub(crate) fn write_boolean_placeholder_into_columns<const USE_MEMORY: bool>(
        &mut self,
        placeholder_columns: usize,
        placeholder_type: Placeholder,
    ) {
        let value = Oracle::<F>::get_boolean_witness_from_placeholder(
            self.oracle,
            placeholder_type,
            self.absolute_row_idx,
        );

        self.write_boolean_value_into_columns::<USE_MEMORY>(placeholder_columns, value);
    }

    #[inline]
    pub(crate) fn write_boolean_value_into_columns<const USE_MEMORY: bool>(
        &mut self,
        column: usize,
        value: bool,
    ) {
        // if USE_MEMORY == false && self.absolute_row_idx == 0 && column == 0 {
        //     panic!("debug");
        // }

        if USE_MEMORY {
            debug_assert!(column < self.memory_rows_starts.len());
            unsafe {
                self.memory_rows_starts
                    .get_unchecked_mut(column)
                    .write(F::from_boolean(value));
            }
        } else {
            debug_assert!(column < self.witness_rows_starts.len());
            unsafe {
                self.witness_rows_starts
                    .get_unchecked_mut(column)
                    .write(F::from_boolean(value));
            }
        }
    }

    #[inline]
    pub(crate) fn write_field_value_into_columns<const USE_MEMORY: bool>(
        &mut self,
        column: usize,
        value: F,
    ) {
        // if USE_MEMORY == false && self.absolute_row_idx == 0 && column == 0 {
        //     panic!("debug");
        // }

        if USE_MEMORY {
            debug_assert!(column < self.memory_rows_starts.len());
            unsafe {
                self.memory_rows_starts
                    .get_unchecked_mut(column)
                    .write(value);
            }
        } else {
            debug_assert!(column < self.witness_rows_starts.len());
            unsafe {
                self.witness_rows_starts
                    .get_unchecked_mut(column)
                    .write(value);
            }
        }
    }
}

impl<'a, O: Oracle<F> + 'a, F: PrimeField> WitnessProxy<F, ScalarWitnessTypeSet<F, true>>
    for ColumnMajorWitnessProxy<'a, O, F>
{
    #[inline(always)]
    fn get_memory_place(&self, idx: usize) -> F {
        debug_assert!(idx < self.memory_rows_starts.len());
        unsafe { self.memory_rows_starts.get_unchecked(idx).read() }
    }

    #[inline(always)]
    fn get_witness_place(&self, idx: usize) -> F {
        debug_assert!(idx < self.witness_rows_starts.len());
        unsafe { self.witness_rows_starts.get_unchecked(idx).read() }
    }

    #[inline(always)]
    fn get_scratch_place(&self, idx: usize) -> F {
        debug_assert!(idx < self.scratch_space.len());
        unsafe { self.scratch_space.get_unchecked(idx).read() }
    }

    #[inline(always)]
    fn get_oracle_value(&self, placeholder: Placeholder, subindex: usize) -> F {
        self.oracle
            .get_witness_from_placeholder(placeholder, subindex, self.absolute_row_idx)
    }

    #[inline(always)]
    fn get_oracle_value_u32(&self, placeholder: Placeholder) -> u32 {
        self.oracle
            .get_u32_witness_from_placeholder(placeholder, self.absolute_row_idx)
    }

    #[inline(always)]
    fn get_oracle_value_u16(&self, placeholder: Placeholder) -> u16 {
        self.oracle
            .get_u16_witness_from_placeholder(placeholder, self.absolute_row_idx)
    }

    #[inline(always)]
    fn get_oracle_value_u8(&self, placeholder: Placeholder) -> u8 {
        self.oracle
            .get_u8_witness_from_placeholder(placeholder, self.absolute_row_idx)
    }

    #[inline(always)]
    fn get_oracle_value_boolean(&self, placeholder: Placeholder) -> bool {
        self.oracle
            .get_boolean_witness_from_placeholder(placeholder, self.absolute_row_idx)
    }

    #[inline(always)]
    fn set_memory_place(&mut self, idx: usize, value: F) {
        debug_assert!(
            idx < self.memory_rows_starts.len(),
            "trying to access memory column {}, while only {} columns exist",
            idx,
            self.memory_rows_starts.len()
        );
        unsafe {
            self.memory_rows_starts.get_unchecked_mut(idx).write(value);
        }
    }

    #[inline(always)]
    fn set_witness_place(&mut self, idx: usize, value: F) {
        debug_assert!(
            idx < self.witness_rows_starts.len(),
            "trying to access witness column {}, while only {} columns exist",
            idx,
            self.witness_rows_starts.len()
        );
        unsafe {
            self.witness_rows_starts.get_unchecked_mut(idx).write(value);
        }
    }

    #[inline(always)]
    fn set_scratch_place(&mut self, idx: usize, value: F) {
        debug_assert!(
            idx < self.scratch_space.len(),
            "trying to access scratch space column {}, while only {} columns exist",
            idx,
            self.scratch_space.len()
        );

        unsafe {
            self.scratch_space.get_unchecked_mut(idx).write(value);
        }
    }

    #[inline(always)]
    fn lookup<const M: usize, const N: usize>(
        &mut self,
        inputs: &[F; M],
        table_id: u16,
        lookup_mapping_idx: usize,
    ) -> [F; N] {
        let (absolute_index, values) = self
            .table_driver
            .lookup_values_and_get_absolute_index::<N>(inputs, table_id as u32);

        debug_assert!(
            absolute_index < self.multiplicity_counting_scratch.len(),
            "absolute table index from lookup is {}, but total expected tables length is {}",
            absolute_index,
            self.multiplicity_counting_scratch.len()
        );
        debug_assert!(
            lookup_mapping_idx < self.lookup_mapping_rows_starts.len(),
            "lookup mapping idx is {}, but in total only {} lookup mappings exist",
            lookup_mapping_idx,
            self.lookup_mapping_rows_starts.len()
        );

        unsafe {
            *self
                .multiplicity_counting_scratch
                .get_unchecked_mut(absolute_index) += 1;
            // assert_eq!(self.lookup_mapping_row[lookup_mapping_idx], 0);
            self.lookup_mapping_rows_starts
                .get_unchecked_mut(lookup_mapping_idx)
                .write(absolute_index as u32);
        }

        values
    }

    #[inline(always)]
    fn maybe_lookup<const M: usize, const N: usize>(
        &mut self,
        inputs: &[F; M],
        table_id: u16,
        condition: bool,
    ) -> [F; N] {
        if condition {
            let (_absolute_index, values) = self
                .table_driver
                .lookup_values_and_get_absolute_index::<N>(inputs, table_id as u32);
            // we do not need to count multiplicity here
            values
        } else {
            [F::ZERO; N]
        }
    }

    #[inline(always)]
    fn lookup_enforce<const M: usize>(
        &mut self,
        inputs: &[F; M],
        table_id: u16,
        lookup_mapping_idx: usize,
    ) {
        let absolute_index = self
            .table_driver
            .enforce_values_and_get_absolute_index::<M>(inputs, table_id as u32);

        debug_assert!(
            absolute_index < self.multiplicity_counting_scratch.len(),
            "absolute table index from lookup is {}, but total expected tables length is {}",
            absolute_index,
            self.multiplicity_counting_scratch.len()
        );
        debug_assert!(
            lookup_mapping_idx < self.lookup_mapping_rows_starts.len(),
            "lookup mapping idx is {}, but in total only {} lookup mappings exist",
            lookup_mapping_idx,
            self.lookup_mapping_rows_starts.len()
        );

        unsafe {
            *self
                .multiplicity_counting_scratch
                .get_unchecked_mut(absolute_index) += 1;
            // assert_eq!(self.lookup_mapping_row[lookup_mapping_idx], 0);
            self.lookup_mapping_rows_starts
                .get_unchecked_mut(lookup_mapping_idx)
                .write(absolute_index as u32);
        }
    }
}
