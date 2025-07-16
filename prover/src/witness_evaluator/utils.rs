use super::*;

#[inline(always)]
pub(crate) fn lookup_index_into_encoding_tuple(
    lookup_row: usize,
    lookup_encoding_capacity: usize,
) -> (u32, u32) {
    let column = lookup_row / lookup_encoding_capacity;
    let row = lookup_row % lookup_encoding_capacity;

    (column as u32, row as u32)
}

#[inline(always)]
pub(crate) fn encoding_tuple_into_lookup_index(
    column: u32,
    row: u32,
    lookup_encoding_capacity: usize,
) -> usize {
    let offset = (column as usize) * lookup_encoding_capacity;
    offset + (row as usize)
}

#[inline(always)]
pub(crate) fn write_boolean_placeholder_into_columns<O: Oracle<Mersenne31Field>>(
    placeholder_columns: ColumnSet<1>,
    placeholder_type: Placeholder,
    oracle: &O,
    columns_view: &mut [Mersenne31Field],
    trace_step: usize,
) {
    let value = Oracle::<Mersenne31Field>::get_boolean_witness_from_placeholder(
        oracle,
        placeholder_type,
        trace_step,
    );

    write_boolean_value_into_columns(placeholder_columns, value, columns_view);
}

#[inline(always)]
pub(crate) fn write_boolean_value_into_columns(
    placeholder_columns: ColumnSet<1>,
    value: bool,
    columns_view: &mut [Mersenne31Field],
) {
    let offset = placeholder_columns.start();

    debug_assert!(offset < columns_view.len());
    unsafe {
        *columns_view.get_unchecked_mut(offset) = Mersenne31Field(value as u32);
    }
}

#[inline(always)]
pub(crate) fn write_u8_placeholder_into_columns<O: Oracle<Mersenne31Field>>(
    placeholder_columns: ColumnSet<1>,
    placeholder_type: Placeholder,
    oracle: &O,
    columns_view: &mut [Mersenne31Field],
    trace_step: usize,
) {
    let value = Oracle::<Mersenne31Field>::get_u8_witness_from_placeholder(
        oracle,
        placeholder_type,
        trace_step,
    );

    write_u8_value_into_columns(placeholder_columns, value, columns_view);
}

#[inline(always)]
pub(crate) fn write_u8_value_into_columns(
    placeholder_columns: ColumnSet<1>,
    value: u8,
    columns_view: &mut [Mersenne31Field],
) {
    let offset = placeholder_columns.start();

    debug_assert!(offset < columns_view.len());
    unsafe {
        *columns_view.get_unchecked_mut(offset) = Mersenne31Field(value as u32);
    }
}

#[inline(always)]
pub(crate) fn write_u16_placeholder_into_columns<O: Oracle<Mersenne31Field>>(
    placeholder_columns: ColumnSet<1>,
    placeholder_type: Placeholder,
    oracle: &O,
    columns_view: &mut [Mersenne31Field],
    trace_step: usize,
) {
    let value = Oracle::<Mersenne31Field>::get_u16_witness_from_placeholder(
        oracle,
        placeholder_type,
        trace_step,
    );

    write_u16_value_into_columns(placeholder_columns, value, columns_view);
}

#[inline(always)]
pub(crate) fn write_u16_value_into_columns(
    placeholder_columns: ColumnSet<1>,
    value: u16,
    columns_view: &mut [Mersenne31Field],
) {
    let offset = placeholder_columns.start();

    debug_assert!(offset < columns_view.len());
    unsafe {
        *columns_view.get_unchecked_mut(offset) = Mersenne31Field(value as u32);
    }
}

#[inline(always)]
pub(crate) fn write_u32_placeholder_into_columns<O: Oracle<Mersenne31Field>>(
    placeholder_columns: ColumnSet<2>,
    placeholder_type: Placeholder,
    oracle: &O,
    columns_view: &mut [Mersenne31Field],
    trace_step: usize,
) {
    let value = Oracle::<Mersenne31Field>::get_u32_witness_from_placeholder(
        oracle,
        placeholder_type,
        trace_step,
    );

    write_u32_value_into_columns(placeholder_columns, value, columns_view);
}

#[inline(always)]
pub(crate) fn write_timestamp_placeholder_into_columns<O: Oracle<Mersenne31Field>>(
    placeholder_columns: ColumnSet<2>,
    placeholder_type: Placeholder,
    oracle: &O,
    columns_view: &mut [Mersenne31Field],
    trace_step: usize,
) {
    let value = Oracle::<Mersenne31Field>::get_timestamp_witness_from_placeholder(
        oracle,
        placeholder_type,
        trace_step,
    );

    write_timestamp_value_into_columns(placeholder_columns, value, columns_view);
}

#[inline(always)]
pub(crate) fn write_u32_value_into_columns(
    columns: ColumnSet<2>,
    value: u32,
    columns_view: &mut [Mersenne31Field],
) {
    let offset_low = columns.start();
    let offset_high = offset_low + 1;

    debug_assert!(offset_low < columns_view.len());
    debug_assert!(offset_high < columns_view.len());

    unsafe {
        *columns_view.get_unchecked_mut(offset_low) = Mersenne31Field(value & 0xffff);
        *columns_view.get_unchecked_mut(offset_high) = Mersenne31Field(value >> 16);
    }
}

#[inline(always)]
pub(crate) fn write_timestamp_value_into_columns(
    columns: ColumnSet<2>,
    value: TimestampScalar,
    columns_view: &mut [Mersenne31Field],
) {
    let offset_low = columns.start();
    let offset_high = offset_low + 1;

    debug_assert!(offset_low < columns_view.len());
    debug_assert!(offset_high < columns_view.len());

    let [low, high] = timestamp_scalar_into_column_values(value);
    unsafe {
        *columns_view.get_unchecked_mut(offset_low) = Mersenne31Field(low);
        *columns_view.get_unchecked_mut(offset_high) = Mersenne31Field(high);
    }
}
