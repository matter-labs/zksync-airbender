use super::*;

mod every_row_except_last;
mod every_row_except_last_two;
mod last_row_and_at_zero;

pub(crate) use self::every_row_except_last::*;
pub(crate) use self::every_row_except_last_two::*;
pub(crate) use self::last_row_and_at_zero::*;

pub(crate) fn add_boundary_constraints_from_memory_init_teardown(
    first_row_boundary_constraints: &mut Vec<(ColumnAddress, Mersenne31Field)>,
    one_before_last_row_boundary_constraints: &mut Vec<(ColumnAddress, Mersenne31Field)>,
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    aux_boundary_values: &[AuxArgumentsBoundaryValues],
) {
    assert_eq!(
        compiled_circuit
            .memory_layout
            .shuffle_ram_inits_and_teardowns
            .len(),
        aux_boundary_values.len()
    );
    for (values, set) in aux_boundary_values.iter().zip(
        compiled_circuit
            .memory_layout
            .shuffle_ram_inits_and_teardowns
            .iter(),
    ) {
        // first row
        {
            first_row_boundary_constraints.push((
                ColumnAddress::MemorySubtree(set.lazy_init_addresses_columns.start()),
                values.lazy_init_first_row[0],
            ));
            first_row_boundary_constraints.push((
                ColumnAddress::MemorySubtree(set.lazy_init_addresses_columns.start() + 1),
                values.lazy_init_first_row[1],
            ));

            first_row_boundary_constraints.push((
                ColumnAddress::MemorySubtree(set.lazy_teardown_values_columns.start()),
                values.teardown_value_first_row[0],
            ));
            first_row_boundary_constraints.push((
                ColumnAddress::MemorySubtree(set.lazy_teardown_values_columns.start() + 1),
                values.teardown_value_first_row[1],
            ));

            first_row_boundary_constraints.push((
                ColumnAddress::MemorySubtree(set.lazy_teardown_timestamps_columns.start()),
                values.teardown_timestamp_first_row[0],
            ));
            first_row_boundary_constraints.push((
                ColumnAddress::MemorySubtree(set.lazy_teardown_timestamps_columns.start() + 1),
                values.teardown_timestamp_first_row[1],
            ));
        }

        // one before last row
        {
            one_before_last_row_boundary_constraints.push((
                ColumnAddress::MemorySubtree(set.lazy_init_addresses_columns.start()),
                values.lazy_init_one_before_last_row[0],
            ));
            one_before_last_row_boundary_constraints.push((
                ColumnAddress::MemorySubtree(set.lazy_init_addresses_columns.start() + 1),
                values.lazy_init_one_before_last_row[1],
            ));

            one_before_last_row_boundary_constraints.push((
                ColumnAddress::MemorySubtree(set.lazy_teardown_values_columns.start()),
                values.teardown_value_one_before_last_row[0],
            ));
            one_before_last_row_boundary_constraints.push((
                ColumnAddress::MemorySubtree(set.lazy_teardown_values_columns.start() + 1),
                values.teardown_value_one_before_last_row[1],
            ));

            one_before_last_row_boundary_constraints.push((
                ColumnAddress::MemorySubtree(set.lazy_teardown_timestamps_columns.start()),
                values.teardown_timestamp_one_before_last_row[0],
            ));
            one_before_last_row_boundary_constraints.push((
                ColumnAddress::MemorySubtree(set.lazy_teardown_timestamps_columns.start() + 1),
                values.teardown_timestamp_one_before_last_row[1],
            ));
        }
    }
}
