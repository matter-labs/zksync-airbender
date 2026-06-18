use super::*;
use crate::constraint::Constraint;
use crate::constraint::Term;
use crate::cs::circuit::LookupQueryTableType;
use crate::cs::circuit::RangeCheckQuery;
use crate::cs::circuit_trait::MemoryAccess;
use crate::definitions::LookupInput;
use crate::definitions::Variable;
use crate::definitions::LARGE_RANGE_CHECK_TABLE_WIDTH;
use crate::definitions::SMALL_RANGE_CHECK_TABLE_WIDTH;
use crate::tables::TableType;

pub(crate) fn compile_timestamp_comparison_range_checks<F: PrimeField>(
    dst: &mut Vec<LookupInput<F>>,
    shuffle_ram_augmented_sets: &[(MemoryAccess, ShuffleRamTimestampComparisonPartialData)],
    write_timestamp_base: [Variable; NUM_TIMESTAMP_COLUMNS_FOR_RAM],
) {
    // timestamps deserve separate range checks for shuffle RAM in the main circuit,
    // as those also take contribution from circuit index in the sequence

    for (_query, aux) in shuffle_ram_augmented_sets.iter() {
        let ShuffleRamTimestampComparisonPartialData {
            intermediate_borrow,
            read_timestamp,
            local_timestamp_in_cycle,
        } = aux;

        // read - write is with borrow. Note that we have write_timestamp_base + local timestamp offset as range checked,
        // and so to ensure correctness of the result we should check both that carry is boolean and that result is range checked.
        // We allocated intermediate carries before, and ensured that those are boolean, so we just add range checks one
        // non-materialized value of the result

        // low part
        {
            let mut constraint = Constraint::<F>::from(Term::from((
                F::from_u32_unchecked(1 << TIMESTAMP_COLUMNS_NUM_BITS),
                *intermediate_borrow,
            )));
            constraint = constraint + Term::from(read_timestamp[0]);
            constraint = constraint - Term::from(write_timestamp_base[0]);
            constraint = constraint - Term::from(*local_timestamp_in_cycle as u32);

            let input = LookupInput::from(constraint);
            dst.push(input);
        }
        // and almost the same for high part
        {
            let mut constraint =
                Constraint::<F>::from(Term::from((F::MINUS_ONE, *intermediate_borrow)));
            constraint = constraint + Term::from(read_timestamp[1]);
            constraint = constraint
                + Term::from_field(F::from_u32_unchecked(1 << TIMESTAMP_COLUMNS_NUM_BITS));
            constraint = constraint - Term::from(write_timestamp_base[1]);

            // if we borrowed - then we will fit into TIMESTAMP_COLUMNS_NUM_BITS

            let input = LookupInput::from(constraint);
            dst.push(input);
        }
    }
}

pub(crate) fn split_range_check_exprs_from_compiler<F: PrimeField>(
    range_check_expressions: &[RangeCheckQuery<F>],
) -> (
    Vec<LookupInput<F>>,
    Vec<(Vec<LookupInput<F>>, LookupQueryTableType<F>)>,
) {
    for range_check in range_check_expressions.iter() {
        let RangeCheckQuery { input, width } = range_check;
        let LookupInput::Variable(..) = input else {
            unimplemented!()
        };
        assert!(*width == LARGE_RANGE_CHECK_TABLE_WIDTH || *width == SMALL_RANGE_CHECK_TABLE_WIDTH);
    }

    // We will place 8-bit range check variables, and then 16-bit ones

    let mut range_check_8_iter = range_check_expressions
        .iter()
        .filter(|el| el.width == SMALL_RANGE_CHECK_TABLE_WIDTH);
    let range_check_16_iter = range_check_expressions
        .iter()
        .filter(|el| el.width == LARGE_RANGE_CHECK_TABLE_WIDTH);

    let num_range_check_8 = range_check_8_iter.clone().count();

    let num_pairs = num_range_check_8 / 2;
    let remainder = num_range_check_8 % 2;

    let mut range_checks_8_as_generic_lookup = vec![];
    let lookup_query_type = LookupQueryTableType::Constant(TableType::RangeCheck8x8);

    for _ in 0..num_pairs {
        let mut inputs = vec![];
        for _ in 0..2 {
            let input = range_check_8_iter.next().unwrap();
            let LookupInput::Variable(..) = &input.input else {
                unimplemented!()
            };
            inputs.push(input.input.clone());
        }
        range_checks_8_as_generic_lookup.push((inputs, lookup_query_type.clone()));
    }
    if remainder > 0 {
        let input = range_check_8_iter.next().unwrap();
        let LookupInput::Variable(..) = &input.input else {
            unimplemented!()
        };
        range_checks_8_as_generic_lookup.push((vec![input.input.clone()], lookup_query_type));
    }
    assert!(range_check_8_iter.next().is_none());

    let range_checks_16 = range_check_16_iter
        .map(|el| {
            let LookupInput::Variable(..) = &el.input else {
                unimplemented!()
            };

            el.input.clone()
        })
        .collect();

    (range_checks_16, range_checks_8_as_generic_lookup)
}
