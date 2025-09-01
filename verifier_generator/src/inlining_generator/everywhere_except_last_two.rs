use super::*;

pub(crate) fn transform_shuffle_ram_lazy_init_address_ordering(
    shuffle_ram_inits_and_teardowns: &[ShuffleRamInitAndTeardownLayout],
    lazy_init_address_aux_vars: &[ShuffleRamAuxComparisonSet],
    idents: &Idents,
    into: &mut TokenStream,
) {
    assert_eq!(
        shuffle_ram_inits_and_teardowns.len(),
        lazy_init_address_aux_vars.len()
    );
    let Idents {
        individual_term_ident,
        ..
    } = idents;

    for (inits_and_teardowns, aux_vars) in shuffle_ram_inits_and_teardowns
        .iter()
        .zip(lazy_init_address_aux_vars.iter())
    {
        let lazy_init_address_start = inits_and_teardowns.lazy_init_addresses_columns.start();

        let lazy_init_address_low = lazy_init_address_start;
        let lazy_init_address_high = lazy_init_address_start + 1;
        let lazy_init_address_low_place = ColumnAddress::MemorySubtree(lazy_init_address_low);
        let lazy_init_address_high_place = ColumnAddress::MemorySubtree(lazy_init_address_high);

        let ShuffleRamAuxComparisonSet {
            aux_low_high: [address_aux_low, address_aux_high],
            intermediate_borrow,
            final_borrow,
        } = *aux_vars;

        let this_low_expr = read_value_expr(lazy_init_address_low_place, idents, false);
        let this_high_expr = read_value_expr(lazy_init_address_high_place, idents, false);
        let intermediate_borrow_value_expr = read_value_expr(intermediate_borrow, idents, false);
        let final_borrow_value_expr = read_value_expr(final_borrow, idents, false);

        let common_stream = quote! {
            let intermedaite_borrow_value = #intermediate_borrow_value_expr;
            let final_borrow_value = #final_borrow_value_expr;
            let this_low = #this_low_expr;
            let this_high = #this_high_expr;

            let mut final_borrow_minus_one = final_borrow_value;
            final_borrow_minus_one.sub_assign_base(&Mersenne31Field::ONE);
        };

        let mut streams = vec![];

        // two constraints to compare sorting of lazy init
        {
            let next_low_expr = read_value_expr(lazy_init_address_low_place, idents, true);
            let next_high_expr = read_value_expr(lazy_init_address_high_place, idents, true);
            let aux_low_expr = read_value_expr(address_aux_low, idents, false);
            let aux_high_expr = read_value_expr(address_aux_high, idents, false);

            // we do low: this - next with borrow

            let t = quote! {
                let #individual_term_ident = {
                    let next_low = #next_low_expr;
                    let aux_low = #aux_low_expr;

                    let mut #individual_term_ident = intermedaite_borrow_value;
                    #individual_term_ident.mul_assign_by_base(&Mersenne31Field(1 << 16));
                    #individual_term_ident.add_assign(&this_low);
                    #individual_term_ident.sub_assign(&next_low);
                    #individual_term_ident.sub_assign(&aux_low);

                    #individual_term_ident
                };
            };

            streams.push(t);

            let t = quote! {
                let #individual_term_ident = {
                    let next_high = #next_high_expr;
                    let aux_high = #aux_high_expr;

                    let mut #individual_term_ident = final_borrow_value;
                    #individual_term_ident.mul_assign_by_base(&Mersenne31Field(1 << 16));
                    #individual_term_ident.add_assign(&this_high);
                    #individual_term_ident.sub_assign(&intermedaite_borrow_value);
                    #individual_term_ident.sub_assign(&next_high);
                    #individual_term_ident.sub_assign(&aux_high);

                    #individual_term_ident
                };
            };

            streams.push(t);
        }

        accumulate_contributions(into, Some(common_stream), streams, idents);
    }
}

pub(crate) fn transform_linking_constraints(
    state_linkage_constraints: &[(ColumnAddress, ColumnAddress)],
    idents: &Idents,
) -> Vec<TokenStream> {
    let Idents {
        individual_term_ident,
        ..
    } = idents;

    let mut streams = vec![];

    // linking constraints
    for (src, dst) in state_linkage_constraints.iter() {
        let this_row_expr = read_value_expr(*src, idents, false);
        let next_row_expr = read_value_expr(*dst, idents, true);

        let t = quote! {
            let #individual_term_ident = {
                let mut #individual_term_ident = #this_row_expr;
                let t = #next_row_expr;
                #individual_term_ident.sub_assign(&t);

                #individual_term_ident
            };
        };

        streams.push(t);
    }

    streams
}
