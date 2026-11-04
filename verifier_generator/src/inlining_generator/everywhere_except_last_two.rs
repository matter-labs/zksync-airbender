use super::mersenne_wrapper::MersenneWrapper;
use super::*;

pub(crate) fn transform_shuffle_ram_lazy_init_address_ordering<MW: MersenneWrapper>(
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

        let final_borrow_minus_one_sub_assign_base_field_one =
            MW::sub_assign_base(quote! { final_borrow_minus_one }, MW::field_one());
        let common_stream = quote! {
            let intermedaite_borrow_value = #intermediate_borrow_value_expr;
            let final_borrow_value = #final_borrow_value_expr;
            let this_low = #this_low_expr;
            let this_high = #this_high_expr;

            let mut final_borrow_minus_one = final_borrow_value;
            #final_borrow_minus_one_sub_assign_base_field_one;
        };

        let mut streams = vec![];

        // two constraints to compare sorting of lazy init
        {
            let next_low_expr = read_value_expr(lazy_init_address_low_place, idents, true);
            let next_high_expr = read_value_expr(lazy_init_address_high_place, idents, true);
            let aux_low_expr = read_value_expr(address_aux_low, idents, false);
            let aux_high_expr = read_value_expr(address_aux_high, idents, false);

            // we do low: this - next with borrow

            let individual_term_ident_mul_assign_by_base_shifted = MW::mul_assign_by_base(
                quote! { #individual_term_ident },
                MW::field_new(quote! { 1 << 16 }),
            );
            let individual_term_ident_add_assign_this_low =
                MW::add_assign(quote! { #individual_term_ident }, quote! { this_low });
            let individual_term_ident_sub_assign_next_low =
                MW::sub_assign(quote! { #individual_term_ident }, quote! { next_low });
            let individual_term_ident_sub_assign_aux_low =
                MW::sub_assign(quote! { #individual_term_ident }, quote! { aux_low });
            let t = quote! {
                let #individual_term_ident = {
                    let next_low = #next_low_expr;
                    let aux_low = #aux_low_expr;

                    let mut #individual_term_ident = intermedaite_borrow_value;
                    #individual_term_ident_mul_assign_by_base_shifted;
                    #individual_term_ident_add_assign_this_low;
                    #individual_term_ident_sub_assign_next_low;
                    #individual_term_ident_sub_assign_aux_low;

                    #individual_term_ident
                };
            };

            streams.push(t);

            let individual_term_ident_add_assign_this_high =
                MW::add_assign(quote! { #individual_term_ident }, quote! { this_high });
            let individual_term_ident_sub_assign_intermedaite_borrow_value = MW::sub_assign(
                quote! { #individual_term_ident },
                quote! { intermedaite_borrow_value },
            );
            let individual_term_ident_sub_assign_next_high =
                MW::sub_assign(quote! { #individual_term_ident }, quote! { next_high });
            let individual_term_ident_sub_assign_aux_high =
                MW::sub_assign(quote! { #individual_term_ident }, quote! { aux_high });
            let t = quote! {
                let #individual_term_ident = {
                    let next_high = #next_high_expr;
                    let aux_high = #aux_high_expr;

                    let mut #individual_term_ident = final_borrow_value;
                    #individual_term_ident_mul_assign_by_base_shifted;
                    #individual_term_ident_add_assign_this_high;
                    #individual_term_ident_sub_assign_intermedaite_borrow_value;
                    #individual_term_ident_sub_assign_next_high;
                    #individual_term_ident_sub_assign_aux_high;

                    #individual_term_ident
                };
            };

            streams.push(t);
        }

        accumulate_contributions::<MW>(into, Some(common_stream), streams, idents);
    }
}

pub(crate) fn transform_linking_constraints<MW: MersenneWrapper>(
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

        let individual_term_ident_sub_assign_t =
            MW::sub_assign(quote! { #individual_term_ident }, quote! { t });
        let t = quote! {
            let #individual_term_ident = {
                let mut #individual_term_ident = #this_row_expr;
                let t = #next_row_expr;
                #individual_term_ident_sub_assign_t;

                #individual_term_ident
            };
        };

        streams.push(t);
    }

    streams
}
