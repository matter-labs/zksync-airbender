use super::mersenne_wrapper::MersenneWrapper;
use super::*;

pub(crate) fn read_value_expr(
    column: ColumnAddress,
    idents: &Idents,
    use_next_row: bool,
) -> TokenStream {
    match column {
        ColumnAddress::WitnessSubtree(offset) => {
            let ident = if use_next_row == false {
                &idents.witness_values_ident
            } else {
                &idents.witness_values_next_row_ident
            };

            quote! {
                *(#ident.get_unchecked(#offset))
            }
        }
        ColumnAddress::MemorySubtree(offset) => {
            let ident = if use_next_row == false {
                &idents.memory_values_ident
            } else {
                &idents.memory_values_next_row_ident
            };

            quote! {
                *(#ident.get_unchecked(#offset))
            }
        }
        ColumnAddress::SetupSubtree(offset) => {
            assert!(use_next_row == false);
            let ident = &idents.setup_values_ident;

            quote! {
                *(#ident.get_unchecked(#offset))
            }
        }
        ColumnAddress::OptimizedOut(..) => {
            unreachable!("quotient must not use `optimized out` variables");
        }
    }
}

pub(crate) fn read_stage_2_value_expr(
    offset: usize,
    idents: &Idents,
    use_next_row: bool,
) -> TokenStream {
    let ident = if use_next_row == false {
        &idents.stage_2_values_ident
    } else {
        &idents.stage_2_values_next_row_ident
    };

    quote! {
        *(#ident.get_unchecked(#offset))
    }
}

pub(crate) fn accumulate_contributions<MW: MersenneWrapper>(
    into: &mut TokenStream,
    common_stream_for_terms: Option<TokenStream>,
    individual_term_streams: Vec<TokenStream>,
    idents: &Idents,
) {
    if individual_term_streams.is_empty() {
        assert!(common_stream_for_terms.is_none());
        return;
    }

    if let Some(common_stream_for_terms) = common_stream_for_terms {
        if into.is_empty() {
            let terms_accumulator_ident = &idents.terms_accumulator_ident;
            let quartic_zero = MW::quartic_zero();
            // a little inefficient, but simplifies leaking of common expressions
            let t = quote! {
                let mut #terms_accumulator_ident = #quartic_zero;
            };
            into.extend(t);
        }

        let mut inner_stream = TokenStream::new();
        for el in individual_term_streams.into_iter() {
            accumulate_contribution::<MW>(&mut inner_stream, false, el, idents);
        }
        let t = quote! {
            {
                #common_stream_for_terms

                #inner_stream
            }
        };
        into.extend(t);
    } else {
        for el in individual_term_streams.into_iter() {
            let is_first = into.is_empty();
            accumulate_contribution::<MW>(into, is_first, el, idents);
        }
    }
}

fn accumulate_contribution<MW: MersenneWrapper>(
    into: &mut TokenStream,
    is_first: bool,
    individual_term_stream: TokenStream,
    idents: &Idents,
) {
    let Idents {
        individual_term_ident,
        terms_accumulator_ident,
        quotient_alpha_ident,
        ..
    } = idents;

    let t = if is_first {
        quote! {
            let mut #terms_accumulator_ident = {
                #individual_term_stream

                #individual_term_ident
            };
        }
    } else {
        let terms_accumulator_mul_assign_alpha = MW::mul_assign(
            quote! { #terms_accumulator_ident },
            quote! { #quotient_alpha_ident },
        );
        let terms_accumulator_add_assign_contribution =
            MW::add_assign(quote! { #terms_accumulator_ident }, quote! { contribution });
        quote! {
            {
                #terms_accumulator_mul_assign_alpha;
                let contribution = {
                    #individual_term_stream

                    #individual_term_ident
                };
                #terms_accumulator_add_assign_contribution;
            }
        }
    };
    into.extend(t);
}
