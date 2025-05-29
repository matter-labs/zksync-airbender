use std::collections::BTreeMap;

use ::field::PrimeField;
use cs::cs::witness_placer::graph_description::{
    BoolNodeExpression, Expression, FieldNodeExpression, FixedWidthIntegerNodeExpression,
    RawExpression,
};
use cs::definitions::ColumnAddress;
use cs::definitions::Variable;
use cs::one_row_compiler::CompiledCircuitArtifact;
use cs::one_row_compiler::slice_to_token_array;
use proc_macro2::*;
use quote::{ToTokens, quote};

mod boolean;
mod field;
mod integer;

struct SSAGenerator<F: PrimeField + ToTokens> {
    next_var_idx: usize,
    stream: TokenStream,
    witness_proxy_ident: Ident,
    witness_placer_ident: Ident,
    layout: BTreeMap<Variable, ColumnAddress>,
    num_lookup_mappings: usize,
    write_into_memory: bool,
    _marker: std::marker::PhantomData<F>,
}

impl<F: PrimeField + ToTokens> SSAGenerator<F> {
    fn new(
        witness_proxy_ident: &Ident,
        witness_placer_ident: &Ident,
        layout: &BTreeMap<Variable, ColumnAddress>,
        num_lookup_mappings: usize,
        write_into_memory: bool,
    ) -> Self {
        Self {
            next_var_idx: 0,
            stream: TokenStream::new(),
            witness_proxy_ident: witness_proxy_ident.clone(),
            witness_placer_ident: witness_placer_ident.clone(),
            layout: layout.clone(),
            num_lookup_mappings,
            write_into_memory,
            _marker: std::marker::PhantomData,
        }
    }

    fn create_var(&mut self) -> Ident {
        let idx = self.next_var_idx;
        self.next_var_idx += 1;
        Self::ident_for_idx(idx)
    }

    fn get_column_address(&self, variable: &Variable) -> ColumnAddress {
        if variable.is_placeholder() {
            panic!("variable is placeholder");
        }
        self.layout[variable]
    }

    fn ident_for_idx(idx: usize) -> Ident {
        Ident::new(&format!("v_{}", idx), Span::call_site())
    }

    fn field_expr_into_var(&self, expr: &FieldNodeExpression<F>) -> Ident {
        let FieldNodeExpression::SubExpression(idx) = expr else {
            unreachable!();
        };
        Self::ident_for_idx(*idx)
    }

    fn boolean_expr_into_var(&self, expr: &BoolNodeExpression<F>) -> Ident {
        let BoolNodeExpression::SubExpression(idx) = expr else {
            unreachable!();
        };
        Self::ident_for_idx(*idx)
    }

    fn integer_expr_into_var(&self, expr: &FixedWidthIntegerNodeExpression<F>) -> Ident {
        match expr {
            FixedWidthIntegerNodeExpression::U8SubExpression(idx)
            | FixedWidthIntegerNodeExpression::U16SubExpression(idx)
            | FixedWidthIntegerNodeExpression::U32SubExpression(idx) => Self::ident_for_idx(*idx),
            a @ _ => {
                panic!("Trying to make variable from expression {:?}", a);
            }
        }
    }

    fn add_expression(&mut self, expr: &RawExpression<F>) {
        match expr {
            RawExpression::Bool(expr) => {
                self.add_boolean_expr(expr);
            }
            RawExpression::Field(expr) => {
                self.add_field_expr(expr);
            }
            RawExpression::Integer(expr) => {
                self.add_integer_expr(expr);
            }
            RawExpression::PerformLookup {
                input_subexpr_idxes, // subexpressions
                table_id_subexpr_idx,
                num_outputs,
                lookup_mapping_idx,
            } => {
                assert!(
                    *lookup_mapping_idx < self.num_lookup_mappings,
                    "expression refers to lookup number {}, while only {} exist in scope",
                    lookup_mapping_idx,
                    self.num_lookup_mappings
                );
                let new_ident = self.create_var();
                let witness_proxy_ident = &self.witness_proxy_ident;

                // println!("Synthesize lookup expression for index {} with {} outputs", lookup_mapping_idx, num_outputs);

                let num_inputs = input_subexpr_idxes.len();

                let inputs: Vec<_> = input_subexpr_idxes
                    .iter()
                    .map(|el| Self::ident_for_idx(*el))
                    .collect();
                let inputs = slice_to_token_array(&inputs);
                let table_id = Self::ident_for_idx(*table_id_subexpr_idx);

                if *num_outputs > 0 {
                    let t = quote! {
                        let #new_ident = #witness_proxy_ident.lookup::< #num_inputs, #num_outputs >(& #inputs, #table_id, #lookup_mapping_idx);
                    };
                    self.stream.extend(t);
                } else {
                    let t = quote! {
                        let #new_ident = #witness_proxy_ident.lookup_enforce::< #num_inputs>(& #inputs, #table_id, #lookup_mapping_idx);
                    };
                    self.stream.extend(t);
                }
            }
            RawExpression::MaybePerformLookup {
                input_subexpr_idxes, // subexpressions
                table_id_subexpr_idx,
                mask_id_subexpr_idx,
                num_outputs,
            } => {
                let new_ident = self.create_var();
                let witness_proxy_ident = &self.witness_proxy_ident;

                let num_inputs = input_subexpr_idxes.len();

                let inputs: Vec<_> = input_subexpr_idxes
                    .iter()
                    .map(|el| Self::ident_for_idx(*el))
                    .collect();
                let inputs = slice_to_token_array(&inputs);
                let table_id = Self::ident_for_idx(*table_id_subexpr_idx);
                let mask_id = Self::ident_for_idx(*mask_id_subexpr_idx);

                let t = quote! {
                    let #new_ident = #witness_proxy_ident.maybe_lookup::< #num_inputs, #num_outputs >(& #inputs, #table_id, #mask_id);
                };

                self.stream.extend(t);
            }
            RawExpression::AccessLookup {
                subindex,
                output_index,
            } => {
                let var_ident = Self::ident_for_idx(*subindex);
                let new_ident = self.create_var();

                let t = quote! {
                    let #new_ident = #var_ident[# output_index];
                };

                self.stream.extend(t);
            }
            RawExpression::WriteVariable {
                into_variable,
                source_subexpr, // it'll be only subexpression, but we need type
                condition_subexpr_idx,
            } => {
                // this is an expression in SSA, so we should update index
                self.next_var_idx += 1;

                let witness_proxy_ident = &self.witness_proxy_ident;
                let witness_placer_ident = &self.witness_placer_ident;
                let address = self.get_column_address(into_variable);
                let t = match address {
                    ColumnAddress::WitnessSubtree(idx) => match source_subexpr {
                        Expression::Field(expr) => {
                            let source_ident = self.field_expr_into_var(expr);
                            if let Some(condition) = condition_subexpr_idx {
                                let condition_ident = Self::ident_for_idx(*condition);

                                quote! {
                                    #witness_proxy_ident.set_witness_place(#idx, #witness_placer_ident::Field::select(& #condition_ident, & #source_ident, & #witness_proxy_ident.get_witness_place(#idx)));
                                }
                            } else {
                                quote! {
                                    #witness_proxy_ident.set_witness_place(#idx, #source_ident);
                                }
                            }
                        }
                        Expression::Bool(expr) => {
                            let source_ident = self.boolean_expr_into_var(expr);
                            if let Some(condition) = condition_subexpr_idx {
                                let condition_ident = Self::ident_for_idx(*condition);

                                quote! {
                                    #witness_proxy_ident.set_witness_place_boolean(#idx, #witness_placer_ident::Mask::select(& #condition_ident, & #source_ident, & #witness_proxy_ident.get_witness_place_boolean(#idx)));
                                }
                            } else {
                                quote! {
                                    #witness_proxy_ident.set_witness_place_boolean(#idx, #source_ident);
                                }
                            }
                        }
                        Expression::U8(expr) => {
                            let source_ident = self.integer_expr_into_var(expr);
                            if let Some(condition) = condition_subexpr_idx {
                                let condition_ident = Self::ident_for_idx(*condition);

                                quote! {
                                    #witness_proxy_ident.set_witness_place_u8(#idx, #witness_placer_ident::U8::select(& #condition_ident, & #source_ident, & #witness_proxy_ident.get_witness_place_u8(#idx)));
                                }
                            } else {
                                quote! {
                                    #witness_proxy_ident.set_witness_place_u8(#idx, #source_ident);
                                }
                            }
                        }
                        Expression::U16(expr) => {
                            let source_ident = self.integer_expr_into_var(expr);
                            if let Some(condition) = condition_subexpr_idx {
                                let condition_ident = Self::ident_for_idx(*condition);

                                quote! {
                                    #witness_proxy_ident.set_witness_place_u16(#idx, #witness_placer_ident::U16::select(& #condition_ident, & #source_ident, & #witness_proxy_ident.get_witness_place_u16(#idx)));
                                }
                            } else {
                                quote! {
                                    #witness_proxy_ident.set_witness_place_u16(#idx, #source_ident);
                                }
                            }
                        }
                        Expression::U32(expr) => {
                            let source_ident = self.integer_expr_into_var(expr);
                            if let Some(condition) = condition_subexpr_idx {
                                let condition_ident = Self::ident_for_idx(*condition);

                                quote! {
                                    #witness_proxy_ident.set_witness_place_u32(#idx, #witness_placer_ident::U32::select(& #condition_ident, & #source_ident, & #witness_proxy_ident.get_witness_place_u32(#idx)));
                                }
                            } else {
                                quote! {
                                    #witness_proxy_ident.set_witness_place_u32(#idx, #source_ident);
                                }
                            }
                        }
                    },
                    ColumnAddress::MemorySubtree(_idx) => {
                        if self.write_into_memory {
                            todo!()
                        } else {
                            // do nothing and rely on the generic procedure. Hope that compiler optimizes out unused expressions
                            quote! {}
                        }
                    }
                    ColumnAddress::SetupSubtree(_idx) => {
                        unreachable!("can not write to setup");
                    }
                    ColumnAddress::OptimizedOut(idx) => match source_subexpr {
                        Expression::Field(expr) => {
                            let source_ident = self.field_expr_into_var(expr);
                            if let Some(condition) = condition_subexpr_idx {
                                let condition_ident = Self::ident_for_idx(*condition);

                                quote! {
                                    #witness_proxy_ident.set_scratch_place(#idx, #witness_placer_ident::Field::select(& #condition_ident, & #source_ident, & #witness_proxy_ident.get_scratch_place(#idx)));
                                }
                            } else {
                                quote! {
                                    #witness_proxy_ident.set_scratch_place(#idx, #source_ident);
                                }
                            }
                        }
                        Expression::Bool(expr) => {
                            let source_ident = self.boolean_expr_into_var(expr);
                            if let Some(condition) = condition_subexpr_idx {
                                let condition_ident = Self::ident_for_idx(*condition);

                                quote! {
                                    #witness_proxy_ident.set_scratch_place_boolean(#idx, #witness_placer_ident::Mask::select(& #condition_ident, & #source_ident, & #witness_proxy_ident.get_scratch_place_boolean(#idx)));
                                }
                            } else {
                                quote! {
                                    #witness_proxy_ident.set_scratch_place_boolean(#idx, #source_ident);
                                }
                            }
                        }
                        Expression::U8(expr) => {
                            let source_ident = self.integer_expr_into_var(expr);
                            if let Some(condition) = condition_subexpr_idx {
                                let condition_ident = Self::ident_for_idx(*condition);

                                quote! {
                                    #witness_proxy_ident.set_scratch_place_u8(#idx, #witness_placer_ident::U8::select(& #condition_ident, & #source_ident, & #witness_proxy_ident.get_scratch_place_u8(#idx)));
                                }
                            } else {
                                quote! {
                                    #witness_proxy_ident.set_scratch_place_u8(#idx, #source_ident);
                                }
                            }
                        }
                        Expression::U16(expr) => {
                            let source_ident = self.integer_expr_into_var(expr);
                            if let Some(condition) = condition_subexpr_idx {
                                let condition_ident = Self::ident_for_idx(*condition);

                                quote! {
                                    #witness_proxy_ident.set_scratch_place_u16(#idx, #witness_placer_ident::U16::select(& #condition_ident, & #source_ident, & #witness_proxy_ident.get_scratch_place_u16(#idx)));
                                }
                            } else {
                                quote! {
                                    #witness_proxy_ident.set_scratch_place_u16(#idx, #source_ident);
                                }
                            }
                        }
                        Expression::U32(expr) => {
                            let source_ident = self.integer_expr_into_var(expr);
                            if let Some(condition) = condition_subexpr_idx {
                                let condition_ident = Self::ident_for_idx(*condition);

                                quote! {
                                    #witness_proxy_ident.set_scratch_place_u32(#idx, #witness_placer_ident::U32::select(& #condition_ident, & #source_ident, & #witness_proxy_ident.get_scratch_place_u32(#idx)));
                                }
                            } else {
                                quote! {
                                    #witness_proxy_ident.set_scratch_place_u32(#idx, #source_ident);
                                }
                            }
                        }
                    },
                };

                self.stream.extend(t);
            }
        }
    }
}

use ::field::Mersenne31Field;

const INLINING_LIMIT: usize = 16;

pub fn derive_from_ssa(
    ssa: &[Vec<RawExpression<Mersenne31Field>>],
    layout: &CompiledCircuitArtifact<Mersenne31Field>,
    perform_assignments_to_memory: bool,
) -> TokenStream {
    let num_lookup_mappings = layout.witness_layout.width_3_lookups.len();

    let witness_proxy_ident = Ident::new("witness_proxy", Span::call_site());
    let witness_placer_ident = Ident::new("W", Span::call_site());
    let field_ident = Ident::new("Mersenne31Field", Span::call_site());
    let layout = &layout.variable_mapping;

    let mut individual_fns_stream = TokenStream::new();
    let mut external_caller_stream = TokenStream::new();

    for (fn_idx, eval_fn) in ssa.iter().enumerate() {
        // quickly check that if all outputs are into memory, then we can skip such cases
        if perform_assignments_to_memory == false {
            let mut can_skip = true;
            for expr in eval_fn.iter() {
                if let RawExpression::WriteVariable { into_variable, .. } = expr {
                    let place = layout[into_variable];
                    match place {
                        ColumnAddress::MemorySubtree(..) => {}
                        _ => {
                            can_skip = false;
                            break;
                        }
                    }
                }
                if let RawExpression::PerformLookup { .. } = expr {
                    // we can not skip it as we will need to count multiplicity
                    can_skip = false;
                    break;
                }
            }

            if can_skip {
                continue;
            }
        }

        let inline_tag = if eval_fn.len() >= INLINING_LIMIT {
            quote! {}
        } else {
            quote! {#[inline(always)]}
        };

        let mut generator = SSAGenerator::<Mersenne31Field>::new(
            &witness_proxy_ident,
            &witness_placer_ident,
            &layout,
            num_lookup_mappings,
            perform_assignments_to_memory,
        );

        for el in eval_fn.iter() {
            generator.add_expression(el);
        }

        let ident = Ident::new(&format!("eval_fn_{}", fn_idx), Span::call_site());
        let generated_stream = generator.stream;
        let substream = quote! {
            #[allow(unused_variables)]
            #inline_tag
            fn #ident<'a, 'b: 'a, W: WitnessTypeSet<#field_ident>, P: WitnessProxy<#field_ident, W> + 'b>(witness_proxy: &'a mut P) where W::Field: Copy, W::Mask: Copy, W::U32: Copy, W::U16: Copy, W::U8: Copy, W::I32: Copy {
                #generated_stream
            }
        };
        individual_fns_stream.extend(substream);

        external_caller_stream.extend(quote! {
            #ident(witness_proxy);
        })
    }

    quote! {
        #individual_fns_stream

        #[allow(dead_code)]
        pub fn evaluate_witness_fn<'a, 'b: 'a, W: WitnessTypeSet<#field_ident>, P: WitnessProxy<#field_ident, W> + 'b>(witness_proxy: &'a mut P) where W::Field: Copy, W::Mask: Copy, W::U32: Copy, W::U16: Copy, W::U8: Copy, W::I32: Copy {
            #external_caller_stream
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use ::field::Mersenne31Field;
    use std::io::Write;

    fn deserialize_from_file<T: serde::de::DeserializeOwned>(filename: &str) -> T {
        let src = std::fs::File::open(filename).unwrap();
        serde_json::from_reader(src).unwrap()
    }

    #[test]
    fn launch() {
        // let compiled_circuit: CompiledCircuitArtifact<Mersenne31Field> =
        //     deserialize_from_file("../cs/full_machine_with_delegation_layout.json");
        let compiled_circuit: CompiledCircuitArtifact<Mersenne31Field> =
            deserialize_from_file("../prover/full_machine_layout.json");
        let compiled_graph: Vec<Vec<RawExpression<Mersenne31Field>>> =
            deserialize_from_file("../cs/full_machine_with_delegation_ssa.json");

        let full_stream = derive_from_ssa(&compiled_graph, &compiled_circuit, false);

        std::fs::File::create("src/generated.rs")
            .unwrap()
            .write_all(&full_stream.to_string().as_bytes())
            .unwrap();
    }

    #[test]
    fn gen_for_prover_tests() {
        for prefix in [
            "full_machine_with_delegation",
            "minimal_machine_with_delegation",
            "blake_delegation",
        ] {
            let compiled_circuit: CompiledCircuitArtifact<Mersenne31Field> =
                deserialize_from_file(&format!("../cs/{}_layout.json", prefix));
            let compiled_graph: Vec<Vec<RawExpression<Mersenne31Field>>> =
                deserialize_from_file(&format!("../cs/{}_ssa.json", prefix));
            let full_stream = derive_from_ssa(&compiled_graph, &compiled_circuit, false);

            std::fs::File::create(&format!("../prover/{}_generated.rs", prefix))
                .unwrap()
                .write_all(&full_stream.to_string().as_bytes())
                .unwrap();
        }
    }
}
