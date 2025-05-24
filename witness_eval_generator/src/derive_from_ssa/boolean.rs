use super::*;

impl<F: PrimeField + ToTokens> SSAGenerator<F> {
    pub(crate) fn add_boolean_expr(&mut self, expr: &BoolNodeExpression<F>) {
        // And {
        //     lhs: Box<Self>,
        //     rhs: Box<Self>,
        // },
        // Or {
        //     lhs: Box<Self>,
        //     rhs: Box<Self>,
        // },
        // Select {
        //     selector: Box<Self>,
        //     if_true: Box<Self>,
        //     if_false: Box<Self>,
        // },
        // Negate(Box<Self>),

        let t = match expr {
            BoolNodeExpression::Place(variable) => {
                let new_ident = self.create_var();
                let witness_proxy_ident = &self.witness_proxy_ident;
                let address = self.get_column_address(variable);
                match address {
                    ColumnAddress::WitnessSubtree(idx) => {
                        quote! {
                            let #new_ident = #witness_proxy_ident.get_witness_place_boolean(#idx);
                        }
                    }
                    ColumnAddress::MemorySubtree(idx) => {
                        quote! {
                            let #new_ident = #witness_proxy_ident.get_memory_place_boolean(#idx);
                        }
                    }
                    ColumnAddress::SetupSubtree(_idx) => {
                        todo!();
                    }
                    ColumnAddress::OptimizedOut(idx) => {
                        quote! {
                            let #new_ident = #witness_proxy_ident.get_scratch_place_boolean(#idx);
                        }
                    }
                }
            }
            BoolNodeExpression::OracleValue { placeholder } => {
                let new_ident = self.create_var();
                let witness_proxy_ident = &self.witness_proxy_ident;
                quote! {
                    let #new_ident = #witness_proxy_ident.get_oracle_value_boolean(#placeholder);
                }
            }
            BoolNodeExpression::SubExpression(_usize) => {
                unreachable!("not supported at the upper level");
            }
            BoolNodeExpression::Constant(constant) => {
                let new_ident = self.create_var();
                let witness_placer_ident = &self.witness_placer_ident;
                let literal = *constant;
                quote! {
                    let #new_ident = #witness_placer_ident::Mask::constant(#literal);
                }
            }
            BoolNodeExpression::FromGenericInteger(expr) => {
                let var_ident = self.integer_expr_into_var(expr);
                let new_ident = self.create_var();
                //let witness_placer_ident = &self.witness_placer_ident;
                quote! {
                    let #new_ident = WitnessComputationCore::into_mask(#var_ident);
                }
            }
            BoolNodeExpression::FromField(expr) => {
                let var_ident = self.field_expr_into_var(expr);
                let new_ident = self.create_var();
                let witness_placer_ident = &self.witness_placer_ident;
                quote! {
                    let #new_ident = #witness_placer_ident::Field::into_mask(#var_ident);
                }
            }
            BoolNodeExpression::FromGenericIntegerEquality { lhs, rhs } => {
                let type_ident = Self::ident_for_integer_binop(lhs, rhs);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                let new_ident = self.create_var();
                let witness_placer_ident = &self.witness_placer_ident;
                quote! {
                    let #new_ident = #witness_placer_ident::#type_ident::equal(& #lhs, & #rhs);
                }
            }
            BoolNodeExpression::FromGenericIntegerCarry { lhs, rhs } => {
                let type_ident = Self::ident_for_integer_binop(lhs, rhs);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                let new_ident = self.create_var();
                let witness_placer_ident = &self.witness_placer_ident;
                quote! {
                    let #new_ident = #witness_placer_ident::#type_ident::overflowing_add(& #lhs, & #rhs).1;
                }
            }
            BoolNodeExpression::FromGenericIntegerBorrow { lhs, rhs } => {
                let type_ident = Self::ident_for_integer_binop(lhs, rhs);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                let new_ident = self.create_var();
                let witness_placer_ident = &self.witness_placer_ident;
                quote! {
                    let #new_ident = #witness_placer_ident::#type_ident::overflowing_sub(& #lhs, & #rhs).1;
                }
            }
            BoolNodeExpression::FromFieldEquality { lhs, rhs } => {
                let lhs = self.field_expr_into_var(lhs);
                let rhs = self.field_expr_into_var(rhs);
                let new_ident = self.create_var();
                let witness_placer_ident = &self.witness_placer_ident;
                quote! {
                    let #new_ident = #witness_placer_ident::Field::equal(& #lhs, & #rhs);
                }
            }
            BoolNodeExpression::And { lhs, rhs } => {
                let lhs = self.boolean_expr_into_var(lhs);
                let rhs = self.boolean_expr_into_var(rhs);
                let new_ident = self.create_var();
                let witness_placer_ident = &self.witness_placer_ident;
                quote! {
                    let #new_ident = #witness_placer_ident::Mask::and(& #lhs, & #rhs);
                }
            }
            BoolNodeExpression::Or { lhs, rhs } => {
                let lhs = self.boolean_expr_into_var(lhs);
                let rhs = self.boolean_expr_into_var(rhs);
                let new_ident = self.create_var();
                let witness_placer_ident = &self.witness_placer_ident;
                quote! {
                    let #new_ident = #witness_placer_ident::Mask::or(& #lhs, & #rhs);
                }
            }
            BoolNodeExpression::Select {
                selector,
                if_true,
                if_false,
            } => {
                let selector = self.boolean_expr_into_var(selector);
                let if_true = self.boolean_expr_into_var(if_true);
                let if_false = self.boolean_expr_into_var(if_false);
                let new_ident = self.create_var();
                let witness_placer_ident = &self.witness_placer_ident;
                quote! {
                    let #new_ident = #witness_placer_ident::Mask::select(& #selector, & #if_true, & #if_false);
                }
            }
            BoolNodeExpression::Negate(expr) => {
                let var_ident = self.boolean_expr_into_var(expr);
                let new_ident = self.create_var();
                let witness_placer_ident = &self.witness_placer_ident;
                quote! {
                    let #new_ident = #witness_placer_ident::Mask::negate(& #var_ident);
                }
            }
        };

        self.stream.extend(t);
    }
}
