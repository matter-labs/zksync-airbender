use super::*;

impl<F: PrimeField + ToTokens> SSAGenerator<F> {
    pub(crate) fn add_field_expr(&mut self, expr: &FieldNodeExpression<F>) {
        let t = match expr {
            FieldNodeExpression::Place(variable) => {
                let new_ident = self.create_var();
                let witness_proxy_ident = &self.witness_proxy_ident;
                let address = self.get_column_address(variable);
                match address {
                    ColumnAddress::WitnessSubtree(idx) => {
                        quote! {
                            let #new_ident = #witness_proxy_ident.get_witness_place(#idx);
                        }
                    }
                    ColumnAddress::MemorySubtree(idx) => {
                        quote! {
                            let #new_ident = #witness_proxy_ident.get_memory_place(#idx);
                        }
                    }
                    ColumnAddress::SetupSubtree(_idx) => {
                        todo!();
                    }
                    ColumnAddress::OptimizedOut(idx) => {
                        quote! {
                            let #new_ident = #witness_proxy_ident.get_scratch_place(#idx);
                        }
                    }
                }
            }
            FieldNodeExpression::SubExpression(_usize) => {
                unreachable!("not supported at the upper level");
            }
            FieldNodeExpression::Constant(constant) => {
                let new_ident = self.create_var();
                let witness_placer_ident = &self.witness_placer_ident;
                let literal = *constant;
                quote! {
                    let #new_ident = #witness_placer_ident::Field::constant(#literal);
                }
            }
            FieldNodeExpression::FromInteger(expr) => {
                let var_ident = self.integer_expr_into_var(expr);
                let new_ident = self.create_var();
                let witness_placer_ident = &self.witness_placer_ident;
                quote! {
                    let #new_ident = #witness_placer_ident::Field::from_integer(#var_ident);
                }
            }
            FieldNodeExpression::FromMask(expr) => {
                let var_ident = self.boolean_expr_into_var(expr);
                let new_ident = self.create_var();
                let witness_placer_ident = &self.witness_placer_ident;
                quote! {
                    let #new_ident = #witness_placer_ident::Field::from_mask(#var_ident);
                }
            }
            FieldNodeExpression::OracleValue {
                placeholder,
                subindex,
            } => {
                let new_ident = self.create_var();
                let witness_proxy_ident = &self.witness_proxy_ident;
                quote! {
                    let #new_ident = #witness_proxy_ident.get_oracle_value(#placeholder, #subindex);
                }
            }
            FieldNodeExpression::Add { lhs, rhs } => {
                let lhs = self.field_expr_into_var(lhs);
                let rhs = self.field_expr_into_var(rhs);
                let new_ident = self.create_var();
                let witness_placer_ident = &self.witness_placer_ident;
                quote! {
                    let mut #new_ident = #lhs;
                    #witness_placer_ident::Field::add_assign(&mut #new_ident, & #rhs);
                }
            }
            FieldNodeExpression::Sub { lhs, rhs } => {
                let lhs = self.field_expr_into_var(lhs);
                let rhs = self.field_expr_into_var(rhs);
                let new_ident = self.create_var();
                let witness_placer_ident = &self.witness_placer_ident;
                quote! {
                    let mut #new_ident = #lhs;
                    #witness_placer_ident::Field::sub_assign(&mut #new_ident, & #rhs);
                }
            }
            FieldNodeExpression::Mul { lhs, rhs } => {
                let lhs = self.field_expr_into_var(lhs);
                let rhs = self.field_expr_into_var(rhs);
                let new_ident = self.create_var();
                let witness_placer_ident = &self.witness_placer_ident;
                quote! {
                    let mut #new_ident = #lhs;
                    #witness_placer_ident::Field::mul_assign(&mut #new_ident, & #rhs);
                }
            }
            FieldNodeExpression::AddProduct {
                additive_term,
                mul_0,
                mul_1,
            } => {
                let additive_term = self.field_expr_into_var(additive_term);
                let mul_0 = self.field_expr_into_var(mul_0);
                let mul_1 = self.field_expr_into_var(mul_1);
                let new_ident = self.create_var();
                let witness_placer_ident = &self.witness_placer_ident;
                quote! {
                    let mut #new_ident = #additive_term;
                    #witness_placer_ident::Field::add_assign_product(&mut #new_ident, & #mul_0, & #mul_1);
                }
            }
            FieldNodeExpression::Select {
                selector,
                if_true,
                if_false,
            } => {
                let selector = self.boolean_expr_into_var(selector);
                let if_true = self.field_expr_into_var(if_true);
                let if_false = self.field_expr_into_var(if_false);
                let new_ident = self.create_var();
                let witness_placer_ident = &self.witness_placer_ident;
                quote! {
                    let #new_ident = #witness_placer_ident::Field::select(& #selector, & #if_true, & #if_false);
                }
            }
            FieldNodeExpression::InverseUnchecked(expr) => {
                let var_ident = self.field_expr_into_var(expr);
                let new_ident = self.create_var();
                let witness_placer_ident = &self.witness_placer_ident;
                quote! {
                    let #new_ident = #witness_placer_ident::Field::inverse(& #var_ident);
                }
            }
            FieldNodeExpression::InverseOrZero(expr) => {
                let var_ident = self.field_expr_into_var(expr);
                let new_ident = self.create_var();
                let witness_placer_ident = &self.witness_placer_ident;
                quote! {
                    let #new_ident = #witness_placer_ident::Field::inverse_or_zero(& #var_ident);
                }
            }
            FieldNodeExpression::LookupOutput { .. } => {
                unreachable!("not supported at the upper level");
            }
            FieldNodeExpression::MaybeLookupOutput { .. } => {
                unreachable!("not supported at the upper level");
            }
        };

        self.stream.extend(t);
    }
}
