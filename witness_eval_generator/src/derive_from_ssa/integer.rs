use super::*;

impl<F: PrimeField + ToTokens> SSAGenerator<F> {
    pub(crate) fn ident_for_integer_unop(lhs: &FixedWidthIntegerNodeExpression<F>) -> Ident {
        let lhs = lhs.bit_width();

        match lhs {
            8 => Ident::new("U8", Span::call_site()),
            16 => Ident::new("U16", Span::call_site()),
            32 => Ident::new("U32", Span::call_site()),
            a @ _ => {
                panic!("unknown bit width {}", a);
            }
        }
    }

    pub(crate) fn ident_for_integer_binop(
        lhs: &FixedWidthIntegerNodeExpression<F>,
        rhs: &FixedWidthIntegerNodeExpression<F>,
    ) -> Ident {
        let lhs_width = lhs.bit_width();
        let rhs_width = rhs.bit_width();
        assert_eq!(lhs_width, rhs_width);

        Self::ident_for_integer_unop(lhs)
    }

    pub(crate) fn add_integer_expr(&mut self, expr: &FixedWidthIntegerNodeExpression<F>) {
        let t = match expr {
            FixedWidthIntegerNodeExpression::U8Place(variable) => {
                let new_ident = self.create_var();
                let witness_proxy_ident = &self.witness_proxy_ident;
                let address = self.get_column_address(variable);
                match address {
                    ColumnAddress::WitnessSubtree(idx) => {
                        quote! {
                            let #new_ident = #witness_proxy_ident.get_witness_place_u8(#idx);
                        }
                    }
                    ColumnAddress::MemorySubtree(idx) => {
                        quote! {
                            let #new_ident = #witness_proxy_ident.get_memory_place_u8(#idx);
                        }
                    }
                    ColumnAddress::SetupSubtree(_idx) => {
                        todo!();
                    }
                    ColumnAddress::OptimizedOut(idx) => {
                        quote! {
                            let #new_ident = #witness_proxy_ident.get_scratch_place_u8(#idx);
                        }
                    }
                }
            }
            FixedWidthIntegerNodeExpression::U16Place(variable) => {
                let new_ident = self.create_var();
                let witness_proxy_ident = &self.witness_proxy_ident;
                let address = self.get_column_address(variable);
                match address {
                    ColumnAddress::WitnessSubtree(idx) => {
                        quote! {
                            let #new_ident = #witness_proxy_ident.get_witness_place_u16(#idx);
                        }
                    }
                    ColumnAddress::MemorySubtree(idx) => {
                        quote! {
                            let #new_ident = #witness_proxy_ident.get_memory_place_u16(#idx);
                        }
                    }
                    ColumnAddress::SetupSubtree(_idx) => {
                        todo!();
                    }
                    ColumnAddress::OptimizedOut(idx) => {
                        quote! {
                            let #new_ident = #witness_proxy_ident.get_scratch_place_u16(#idx);
                        }
                    }
                }
            }

            FixedWidthIntegerNodeExpression::U8SubExpression(_usize)
            | FixedWidthIntegerNodeExpression::U16SubExpression(_usize)
            | FixedWidthIntegerNodeExpression::U32SubExpression(_usize) => {
                unreachable!("not supported at the upper level");
            }
            FixedWidthIntegerNodeExpression::U32OracleValue { placeholder } => {
                let new_ident = self.create_var();
                let witness_proxy_ident = &self.witness_proxy_ident;
                quote! {
                    let #new_ident = #witness_proxy_ident.get_oracle_value_u32(#placeholder);
                }
            }
            FixedWidthIntegerNodeExpression::U16OracleValue { placeholder } => {
                let new_ident = self.create_var();
                let witness_proxy_ident = &self.witness_proxy_ident;
                quote! {
                    let #new_ident = #witness_proxy_ident.get_oracle_value_u16(#placeholder);
                }
            }
            FixedWidthIntegerNodeExpression::U8OracleValue { placeholder } => {
                let new_ident = self.create_var();
                let witness_proxy_ident = &self.witness_proxy_ident;
                quote! {
                    let #new_ident = #witness_proxy_ident.get_oracle_value_u8(#placeholder);
                }
            }
            FixedWidthIntegerNodeExpression::ConstantU8(constant) => {
                let new_ident = self.create_var();
                let witness_placer_ident = &self.witness_placer_ident;
                let literal = *constant;
                quote! {
                    let #new_ident = #witness_placer_ident::U8::constant(#literal);
                }
            }
            FixedWidthIntegerNodeExpression::ConstantU16(constant) => {
                let new_ident = self.create_var();
                let witness_placer_ident = &self.witness_placer_ident;
                let literal = *constant;
                quote! {
                    let #new_ident = #witness_placer_ident::U16::constant(#literal);
                }
            }
            FixedWidthIntegerNodeExpression::ConstantU32(constant) => {
                let new_ident = self.create_var();
                let witness_placer_ident = &self.witness_placer_ident;
                let literal = *constant;
                quote! {
                    let #new_ident = #witness_placer_ident::U32::constant(#literal);
                }
            }
            FixedWidthIntegerNodeExpression::U32FromMask(expr) => {
                let var_ident = self.boolean_expr_into_var(expr);
                let new_ident = self.create_var();
                let witness_placer_ident = &self.witness_placer_ident;
                quote! {
                    let #new_ident = #witness_placer_ident::U32::from_mask(#var_ident);
                }
            }
            FixedWidthIntegerNodeExpression::U32FromField(expr) => {
                let var_ident = self.field_expr_into_var(expr);
                let new_ident = self.create_var();
                //let witness_placer_ident = &self.witness_placer_ident;
                quote! {
                    let #new_ident = #var_ident.as_integer();
                }
            }

            FixedWidthIntegerNodeExpression::WidenFromU8(expr)
            | FixedWidthIntegerNodeExpression::WidenFromU16(expr) => {
                let var_ident = self.integer_expr_into_var(expr);
                let new_ident = self.create_var();
                //let witness_placer_ident = &self.witness_placer_ident;
                quote! {
                    let #new_ident = #var_ident.widen();
                }
            }

            FixedWidthIntegerNodeExpression::TruncateFromU16(expr)
            | FixedWidthIntegerNodeExpression::TruncateFromU32(expr) => {
                let var_ident = self.integer_expr_into_var(expr);
                let new_ident = self.create_var();
                //let witness_placer_ident = &self.witness_placer_ident;
                quote! {
                    let #new_ident = #var_ident.truncate();
                }
            }
            FixedWidthIntegerNodeExpression::I32FromU32(expr) => {
                let var_ident = self.integer_expr_into_var(expr);
                let new_ident = self.create_var();
                let witness_placer_ident = &self.witness_placer_ident;
                quote! {
                    let #new_ident = #witness_placer_ident::I32::from_unsigned(#var_ident);
                }
            }
            FixedWidthIntegerNodeExpression::U32FromI32(expr) => {
                let var_ident = self.integer_expr_into_var(expr);
                let new_ident = self.create_var();
                let witness_placer_ident = &self.witness_placer_ident;
                quote! {
                    let #new_ident = #witness_placer_ident::I32::as_unsigned(#var_ident);
                }
            }
            FixedWidthIntegerNodeExpression::Select {
                selector,
                if_true,
                if_false,
            } => {
                let selector = self.boolean_expr_into_var(selector);
                let if_true = self.integer_expr_into_var(if_true);
                let if_false = self.integer_expr_into_var(if_false);
                let new_ident = self.create_var();
                //let witness_placer_ident = &self.witness_placer_ident;
                quote! {
                    let #new_ident = WitnessComputationCore::select(& #selector, & #if_true, & #if_false);
                }
            }
            FixedWidthIntegerNodeExpression::WrappingAdd { lhs, rhs } => {
                let type_ident = Self::ident_for_integer_binop(lhs, rhs);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                let new_ident = self.create_var();
                let witness_placer_ident = &self.witness_placer_ident;
                quote! {
                    let mut #new_ident = #lhs;
                    #witness_placer_ident::#type_ident::add_assign(&mut #new_ident, & #rhs);
                }
            }
            FixedWidthIntegerNodeExpression::WrappingSub { lhs, rhs } => {
                let type_ident = Self::ident_for_integer_binop(lhs, rhs);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                let new_ident = self.create_var();
                let witness_placer_ident = &self.witness_placer_ident;
                quote! {
                    let mut #new_ident = #lhs;
                    #witness_placer_ident::#type_ident::sub_assign(&mut #new_ident, & #rhs);
                }
            }
            FixedWidthIntegerNodeExpression::WrappingShl { lhs, magnitude } => {
                let lhs = self.integer_expr_into_var(lhs);
                let literal = *magnitude;
                let new_ident = self.create_var();
                quote! {
                    let #new_ident = #lhs.shl(#literal);
                }
            }
            FixedWidthIntegerNodeExpression::WrappingShr { lhs, magnitude } => {
                let lhs = self.integer_expr_into_var(lhs);
                let literal = *magnitude;
                let new_ident = self.create_var();
                quote! {
                    let #new_ident = #lhs.shr(#literal);
                }
            }
            FixedWidthIntegerNodeExpression::LowestBits { value, num_bits } => {
                let lhs = self.integer_expr_into_var(value);
                let literal = *num_bits;
                let new_ident = self.create_var();
                assert!(lhs != new_ident);
                quote! {
                    let #new_ident = #lhs.get_lowest_bits(#literal);
                }
            }
            FixedWidthIntegerNodeExpression::MulLow { lhs, rhs } => {
                let type_ident = Self::ident_for_integer_binop(lhs, rhs);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                let new_ident = self.create_var();
                let witness_placer_ident = &self.witness_placer_ident;
                quote! {
                    let #new_ident = #witness_placer_ident::#type_ident::split_widening_product(& #lhs, & #rhs).0;
                }
            }
            FixedWidthIntegerNodeExpression::MulHigh { lhs, rhs } => {
                let type_ident = Self::ident_for_integer_binop(lhs, rhs);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                let new_ident = self.create_var();
                let witness_placer_ident = &self.witness_placer_ident;

                quote! {
                    let #new_ident = #witness_placer_ident::#type_ident::split_widening_product(& #lhs, & #rhs).1;
                }
            }
            FixedWidthIntegerNodeExpression::DivAssumeNonzero { lhs, rhs } => {
                let type_ident = Self::ident_for_integer_binop(lhs, rhs);
                let bit_width = lhs.bit_width();
                assert_eq!(bit_width, 32);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                let new_ident = self.create_var();
                let witness_placer_ident = &self.witness_placer_ident;
                quote! {
                    let #new_ident = #witness_placer_ident::#type_ident::div_rem_assume_nonzero_divisor(& #lhs, & #rhs).0;
                }
            }
            FixedWidthIntegerNodeExpression::RemAssumeNonzero { lhs, rhs } => {
                let type_ident = Self::ident_for_integer_binop(lhs, rhs);
                let bit_width = lhs.bit_width();
                assert_eq!(bit_width, 32);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                let new_ident = self.create_var();
                let witness_placer_ident = &self.witness_placer_ident;
                quote! {
                    let #new_ident = #witness_placer_ident::#type_ident::div_rem_assume_nonzero_divisor(& #lhs, & #rhs).1;
                }
            }
            FixedWidthIntegerNodeExpression::AddProduct {
                additive_term,
                mul_0,
                mul_1,
            } => {
                let type_ident = Self::ident_for_integer_binop(&additive_term, &mul_0);
                let _ = Self::ident_for_integer_binop(&additive_term, &mul_1);
                let additive_term = self.integer_expr_into_var(additive_term);
                let mul_0 = self.integer_expr_into_var(mul_0);
                let mul_1 = self.integer_expr_into_var(mul_1);
                let new_ident = self.create_var();
                let witness_placer_ident = &self.witness_placer_ident;
                quote! {
                    let mut #new_ident = #additive_term;
                    #witness_placer_ident::#type_ident::add_assign_product(&mut #new_ident, & #mul_0, & #mul_1);
                }
            }
            FixedWidthIntegerNodeExpression::SignedDivAssumeNonzeroNoOverflowBits { lhs, rhs } => {
                let _ = Self::ident_for_integer_binop(lhs, rhs);
                let bit_width = lhs.bit_width();
                assert_eq!(bit_width, 32);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                let new_ident = self.create_var();
                let witness_placer_ident = &self.witness_placer_ident;
                quote! {
                    let #new_ident = #witness_placer_ident::I32::div_rem_assume_nonzero_divisor_no_overflow(& #lhs, & #rhs).0;
                }
            }
            FixedWidthIntegerNodeExpression::SignedRemAssumeNonzeroNoOverflowBits { lhs, rhs } => {
                let _ = Self::ident_for_integer_binop(lhs, rhs);
                let bit_width = lhs.bit_width();
                assert_eq!(bit_width, 32);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                let new_ident = self.create_var();
                let witness_placer_ident = &self.witness_placer_ident;
                quote! {
                    let #new_ident = #witness_placer_ident::I32::div_rem_assume_nonzero_divisor_no_overflow(& #lhs, & #rhs).1;
                }
            }
            FixedWidthIntegerNodeExpression::SignedMulLowBits { lhs, rhs } => {
                let _ = Self::ident_for_integer_binop(lhs, rhs);
                let bit_width = lhs.bit_width();
                assert_eq!(bit_width, 32);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                let new_ident = self.create_var();
                let witness_placer_ident = &self.witness_placer_ident;
                quote! {
                    let #new_ident = #witness_placer_ident::I32::widening_product_bits(& #lhs, & #rhs).0;
                }
            }
            FixedWidthIntegerNodeExpression::SignedMulHighBits { lhs, rhs } => {
                let _ = Self::ident_for_integer_binop(lhs, rhs);
                let bit_width = lhs.bit_width();
                assert_eq!(bit_width, 32);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                let new_ident = self.create_var();
                let witness_placer_ident = &self.witness_placer_ident;
                quote! {
                    let #new_ident = #witness_placer_ident::I32::widening_product_bits(& #lhs, & #rhs).1;
                }
            }
            FixedWidthIntegerNodeExpression::SignedByUnsignedMulLowBits { lhs, rhs } => {
                let _ = Self::ident_for_integer_binop(lhs, rhs);
                let bit_width = lhs.bit_width();
                assert_eq!(bit_width, 32);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                let new_ident = self.create_var();
                let witness_placer_ident = &self.witness_placer_ident;
                quote! {
                    let #new_ident = #witness_placer_ident::I32::mixed_widening_product_bits(& #lhs, & #rhs).0;
                }
            }
            FixedWidthIntegerNodeExpression::SignedByUnsignedMulHighBits { lhs, rhs } => {
                let _ = Self::ident_for_integer_binop(lhs, rhs);
                let bit_width = lhs.bit_width();
                assert_eq!(bit_width, 32);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                let new_ident = self.create_var();
                let witness_placer_ident = &self.witness_placer_ident;
                quote! {
                    let #new_ident = #witness_placer_ident::I32::mixed_widening_product_bits(& #lhs, & #rhs).1;
                }
            }
        };

        self.stream.extend(t);
    }
}
