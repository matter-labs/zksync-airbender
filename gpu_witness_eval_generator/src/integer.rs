use super::*;

impl Generator {
    pub(crate) fn ident_for_integer_unop(lhs: &FixedWidthIntegerNodeExpression<F>) -> &'static str {
        let lhs = lhs.bit_width();
        match lhs {
            8 => "u8",
            16 => "u16",
            32 => "u32",
            a @ _ => {
                panic!("unknown bit width {}", a);
            }
        }
    }

    pub(crate) fn ident_for_integer_binop(
        lhs: &FixedWidthIntegerNodeExpression<F>,
        rhs: &FixedWidthIntegerNodeExpression<F>,
    ) -> &'static str {
        let lhs_width = lhs.bit_width();
        let rhs_width = rhs.bit_width();
        assert_eq!(lhs_width, rhs_width);
        Self::ident_for_integer_unop(lhs)
    }

    pub(crate) fn add_integer_expr(&mut self, expr: &FixedWidthIntegerNodeExpression<F>) {
        match expr {
            FixedWidthIntegerNodeExpression::U8Place(variable) => {
                let new_ident = self.create_var();
                let address = self.get_column_address(variable);
                match address {
                    ColumnAddress::WitnessSubtree(idx) => {
                        self.push(&format!("GET_WITNESS_PLACE(u8, {new_ident}, {idx})\n"));
                    }
                    ColumnAddress::MemorySubtree(idx) => {
                        self.push(&format!("GET_MEMORY_PLACE(u8, {new_ident}, {idx})\n"));
                    }
                    ColumnAddress::SetupSubtree(_idx) => {
                        todo!();
                    }
                    ColumnAddress::OptimizedOut(idx) => {
                        assert!(self.scratch_size > idx);
                        self.push(&format!("GET_SCRATCH_PLACE(u8, {new_ident}, {idx})\n"));
                    }
                }
            }
            FixedWidthIntegerNodeExpression::U16Place(variable) => {
                let new_ident = self.create_var();
                let address = self.get_column_address(variable);
                match address {
                    ColumnAddress::WitnessSubtree(idx) => {
                        self.push(&format!("GET_WITNESS_PLACE(u16, {new_ident}, {idx})\n"));
                    }
                    ColumnAddress::MemorySubtree(idx) => {
                        self.push(&format!("GET_MEMORY_PLACE(u16, {new_ident}, {idx})\n"));
                    }
                    ColumnAddress::SetupSubtree(_idx) => {
                        todo!();
                    }
                    ColumnAddress::OptimizedOut(idx) => {
                        assert!(self.scratch_size > idx);
                        self.push(&format!("GET_SCRATCH_PLACE(u16, {new_ident}, {idx})\n"));
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
                let placeholder_ident = Self::get_placeholder_ident(placeholder);
                self.push(&format!(
                    "GET_ORACLE_VALUE(u32, {new_ident}, {placeholder_ident})\n"
                ));
            }
            FixedWidthIntegerNodeExpression::U16OracleValue { placeholder } => {
                let new_ident = self.create_var();
                let placeholder_ident = Self::get_placeholder_ident(placeholder);
                self.push(&format!(
                    "GET_ORACLE_VALUE(u16, {new_ident}, {placeholder_ident})\n"
                ));
            }
            FixedWidthIntegerNodeExpression::U8OracleValue { placeholder } => {
                let new_ident = self.create_var();
                let placeholder_ident = Self::get_placeholder_ident(placeholder);
                self.push(&format!(
                    "GET_ORACLE_VALUE(u8, {new_ident}, {placeholder_ident})\n"
                ));
            }
            FixedWidthIntegerNodeExpression::ConstantU8(constant) => {
                let new_ident = self.create_var();
                let literal = *constant;
                self.push(&format!("CONSTANT(u8, {new_ident}, {literal})\n"));
            }
            FixedWidthIntegerNodeExpression::ConstantU16(constant) => {
                let new_ident = self.create_var();
                let literal = *constant;
                self.push(&format!("CONSTANT(u16, {new_ident}, {literal})\n"));
            }
            FixedWidthIntegerNodeExpression::ConstantU32(constant) => {
                let new_ident = self.create_var();
                let literal = *constant;
                self.push(&format!("CONSTANT(u32, {new_ident}, {literal})\n"));
            }
            FixedWidthIntegerNodeExpression::U32FromMask(expr) => {
                let var_ident = self.boolean_expr_into_var(expr);
                let new_ident = self.create_var();
                self.push(&format!("FROM(u32, {new_ident}, {var_ident})\n"));
            }
            FixedWidthIntegerNodeExpression::U32FromField(expr) => {
                let var_ident = self.field_expr_into_var(expr);
                let new_ident = self.create_var();
                self.push(&format!("FROM(u32, {new_ident}, {var_ident})\n"));
            }
            FixedWidthIntegerNodeExpression::WidenFromU8(expr) => {
                let var_ident = self.integer_expr_into_var(expr);
                let new_ident = self.create_var();
                self.push(&format!("FROM(u16, {new_ident}, {var_ident})\n"));
            }
            FixedWidthIntegerNodeExpression::WidenFromU16(expr) => {
                let var_ident = self.integer_expr_into_var(expr);
                let new_ident = self.create_var();
                self.push(&format!("FROM(u32, {new_ident}, {var_ident})\n"));
            }
            FixedWidthIntegerNodeExpression::TruncateFromU16(expr) => {
                let var_ident = self.integer_expr_into_var(expr);
                let new_ident = self.create_var();
                self.push(&format!("FROM(u8, {new_ident}, {var_ident})\n"));
            }
            FixedWidthIntegerNodeExpression::TruncateFromU32(expr) => {
                let var_ident = self.integer_expr_into_var(expr);
                let new_ident = self.create_var();
                self.push(&format!("FROM(u16, {new_ident}, {var_ident})\n"));
            }
            FixedWidthIntegerNodeExpression::I32FromU32(expr) => {
                let var_ident = self.integer_expr_into_var(expr);
                let new_ident = self.create_var();
                self.push(&format!("FROM(i32, {new_ident}, {var_ident})\n"));
            }
            FixedWidthIntegerNodeExpression::U32FromI32(expr) => {
                let var_ident = self.integer_expr_into_var(expr);
                let new_ident = self.create_var();
                self.push(&format!("FROM(u32, {new_ident}, {var_ident})\n"));
            }
            FixedWidthIntegerNodeExpression::Select {
                selector,
                if_true,
                if_false,
            } => {
                let type_ident = Self::ident_for_integer_binop(if_true, if_false);
                let selector = self.boolean_expr_into_var(selector);
                let if_true = self.integer_expr_into_var(if_true);
                let if_false = self.integer_expr_into_var(if_false);
                let new_ident = self.create_var();
                self.push(&format!(
                    "SELECT({type_ident}, {new_ident}, {selector}, {if_true}, {if_false})\n"
                ));
            }
            FixedWidthIntegerNodeExpression::WrappingAdd { lhs, rhs } => {
                let type_ident = Self::ident_for_integer_binop(lhs, rhs);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                let new_ident = self.create_var();
                self.push(&format!("ADD({type_ident}, {new_ident}, {lhs}, {rhs})\n"));
            }
            FixedWidthIntegerNodeExpression::WrappingSub { lhs, rhs } => {
                let type_ident = Self::ident_for_integer_binop(lhs, rhs);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                let new_ident = self.create_var();
                self.push(&format!("SUB({type_ident}, {new_ident}, {lhs}, {rhs})\n"));
            }
            FixedWidthIntegerNodeExpression::WrappingShl { lhs, magnitude } => {
                let type_ident = Self::ident_for_integer_unop(lhs);
                let lhs = self.integer_expr_into_var(lhs);
                let literal = *magnitude;
                let new_ident = self.create_var();
                self.push(&format!(
                    "SHL({type_ident}, {new_ident}, {lhs}, {literal})\n"
                ));
            }
            FixedWidthIntegerNodeExpression::WrappingShr { lhs, magnitude } => {
                let type_ident = Self::ident_for_integer_unop(lhs);
                let lhs = self.integer_expr_into_var(lhs);
                let literal = *magnitude;
                let new_ident = self.create_var();
                self.push(&format!(
                    "SHR({type_ident}, {new_ident}, {lhs}, {literal})\n"
                ));
            }
            FixedWidthIntegerNodeExpression::BinaryNot(lhs) => {
                let type_ident = Self::ident_for_integer_unop(lhs);
                let lhs = self.integer_expr_into_var(lhs);
                let new_ident = self.create_var();
                self.push(&format!("INOT({type_ident}, {new_ident}, {lhs})\n"));
            }
            FixedWidthIntegerNodeExpression::LowestBits { value, num_bits } => {
                let type_ident = Self::ident_for_integer_unop(value);
                let lhs = self.integer_expr_into_var(value);
                let literal = *num_bits;
                let new_ident = self.create_var();
                // assert!(lhs != new_ident);
                self.push(&format!(
                    "LOWEST_BITS({type_ident}, {new_ident}, {lhs}, {literal})\n"
                ));
            }
            FixedWidthIntegerNodeExpression::MulLow { lhs, rhs } => {
                let type_ident = Self::ident_for_integer_binop(lhs, rhs);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                let new_ident = self.create_var();
                self.push(&format!(
                    "MUL_LOW({type_ident}, {new_ident}, {lhs}, {rhs})\n"
                ));
            }
            FixedWidthIntegerNodeExpression::MulHigh { lhs, rhs } => {
                let type_ident = Self::ident_for_integer_binop(lhs, rhs);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                let new_ident = self.create_var();
                self.push(&format!(
                    "MUL_HIGH({type_ident}, {new_ident}, {lhs}, {rhs})\n"
                ));
            }
            FixedWidthIntegerNodeExpression::DivAssumeNonzero { lhs, rhs } => {
                let type_ident = Self::ident_for_integer_binop(lhs, rhs);
                let bit_width = lhs.bit_width();
                assert_eq!(bit_width, 32);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                let new_ident = self.create_var();
                self.push(&format!("DIV({type_ident}, {new_ident}, {lhs}, {rhs})\n"));
            }
            FixedWidthIntegerNodeExpression::RemAssumeNonzero { lhs, rhs } => {
                let type_ident = Self::ident_for_integer_binop(lhs, rhs);
                let bit_width = lhs.bit_width();
                assert_eq!(bit_width, 32);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                let new_ident = self.create_var();
                self.push(&format!("REM({type_ident}, {new_ident}, {lhs}, {rhs})\n"));
            }
            FixedWidthIntegerNodeExpression::AddProduct {
                additive_term,
                mul_0,
                mul_1,
            } => {
                let type_ident = Self::ident_for_integer_binop(&additive_term, &mul_0);
                let additive_term = self.integer_expr_into_var(additive_term);
                let mul_0 = self.integer_expr_into_var(mul_0);
                let mul_1 = self.integer_expr_into_var(mul_1);
                let new_ident = self.create_var();
                self.push(&format!(
                    "MUL_ADD({type_ident}, {new_ident}, {mul_0}, {mul_1}, {additive_term})\n"
                ));
            }
            FixedWidthIntegerNodeExpression::SignedDivAssumeNonzeroNoOverflowBits { lhs, rhs } => {
                let _ = Self::ident_for_integer_binop(lhs, rhs);
                let bit_width = lhs.bit_width();
                assert_eq!(bit_width, 32);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                let new_ident = self.create_var();
                self.push(&format!("DIV(i32, {new_ident}, {lhs}, {rhs})\n"));
            }
            FixedWidthIntegerNodeExpression::SignedRemAssumeNonzeroNoOverflowBits { lhs, rhs } => {
                let _ = Self::ident_for_integer_binop(lhs, rhs);
                let bit_width = lhs.bit_width();
                assert_eq!(bit_width, 32);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                let new_ident = self.create_var();
                self.push(&format!("REM(i32, {new_ident}, {lhs}, {rhs})\n"));
            }
            FixedWidthIntegerNodeExpression::SignedMulLowBits { lhs, rhs } => {
                let _ = Self::ident_for_integer_binop(lhs, rhs);
                let bit_width = lhs.bit_width();
                assert_eq!(bit_width, 32);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                let new_ident = self.create_var();
                self.push(&format!("SIGNED_MUL_LOW({new_ident}, {lhs}, {rhs})\n"));
            }
            FixedWidthIntegerNodeExpression::SignedMulHighBits { lhs, rhs } => {
                let _ = Self::ident_for_integer_binop(lhs, rhs);
                let bit_width = lhs.bit_width();
                assert_eq!(bit_width, 32);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                let new_ident = self.create_var();
                self.push(&format!("SIGNED_MUL_HIGH({new_ident}, {lhs}, {rhs})\n"));
            }
            FixedWidthIntegerNodeExpression::SignedByUnsignedMulLowBits { lhs, rhs } => {
                let _ = Self::ident_for_integer_binop(lhs, rhs);
                let bit_width = lhs.bit_width();
                assert_eq!(bit_width, 32);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                let new_ident = self.create_var();
                self.push(&format!("MIXED_MUL_LOW({new_ident}, {lhs}, {rhs})\n"));
            }
            FixedWidthIntegerNodeExpression::SignedByUnsignedMulHighBits { lhs, rhs } => {
                let _ = Self::ident_for_integer_binop(lhs, rhs);
                let bit_width = lhs.bit_width();
                assert_eq!(bit_width, 32);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                let new_ident = self.create_var();
                self.push(&format!("MIXED_MUL_HIGH({new_ident}, {lhs}, {rhs})\n"));
            }
            FixedWidthIntegerNodeExpression::BinaryAnd { lhs, rhs } => {
                let type_ident = Self::ident_for_integer_binop(lhs, rhs);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                let new_ident = self.create_var();
                self.push(&format!("IAND({type_ident}, {new_ident}, {lhs}, {rhs})\n"));
            }
            FixedWidthIntegerNodeExpression::BinaryOr { lhs, rhs } => {
                let type_ident = Self::ident_for_integer_binop(lhs, rhs);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                let new_ident = self.create_var();
                self.push(&format!("IOR({type_ident}, {new_ident}, {lhs}, {rhs})\n"));
            }
            FixedWidthIntegerNodeExpression::BinaryXor { lhs, rhs } => {
                let type_ident = Self::ident_for_integer_binop(lhs, rhs);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                let new_ident = self.create_var();
                self.push(&format!("IXOR({type_ident}, {new_ident}, {lhs}, {rhs})\n"));
            }
        };
    }
}
