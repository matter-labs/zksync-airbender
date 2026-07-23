use super::*;

impl Generator {
    pub(crate) fn ident_for_integer_unop(lhs: &FixedWidthIntegerNodeExpression<F>) -> &'static str {
        let lhs = lhs.bit_width();
        match lhs {
            8 => "u8",
            16 => "u16",
            32 => "u32",
            a => {
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
                self.emit_place_read("u8", variable);
            }
            FixedWidthIntegerNodeExpression::U16Place(variable) => {
                self.emit_place_read("u16", variable);
            }
            FixedWidthIntegerNodeExpression::U8SubExpression(_usize)
            | FixedWidthIntegerNodeExpression::U16SubExpression(_usize)
            | FixedWidthIntegerNodeExpression::U32SubExpression(_usize) => {
                unreachable!("not supported at the upper level");
            }
            FixedWidthIntegerNodeExpression::U32OracleValue { placeholder } => {
                self.emit_oracle_value("u32", placeholder);
            }
            FixedWidthIntegerNodeExpression::U16OracleValue { placeholder } => {
                self.emit_oracle_value("u16", placeholder);
            }
            FixedWidthIntegerNodeExpression::U8OracleValue { placeholder } => {
                self.emit_oracle_value("u8", placeholder);
            }
            FixedWidthIntegerNodeExpression::ConstantU8(constant) => {
                self.emit_constant("u8", *constant);
            }
            FixedWidthIntegerNodeExpression::ConstantU16(constant) => {
                self.emit_constant("u16", *constant);
            }
            FixedWidthIntegerNodeExpression::ConstantU32(constant) => {
                self.emit_constant("u32", *constant);
            }
            FixedWidthIntegerNodeExpression::U32FromMask(expr) => {
                let var_ident = self.boolean_expr_into_var(expr);
                self.emit("FROM", Some("u32"), &[var_ident]);
            }
            FixedWidthIntegerNodeExpression::U32FromField(expr) => {
                let var_ident = self.field_expr_into_var(expr);
                self.emit("FROM", Some("u32"), &[var_ident]);
            }
            FixedWidthIntegerNodeExpression::U32RawReprReducedFromField(expr) => {
                let var_ident = self.field_expr_into_var(expr);
                self.emit("RAW_REPR_REDUCED_FROM_FIELD", Some("u32"), &[var_ident]);
            }
            FixedWidthIntegerNodeExpression::WidenFromU8(expr) => {
                let var_ident = self.integer_expr_into_var(expr);
                self.emit("FROM", Some("u16"), &[var_ident]);
            }
            FixedWidthIntegerNodeExpression::WidenFromU16(expr) => {
                let var_ident = self.integer_expr_into_var(expr);
                self.emit("FROM", Some("u32"), &[var_ident]);
            }
            FixedWidthIntegerNodeExpression::TruncateFromU16(expr) => {
                let var_ident = self.integer_expr_into_var(expr);
                self.emit("FROM", Some("u8"), &[var_ident]);
            }
            FixedWidthIntegerNodeExpression::TruncateFromU32(expr) => {
                let var_ident = self.integer_expr_into_var(expr);
                self.emit("FROM", Some("u16"), &[var_ident]);
            }
            FixedWidthIntegerNodeExpression::I32FromU32(expr) => {
                let var_ident = self.integer_expr_into_var(expr);
                self.emit("FROM", Some("i32"), &[var_ident]);
            }
            FixedWidthIntegerNodeExpression::U32FromI32(expr) => {
                let var_ident = self.integer_expr_into_var(expr);
                self.emit("FROM", Some("u32"), &[var_ident]);
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
                self.emit("SELECT", Some(type_ident), &[selector, if_true, if_false]);
            }
            FixedWidthIntegerNodeExpression::WrappingAdd { lhs, rhs } => {
                let type_ident = Self::ident_for_integer_binop(lhs, rhs);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                self.emit("ADD", Some(type_ident), &[lhs, rhs]);
            }
            FixedWidthIntegerNodeExpression::WrappingSub { lhs, rhs } => {
                let type_ident = Self::ident_for_integer_binop(lhs, rhs);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                self.emit("SUB", Some(type_ident), &[lhs, rhs]);
            }
            FixedWidthIntegerNodeExpression::WrappingShl { lhs, magnitude } => {
                let type_ident = Self::ident_for_integer_unop(lhs);
                let lhs = self.integer_expr_into_var(lhs);
                let literal = *magnitude as usize;
                self.emit("SHL", Some(type_ident), &[lhs, literal]);
            }
            FixedWidthIntegerNodeExpression::WrappingShr { lhs, magnitude } => {
                let type_ident = Self::ident_for_integer_unop(lhs);
                let lhs = self.integer_expr_into_var(lhs);
                let literal = *magnitude as usize;
                self.emit("SHR", Some(type_ident), &[lhs, literal]);
            }
            FixedWidthIntegerNodeExpression::BinaryNot(value) => {
                let type_ident = Self::ident_for_integer_unop(value);
                let value = self.integer_expr_into_var(value);
                self.emit("INOT", Some(type_ident), &[value]);
            }
            FixedWidthIntegerNodeExpression::LowestBits { value, num_bits } => {
                let type_ident = Self::ident_for_integer_unop(value);
                let lhs = self.integer_expr_into_var(value);
                let literal = *num_bits as usize;
                self.emit("LOWEST_BITS", Some(type_ident), &[lhs, literal]);
            }
            FixedWidthIntegerNodeExpression::MulLow { lhs, rhs } => {
                let type_ident = Self::ident_for_integer_binop(lhs, rhs);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                self.emit("MUL_LOW", Some(type_ident), &[lhs, rhs]);
            }
            FixedWidthIntegerNodeExpression::MulHigh { lhs, rhs } => {
                let type_ident = Self::ident_for_integer_binop(lhs, rhs);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                self.emit("MUL_HIGH", Some(type_ident), &[lhs, rhs]);
            }
            FixedWidthIntegerNodeExpression::DivAssumeNonzero { lhs, rhs } => {
                let type_ident = Self::ident_for_integer_binop(lhs, rhs);
                let bit_width = lhs.bit_width();
                assert_eq!(bit_width, 32);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                self.emit("DIV", Some(type_ident), &[lhs, rhs]);
            }
            FixedWidthIntegerNodeExpression::RemAssumeNonzero { lhs, rhs } => {
                let type_ident = Self::ident_for_integer_binop(lhs, rhs);
                let bit_width = lhs.bit_width();
                assert_eq!(bit_width, 32);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                self.emit("REM", Some(type_ident), &[lhs, rhs]);
            }
            FixedWidthIntegerNodeExpression::AddProduct {
                additive_term,
                mul_0,
                mul_1,
            } => {
                let type_ident = Self::ident_for_integer_binop(additive_term, mul_0);
                let additive_term = self.integer_expr_into_var(additive_term);
                let mul_0 = self.integer_expr_into_var(mul_0);
                let mul_1 = self.integer_expr_into_var(mul_1);
                self.emit("MUL_ADD", Some(type_ident), &[mul_0, mul_1, additive_term]);
            }
            FixedWidthIntegerNodeExpression::SignedDivAssumeNonzeroNoOverflowBits { lhs, rhs } => {
                let _ = Self::ident_for_integer_binop(lhs, rhs);
                let bit_width = lhs.bit_width();
                assert_eq!(bit_width, 32);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                self.emit("DIV", Some("i32"), &[lhs, rhs]);
            }
            FixedWidthIntegerNodeExpression::SignedRemAssumeNonzeroNoOverflowBits { lhs, rhs } => {
                let _ = Self::ident_for_integer_binop(lhs, rhs);
                let bit_width = lhs.bit_width();
                assert_eq!(bit_width, 32);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                self.emit("REM", Some("i32"), &[lhs, rhs]);
            }
            FixedWidthIntegerNodeExpression::SignedMulLowBits { lhs, rhs } => {
                let _ = Self::ident_for_integer_binop(lhs, rhs);
                let bit_width = lhs.bit_width();
                assert_eq!(bit_width, 32);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                self.emit("SIGNED_MUL_LOW", None, &[lhs, rhs]);
            }
            FixedWidthIntegerNodeExpression::SignedMulHighBits { lhs, rhs } => {
                let _ = Self::ident_for_integer_binop(lhs, rhs);
                let bit_width = lhs.bit_width();
                assert_eq!(bit_width, 32);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                self.emit("SIGNED_MUL_HIGH", None, &[lhs, rhs]);
            }
            FixedWidthIntegerNodeExpression::SignedByUnsignedMulLowBits { lhs, rhs } => {
                let _ = Self::ident_for_integer_binop(lhs, rhs);
                let bit_width = lhs.bit_width();
                assert_eq!(bit_width, 32);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                self.emit("MIXED_MUL_LOW", None, &[lhs, rhs]);
            }
            FixedWidthIntegerNodeExpression::SignedByUnsignedMulHighBits { lhs, rhs } => {
                let _ = Self::ident_for_integer_binop(lhs, rhs);
                let bit_width = lhs.bit_width();
                assert_eq!(bit_width, 32);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                self.emit("MIXED_MUL_HIGH", None, &[lhs, rhs]);
            }
            FixedWidthIntegerNodeExpression::BinaryAnd { lhs, rhs } => {
                let type_ident = Self::ident_for_integer_binop(lhs, rhs);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                self.emit("IAND", Some(type_ident), &[lhs, rhs]);
            }
            FixedWidthIntegerNodeExpression::BinaryOr { lhs, rhs } => {
                let type_ident = Self::ident_for_integer_binop(lhs, rhs);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                self.emit("IOR", Some(type_ident), &[lhs, rhs]);
            }
            FixedWidthIntegerNodeExpression::BinaryXor { lhs, rhs } => {
                let type_ident = Self::ident_for_integer_binop(lhs, rhs);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                self.emit("IXOR", Some(type_ident), &[lhs, rhs]);
            }
        };
    }
}
