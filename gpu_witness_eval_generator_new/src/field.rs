use super::*;

impl Generator {
    pub(crate) fn add_field_expr(&mut self, expr: &FieldNodeExpression<F>) {
        match expr {
            FieldNodeExpression::Place(variable) => {
                let new_ident = self.create_var();
                let address = self.get_column_address(variable);
                match address {
                    ColumnAddress::WitnessSubtree(idx) => {
                        self.push(&format!("GET_WITNESS_PLACE(f, {new_ident}, {idx})\n"));
                    }
                    ColumnAddress::MemorySubtree(idx) => {
                        self.push(&format!("GET_MEMORY_PLACE(f, {new_ident}, {idx})\n"));
                    }
                    ColumnAddress::SetupSubtree(_idx) => {
                        todo!();
                    }
                    ColumnAddress::OptimizedOut(idx) => {
                        assert!(self.scratch_size > idx);
                        self.push(&format!("GET_SCRATCH_PLACE(f, {new_ident}, {idx})\n"));
                    }
                }
            }
            FieldNodeExpression::SubExpression(_usize) => {
                unreachable!("not supported at the upper level");
            }
            FieldNodeExpression::Constant(constant) => {
                let new_ident = self.create_var();
                let literal = *constant;
                self.push(&format!("CONSTANT(f, {new_ident}, {literal})\n"));
            }
            FieldNodeExpression::FromInteger(expr) => {
                let var_ident = self.integer_expr_into_var(expr);
                let new_ident = self.create_var();
                self.push(&format!("FROM(f, {new_ident}, {var_ident})\n"));
            }
            FieldNodeExpression::FromMask(expr) => {
                let var_ident = self.boolean_expr_into_var(expr);
                let new_ident = self.create_var();
                self.push(&format!("FROM(f, {new_ident}, {var_ident})\n"));
            }
            FieldNodeExpression::OracleValue {
                placeholder,
                subindex: _,
            } => {
                let new_ident = self.create_var();
                let placeholder_ident = Self::get_placeholder_ident(placeholder);
                self.push(&format!(
                    "GET_ORACLE_VALUE(f, {new_ident}, {placeholder_ident})\n"
                ));
            }
            FieldNodeExpression::Add { lhs, rhs } => {
                let lhs = self.field_expr_into_var(lhs);
                let rhs = self.field_expr_into_var(rhs);
                let new_ident = self.create_var();
                self.push(&format!("ADD(f, {new_ident}, {lhs}, {rhs})\n"));
            }
            FieldNodeExpression::Sub { lhs, rhs } => {
                let lhs = self.field_expr_into_var(lhs);
                let rhs = self.field_expr_into_var(rhs);
                let new_ident = self.create_var();
                self.push(&format!("SUB(f, {new_ident}, {lhs}, {rhs})\n"));
            }
            FieldNodeExpression::Mul { lhs, rhs } => {
                let lhs = self.field_expr_into_var(lhs);
                let rhs = self.field_expr_into_var(rhs);
                let new_ident = self.create_var();
                self.push(&format!("MUL(f, {new_ident}, {lhs}, {rhs})\n"));
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
                self.push(&format!(
                    "MUL_ADD(f, {new_ident}, {mul_0}, {mul_1}, {additive_term})\n"
                ));
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
                self.push(&format!(
                    "SELECT(f, {new_ident}, {selector}, {if_true}, {if_false})\n"
                ));
            }
            FieldNodeExpression::InverseUnchecked(expr) => {
                let var_ident = self.field_expr_into_var(expr);
                let new_ident = self.create_var();
                self.push(&format!("INV(f, {new_ident}, {var_ident})\n"));
            }
            FieldNodeExpression::InverseOrZero(expr) => {
                let var_ident = self.field_expr_into_var(expr);
                let new_ident = self.create_var();
                self.push(&format!("INV(f, {new_ident}, {var_ident})\n"));
            }
            FieldNodeExpression::LookupOutput { .. } => {
                unreachable!("not supported at the upper level");
            }
            FieldNodeExpression::MaybeLookupOutput { .. } => {
                unreachable!("not supported at the upper level");
            }
        };
    }
}
