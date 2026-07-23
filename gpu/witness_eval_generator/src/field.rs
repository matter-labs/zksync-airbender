use super::*;

impl Generator {
    pub(crate) fn add_field_expr(&mut self, expr: &FieldNodeExpression<F>) {
        match expr {
            FieldNodeExpression::Place(variable) => {
                self.emit_place_read("f", variable);
            }
            FieldNodeExpression::SubExpression(_usize) => {
                unreachable!("not supported at the upper level");
            }
            FieldNodeExpression::Constant(constant) => {
                self.emit_constant("f", *constant);
            }
            FieldNodeExpression::FromInteger(expr) => {
                let var_ident = self.integer_expr_into_var(expr);
                self.emit("FROM", Some("f"), &[var_ident]);
            }
            FieldNodeExpression::FromRawReprWithReduction(expr) => {
                let var_ident = self.integer_expr_into_var(expr);
                self.emit("FROM_RAW_REPR_WITH_REDUCTION", Some("f"), &[var_ident]);
            }
            FieldNodeExpression::FromMask(expr) => {
                let var_ident = self.boolean_expr_into_var(expr);
                self.emit("FROM", Some("f"), &[var_ident]);
            }
            FieldNodeExpression::OracleValue {
                placeholder,
                subindex: _,
            } => {
                self.emit_oracle_value("f", placeholder);
            }
            FieldNodeExpression::Add { lhs, rhs } => {
                let lhs = self.field_expr_into_var(lhs);
                let rhs = self.field_expr_into_var(rhs);
                self.emit("ADD", Some("f"), &[lhs, rhs]);
            }
            FieldNodeExpression::Sub { lhs, rhs } => {
                let lhs = self.field_expr_into_var(lhs);
                let rhs = self.field_expr_into_var(rhs);
                self.emit("SUB", Some("f"), &[lhs, rhs]);
            }
            FieldNodeExpression::Mul { lhs, rhs } => {
                let lhs = self.field_expr_into_var(lhs);
                let rhs = self.field_expr_into_var(rhs);
                self.emit("MUL", Some("f"), &[lhs, rhs]);
            }
            FieldNodeExpression::AddProduct {
                additive_term,
                mul_0,
                mul_1,
            } => {
                let additive_term = self.field_expr_into_var(additive_term);
                let mul_0 = self.field_expr_into_var(mul_0);
                let mul_1 = self.field_expr_into_var(mul_1);
                self.emit("MUL_ADD", Some("f"), &[mul_0, mul_1, additive_term]);
            }
            FieldNodeExpression::Select {
                selector,
                if_true,
                if_false,
            } => {
                let selector = self.boolean_expr_into_var(selector);
                let if_true = self.field_expr_into_var(if_true);
                let if_false = self.field_expr_into_var(if_false);
                self.emit("SELECT", Some("f"), &[selector, if_true, if_false]);
            }
            FieldNodeExpression::InverseUnchecked(expr) => {
                let var_ident = self.field_expr_into_var(expr);
                self.emit("INV", Some("f"), &[var_ident]);
            }
            FieldNodeExpression::InverseOrZero(expr) => {
                let var_ident = self.field_expr_into_var(expr);
                self.emit("INV", Some("f"), &[var_ident]);
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
