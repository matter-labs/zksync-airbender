use super::*;
use cs::witness_placer::graph_description::BoolNodeExpression;

impl Generator {
    pub(crate) fn add_boolean_expr(&mut self, expr: &BoolNodeExpression<F>) {
        match expr {
            BoolNodeExpression::Place(variable) => {
                self.emit_place_read("b", variable);
            }
            BoolNodeExpression::OracleValue { placeholder } => {
                self.emit_oracle_value("b", placeholder);
            }
            BoolNodeExpression::SubExpression(_usize) => {
                unreachable!("not supported at the upper level");
            }
            BoolNodeExpression::Constant(constant) => {
                self.emit_constant("b", *constant);
            }
            BoolNodeExpression::FromGenericInteger(expr) => {
                let var_ident = self.integer_expr_into_var(expr);
                self.emit("FROM", Some("b"), &[var_ident]);
            }
            BoolNodeExpression::FromField(expr) => {
                let var_ident = self.field_expr_into_var(expr);
                self.emit("FROM", Some("b"), &[var_ident]);
            }
            BoolNodeExpression::FromGenericIntegerEquality { lhs, rhs } => {
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                self.emit("B_FROM_INTEGER_EQUALITY", None, &[lhs, rhs]);
            }
            BoolNodeExpression::FromGenericIntegerCarry { lhs, rhs } => {
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                self.emit("B_FROM_INTEGER_CARRY", None, &[lhs, rhs]);
            }
            BoolNodeExpression::FromGenericIntegerBorrow { lhs, rhs } => {
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                self.emit("B_FROM_INTEGER_BORROW", None, &[lhs, rhs]);
            }
            BoolNodeExpression::FromFieldEquality { lhs, rhs } => {
                let lhs = self.field_expr_into_var(lhs);
                let rhs = self.field_expr_into_var(rhs);
                self.emit("B_FROM_FIELD_EQUALITY", None, &[lhs, rhs]);
            }
            BoolNodeExpression::And { lhs, rhs } => {
                let lhs = self.boolean_expr_into_var(lhs);
                let rhs = self.boolean_expr_into_var(rhs);
                self.emit("AND", None, &[lhs, rhs]);
            }
            BoolNodeExpression::Or { lhs, rhs } => {
                let lhs = self.boolean_expr_into_var(lhs);
                let rhs = self.boolean_expr_into_var(rhs);
                self.emit("OR", None, &[lhs, rhs]);
            }
            BoolNodeExpression::Select {
                selector,
                if_true,
                if_false,
            } => {
                let selector = self.boolean_expr_into_var(selector);
                let if_true = self.boolean_expr_into_var(if_true);
                let if_false = self.boolean_expr_into_var(if_false);
                self.emit("SELECT", Some("b"), &[selector, if_true, if_false]);
            }
            BoolNodeExpression::Negate(expr) => {
                let var_ident = self.boolean_expr_into_var(expr);
                self.emit("NEGATE", None, &[var_ident]);
            }
        };
    }
}
