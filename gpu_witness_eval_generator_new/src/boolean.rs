use super::*;
use cs::cs::witness_placer::graph_description::BoolNodeExpression;
use cs::definitions::ColumnAddress;

impl Generator {
    pub(crate) fn add_boolean_expr(&mut self, expr: &BoolNodeExpression<F>) {
        match expr {
            BoolNodeExpression::Place(variable) => {
                let new_ident = self.create_var();
                let address = self.get_column_address(variable);
                match address {
                    ColumnAddress::WitnessSubtree(idx) => {
                        self.push(&format!("GET_WITNESS_PLACE(b, {new_ident}, {idx})\n"));
                    }
                    ColumnAddress::MemorySubtree(idx) => {
                        self.push(&format!("GET_MEMORY_PLACE(b, {new_ident}, {idx})\n"));
                    }
                    ColumnAddress::SetupSubtree(_idx) => {
                        todo!();
                    }
                    ColumnAddress::OptimizedOut(idx) => {
                        assert!(self.scratch_size > idx);
                        self.push(&format!("GET_SCRATCH_PLACE(b, {new_ident}, {idx})\n"));
                    }
                }
            }
            BoolNodeExpression::OracleValue { placeholder } => {
                let new_ident = self.create_var();
                let placeholder_ident = Self::get_placeholder_ident(placeholder);
                self.push(&format!(
                    "GET_ORACLE_VALUE(b, {new_ident}, {placeholder_ident})\n"
                ));
            }
            BoolNodeExpression::SubExpression(_usize) => {
                unreachable!("not supported at the upper level");
            }
            BoolNodeExpression::Constant(constant) => {
                let new_ident = self.create_var();
                let literal = *constant;
                self.push(&format!("CONSTANT(b, {new_ident}, {literal})\n"));
            }
            BoolNodeExpression::FromGenericInteger(expr) => {
                let var_ident = self.integer_expr_into_var(expr);
                let new_ident = self.create_var();
                self.push(&format!("FROM(b, {new_ident}, {var_ident})\n"));
            }
            BoolNodeExpression::FromField(expr) => {
                let var_ident = self.field_expr_into_var(expr);
                let new_ident = self.create_var();
                self.push(&format!("FROM(b, {new_ident}, {var_ident})\n"));
            }
            BoolNodeExpression::FromGenericIntegerEquality { lhs, rhs } => {
                // let type_ident = Self::ident_for_integer_binop(lhs, rhs);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                let new_ident = self.create_var();
                self.push(&format!(
                    "B_FROM_INTEGER_EQUALITY({new_ident}, {lhs}, {rhs})\n"
                ));
            }
            BoolNodeExpression::FromGenericIntegerCarry { lhs, rhs } => {
                // let type_ident = Self::ident_for_integer_binop(lhs, rhs);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                let new_ident = self.create_var();
                self.push(&format!(
                    "B_FROM_INTEGER_CARRY({new_ident}, {lhs}, {rhs})\n"
                ));
            }
            BoolNodeExpression::FromGenericIntegerBorrow { lhs, rhs } => {
                // let type_ident = Self::ident_for_integer_binop(lhs, rhs);
                let lhs = self.integer_expr_into_var(lhs);
                let rhs = self.integer_expr_into_var(rhs);
                let new_ident = self.create_var();
                self.push(&format!(
                    "B_FROM_INTEGER_BORROW({new_ident}, {lhs}, {rhs})\n"
                ));
            }
            BoolNodeExpression::FromFieldEquality { lhs, rhs } => {
                let lhs = self.field_expr_into_var(lhs);
                let rhs = self.field_expr_into_var(rhs);
                let new_ident = self.create_var();
                self.push(&format!(
                    "B_FROM_FIELD_EQUALITY({new_ident}, {lhs}, {rhs})\n"
                ));
            }
            BoolNodeExpression::And { lhs, rhs } => {
                let lhs = self.boolean_expr_into_var(lhs);
                let rhs = self.boolean_expr_into_var(rhs);
                let new_ident = self.create_var();
                self.push(&format!("AND({new_ident}, {lhs}, {rhs})\n"));
            }
            BoolNodeExpression::Or { lhs, rhs } => {
                let lhs = self.boolean_expr_into_var(lhs);
                let rhs = self.boolean_expr_into_var(rhs);
                let new_ident = self.create_var();
                self.push(&format!("OR({new_ident}, {lhs}, {rhs})\n"));
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
                self.push(&format!(
                    "SELECT(b, {new_ident}, {selector}, {if_true}, {if_false})\n"
                ));
            }
            BoolNodeExpression::Negate(expr) => {
                let var_ident = self.boolean_expr_into_var(expr);
                let new_ident = self.create_var();
                self.push(&format!("NEGATE({new_ident}, {var_ident})\n"));
            }
        };
    }
}
