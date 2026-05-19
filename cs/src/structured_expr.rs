use crate::constraint::Constraint;
use crate::definitions::Variable;
use crate::types::{Boolean, Num};
use field::PrimeField;

/// Source-level arithmetic expression metadata for constraints.
///
/// `Constraint` intentionally stores a flattened sparse polynomial, so it is
/// useful for today's max-quadratic compiler path but cannot preserve authored
/// grouping such as `a * (b + c)`. `Expr` keeps that grouping around as metadata
/// while still being able to lower into the existing flat representation.
#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum Expr<F: PrimeField> {
    Constant(F),
    Var(Variable),
    Sum(Vec<Expr<F>>),
    Product(Vec<Expr<F>>),
}

/// Statement-level meaning for a structured expression.
///
/// The expression tree only describes arithmetic. The statement records whether
/// that arithmetic was an assertion or a directed variable definition.
#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum StructuredStatement<F: PrimeField> {
    AssertZero {
        expr: Expr<F>,
        prevent_optimizations: bool,
    },
    Define {
        dst: Variable,
        expr: Expr<F>,
    },
}

impl<F: PrimeField> Expr<F> {
    pub fn constant(value: F) -> Self {
        Self::Constant(value)
    }

    pub fn variable(variable: Variable) -> Self {
        Self::Var(variable)
    }

    pub fn zero() -> Self {
        Self::Constant(F::ZERO)
    }

    pub fn one() -> Self {
        Self::Constant(F::ONE)
    }

    pub fn degree(&self) -> usize {
        match self {
            Self::Constant(_) => 0,
            Self::Var(_) => 1,
            Self::Sum(terms) => terms.iter().map(Self::degree).max().unwrap_or(0),
            Self::Product(factors) => factors.iter().map(Self::degree).sum(),
        }
    }

    #[track_caller]
    pub fn validate_degree_at_most(&self, max_degree: usize) {
        let degree = self.degree();
        assert!(
            degree <= max_degree,
            "structured expression degree {degree} exceeds supported degree {max_degree}"
        );
    }

    pub fn canonicalize(self) -> Self {
        // TODO: Implement once the desired structured-expression normalization is known.
        self
    }

    /// Lower the expression into today's executable constraint representation.
    ///
    /// This deliberately rejects degree-3 and degree-4 expressions even though
    /// the metadata IR can represent them. The current compiler path normalizes
    /// constraints as max-quadratic polynomials, so accepting higher degree here
    /// would hide unsupported executable behavior behind valid metadata.
    #[track_caller]
    pub fn to_max_quadratic_constraint(&self) -> Constraint<F> {
        self.validate_degree_at_most(2);

        let mut constraint = self.to_constraint_unchecked();
        constraint.normalize();

        constraint
    }

    fn to_constraint_unchecked(&self) -> Constraint<F> {
        match self {
            Self::Constant(value) => Constraint::constant(*value),
            Self::Var(variable) => Constraint::from(*variable),
            Self::Sum(terms) => {
                let mut result = Constraint::empty();
                for term in terms {
                    result += term.to_constraint_unchecked();
                }

                result
            }
            Self::Product(factors) => {
                let mut result = Constraint::constant(F::ONE);
                for factor in factors {
                    result = result * factor.to_constraint_unchecked();
                }

                result
            }
        }
    }
}

impl<F: PrimeField> From<Variable> for Expr<F> {
    fn from(value: Variable) -> Self {
        Self::Var(value)
    }
}

impl<F: PrimeField> From<Num<F>> for Expr<F> {
    fn from(value: Num<F>) -> Self {
        match value {
            Num::Var(variable) => Self::Var(variable),
            Num::Constant(value) => Self::Constant(value),
        }
    }
}

impl<F: PrimeField> From<Boolean> for Expr<F> {
    fn from(value: Boolean) -> Self {
        match value {
            Boolean::Is(variable) => Self::Var(variable),
            Boolean::Not(variable) => Self::from(1u32) - Self::Var(variable),
            Boolean::Constant(value) => Self::from(value as u32),
        }
    }
}

impl<F: PrimeField> From<u32> for Expr<F> {
    fn from(value: u32) -> Self {
        Self::Constant(F::from_u32_with_reduction(value))
    }
}

impl<F: PrimeField> From<bool> for Expr<F> {
    fn from(value: bool) -> Self {
        Self::from(value as u32)
    }
}

impl<F: PrimeField> std::ops::Add for Expr<F> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self::Sum(vec![self, rhs])
    }
}

impl<F: PrimeField> std::ops::Sub for Expr<F> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        Self::Sum(vec![self, -rhs])
    }
}

impl<F: PrimeField> std::ops::Neg for Expr<F> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self::Product(vec![Self::Constant(F::MINUS_ONE), self])
    }
}

impl<F: PrimeField> std::ops::Mul for Expr<F> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        Self::Product(vec![self, rhs])
    }
}

impl<F: PrimeField> std::ops::Mul<F> for Expr<F> {
    type Output = Self;

    fn mul(self, rhs: F) -> Self::Output {
        Self::Product(vec![Self::Constant(rhs), self])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraint::Term;
    use crate::cs::circuit::RegisterAccessRequest;
    use crate::cs::circuit_impl::BasicAssembly;
    use crate::cs::circuit_trait::Circuit;
    use crate::definitions::LookupInput;
    use crate::gkr_compiler::GKRCompiler;
    use crate::tables::TableType;
    use crate::types::{Boolean, Num};
    use common_constants::TIMESTAMP_COLUMNS_NUM_BITS;
    use field::Mersenne31Field;

    type F = Mersenne31Field;

    fn var(index: u64) -> Variable {
        Variable(index)
    }

    #[test]
    fn preserves_authored_parentheses() {
        let a = var(0);
        let b = var(1);
        let c = var(2);
        let d = var(3);
        let e = var(4);
        let f = var(5);

        let expr = Expr::<F>::Product(vec![
            Expr::from(a),
            Expr::from(b),
            Expr::from(c),
            Expr::Sum(vec![Expr::from(d), Expr::from(e), Expr::from(f)]),
        ]);

        assert_eq!(expr.degree(), 4);
        assert_eq!(
            expr,
            Expr::Product(vec![
                Expr::Var(a),
                Expr::Var(b),
                Expr::Var(c),
                Expr::Sum(vec![Expr::Var(d), Expr::Var(e), Expr::Var(f)]),
            ])
        );
    }

    #[test]
    #[should_panic(expected = "structured expression degree 5 exceeds supported degree 4")]
    fn rejects_degree_above_structured_limit() {
        let expr = Expr::<F>::Product((0..5).map(var).map(Expr::from).collect());

        expr.validate_degree_at_most(4);
    }

    #[test]
    #[should_panic(expected = "structured expression degree 3 exceeds supported degree 2")]
    fn rejects_non_quadratic_expressions_for_current_constraint_lowering() {
        let expr = Expr::<F>::Product((0..3).map(var).map(Expr::from).collect());

        let _ = expr.to_max_quadratic_constraint();
    }

    #[test]
    fn lowers_quadratic_expr_to_flat_constraint() {
        let a = var(0);
        let b = var(1);
        let c = var(2);

        let expr = Expr::<F>::from(a) * (Expr::from(b) + Expr::from(c));
        let mut expected = Term::from(a) * Term::from(b) + Term::from(a) * Term::from(c);
        expected.normalize();

        assert_eq!(expr.to_max_quadratic_constraint(), expected);
    }

    #[test]
    fn expression_api_stores_metadata_and_flat_constraint() {
        let mut cs = BasicAssembly::<F>::new();
        let a = cs.add_named_variable("a");
        let b = cs.add_named_variable("b");
        let expr = Expr::<F>::from(a) * Expr::from(b);

        cs.add_constraint_expr(expr.clone());
        let (output, _) = cs.finalize();

        assert_eq!(output.constraints.len(), 1);
        assert_eq!(
            output.structured_statements,
            vec![StructuredStatement::AssertZero {
                expr,
                prevent_optimizations: false,
            }]
        );
    }

    #[test]
    fn variable_expression_api_stores_definition_metadata() {
        let mut cs = BasicAssembly::<F>::new();
        let a = cs.add_named_variable("a");
        let b = cs.add_named_variable("b");
        let expr = Expr::<F>::from(a) * Expr::from(b);

        let dst = cs.add_variable_from_expr(expr.clone());
        let (output, _) = cs.finalize();

        assert_eq!(
            output.structured_statements,
            vec![StructuredStatement::Define { dst, expr }]
        );
    }

    #[test]
    fn choose_records_structured_definition_metadata() {
        let mut cs = BasicAssembly::<F>::new();
        let cond = cs.add_named_boolean_variable("cond");
        let a = cs.add_named_variable("a");
        let b = cs.add_named_variable("b");

        let Num::Var(dst) = cs.choose(cond, Num::Var(a), Num::Var(b)) else {
            panic!("variable inputs should produce a variable output");
        };
        let Boolean::Is(cond) = cond else {
            panic!("named boolean variables are positive boolean views");
        };

        let expected_expr = Expr::<F>::from(cond) * (Expr::from(a) - Expr::from(b)) + Expr::from(b);
        let mut expected_flat_constraint = expected_expr.to_max_quadratic_constraint();
        expected_flat_constraint -= Term::from(dst);
        expected_flat_constraint.normalize();

        let (output, _) = cs.finalize();

        assert!(output
            .constraints
            .iter()
            .any(|(constraint, _)| constraint == &expected_flat_constraint));
        assert!(output
            .structured_statements
            .contains(&StructuredStatement::Define {
                dst,
                expr: expected_expr,
            }));
    }

    #[test]
    fn choose_records_structured_metadata_for_negated_flag_and_constant_input() {
        let mut cs = BasicAssembly::<F>::new();
        let cond = cs.add_named_boolean_variable("cond");
        let a = cs.add_named_variable("a");
        let constant = F::from_u32_unchecked(7);
        let flag = cond.toggle();

        let Num::Var(dst) = cs.choose(flag, Num::Constant(constant), Num::Var(a)) else {
            panic!("non-constant flag should produce a variable output");
        };

        let expected_expr = Expr::<F>::from(flag)
            * (Expr::from(Num::Constant(constant)) - Expr::from(Num::Var(a)))
            + Expr::from(Num::Var(a));
        let mut expected_flat_constraint = expected_expr.to_max_quadratic_constraint();
        expected_flat_constraint -= Term::from(dst);
        expected_flat_constraint.normalize();

        let (output, _) = cs.finalize();

        assert!(output
            .constraints
            .iter()
            .any(|(constraint, _)| constraint == &expected_flat_constraint));
        assert!(output
            .structured_statements
            .contains(&StructuredStatement::Define {
                dst,
                expr: expected_expr,
            }));
    }

    #[test]
    fn equals_to_identical_variable_folds_without_constraints() {
        let mut cs = BasicAssembly::<F>::new();
        let a = cs.add_named_variable("a");

        let is_equal = cs.equals_to(Num::Var(a), Num::Var(a));
        let (output, _) = cs.finalize();

        assert_eq!(is_equal, Boolean::Constant(true));
        assert!(output.constraints.is_empty());
        assert!(output.structured_statements.is_empty());
    }

    #[test]
    fn boolean_and_records_structured_definition_metadata() {
        let mut cs = BasicAssembly::<F>::new();
        let a = cs.add_named_boolean_variable("a");
        let b = cs.add_named_boolean_variable("b");
        let expr = Expr::<F>::from(a) * Expr::from(b.toggle());

        let Boolean::Is(dst) = Boolean::and::<F, _>(&a, &b.toggle(), &mut cs) else {
            panic!("non-constant boolean AND should produce a variable output");
        };
        let mut expected_flat_constraint = expr.to_max_quadratic_constraint();
        expected_flat_constraint -= Term::from(dst);
        expected_flat_constraint.normalize();

        let (output, _) = cs.finalize();

        assert!(output
            .constraints
            .iter()
            .any(|(constraint, _)| constraint == &expected_flat_constraint));
        assert!(output
            .structured_statements
            .contains(&StructuredStatement::Define { dst, expr }));
    }

    #[test]
    fn large_boolean_or_records_linear_sum_definition_metadata() {
        let mut cs = BasicAssembly::<F>::new();
        let booleans = [
            cs.add_named_boolean_variable("a"),
            cs.add_named_boolean_variable("b"),
            cs.add_named_boolean_variable("c"),
            cs.add_named_boolean_variable("d"),
            cs.add_named_boolean_variable("e"),
        ];
        let expected_sum_expr = booleans
            .iter()
            .fold(Expr::<F>::zero(), |acc, boolean| acc + Expr::from(*boolean));

        let result = Boolean::multi_or::<F, _>(&booleans, &mut cs);
        let (output, _) = cs.finalize();

        assert!(matches!(result, Boolean::Not(_)));
        assert!(output
            .structured_statements
            .iter()
            .any(|statement| matches!(
                statement,
                StructuredStatement::Define { expr, .. } if expr == &expected_sum_expr
            )));
    }

    #[test]
    fn boolean_negated_views_record_structured_definition_metadata() {
        let mut cs = BasicAssembly::<F>::new();
        let a = cs.add_named_boolean_variable("a");
        let b = cs.add_named_boolean_variable("b");

        let or_expr = Expr::<F>::from(1u32)
            - (Expr::from(1u32) - Expr::from(a.toggle()))
                * (Expr::from(1u32) - Expr::from(b.toggle()));
        let Boolean::Is(or_dst) = Boolean::or::<F, _>(&a.toggle(), &b.toggle(), &mut cs) else {
            panic!("non-constant boolean OR should produce a variable output");
        };

        let xor_left = Expr::<F>::from(a);
        let xor_right = Expr::<F>::from(b.toggle());
        let xor_expr =
            xor_left.clone() + xor_right.clone() - Expr::from(2u32) * (xor_left * xor_right);
        let Boolean::Is(xor_dst) = Boolean::xor::<F, _>(&a, &b.toggle(), &mut cs) else {
            panic!("non-constant boolean XOR should produce a variable output");
        };

        let nor_expr =
            (Expr::<F>::from(1u32) - Expr::from(a.toggle())) * (Expr::from(1u32) - Expr::from(b));
        let Boolean::Is(nor_dst) = Boolean::nor::<F, _>(&a.toggle(), &b, &mut cs) else {
            panic!("non-constant boolean NOR should produce a variable output");
        };

        let (output, _) = cs.finalize();

        for (dst, expr) in [
            (or_dst, or_expr.clone()),
            (xor_dst, xor_expr.clone()),
            (nor_dst, nor_expr.clone()),
        ] {
            let mut expected_flat_constraint = expr.to_max_quadratic_constraint();
            expected_flat_constraint -= Term::from(dst);
            expected_flat_constraint.normalize();

            assert!(output
                .constraints
                .iter()
                .any(|(constraint, _)| constraint == &expected_flat_constraint));
            assert!(output
                .structured_statements
                .contains(&StructuredStatement::Define { dst, expr }));
        }
    }

    #[test]
    fn compiled_artifact_preserves_structured_metadata() {
        let mut cs = BasicAssembly::<F>::new();
        cs.allocate_delegation_state(1);
        cs.request_register_and_indirect_memory_accesses(
            RegisterAccessRequest {
                register_index: 10,
                register_write: true,
                indirects_alignment_log2: 0,
                indirect_accesses: vec![],
            },
            "metadata smoke register access",
            2,
        );
        cs.request_register_and_indirect_memory_accesses(
            RegisterAccessRequest {
                register_index: 11,
                register_write: true,
                indirects_alignment_log2: 0,
                indirect_accesses: vec![],
            },
            "metadata smoke second register access",
            2,
        );
        cs.materialize_table::<1>(TableType::ZeroEntry);
        let lookup_zero = cs.add_named_variable("lookup zero");
        cs.add_constraint_allow_explicit_linear(Term::from(lookup_zero).into());
        cs.enforce_lookup_tuple_for_fixed_table(
            &[LookupInput::Variable(lookup_zero)],
            TableType::ZeroEntry,
            false,
        );

        let a = cs.add_named_variable("a");
        let b = cs.add_named_variable("b");
        let c = cs.add_named_variable("c");
        let expr = Expr::<F>::from(a) * (Expr::from(b) + Expr::from(c));
        let expected_structured_expr = Expr::Product(vec![
            Expr::Var(a),
            Expr::Sum(vec![Expr::Var(b), Expr::Var(c)]),
        ]);
        let mut expected_flat_constraint =
            Term::from(a) * Term::from(b) + Term::from(a) * Term::from(c);
        expected_flat_constraint.normalize();

        assert_eq!(expr, expected_structured_expr);
        cs.add_constraint_expr(expr.clone());

        let (output, _) = cs.finalize();
        assert!(output
            .constraints
            .iter()
            .any(|(constraint, _)| constraint == &expected_flat_constraint));

        let artifact = GKRCompiler::default().compile_delegation_circuit(
            output,
            TIMESTAMP_COLUMNS_NUM_BITS as usize,
            false,
        );

        assert_eq!(
            artifact.structured_statements,
            vec![StructuredStatement::AssertZero {
                expr: expected_structured_expr,
                prevent_optimizations: false,
            }]
        );
    }
}
