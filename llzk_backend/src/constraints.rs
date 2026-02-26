//! LLZK `@constrain` lowering.

use anyhow::anyhow;
use anyhow::Result;
use llzk::dialect::felt;
use llzk::prelude::*;
use prover::cs::constraint::Constraint;
use prover::cs::constraint::Term;
use prover::cs::cs::circuit::DisjunctiveLookup;
use prover::cs::cs::circuit::LookupQuery;
use prover::cs::cs::circuit::LookupQueryTableType;
use prover::cs::cs::circuit::PicusExpr;
use prover::cs::cs::circuit::PicusStructuredConstraint;
use prover::cs::cs::circuit::RangeCheckQuery;
use prover::cs::definitions::LookupInput;
use prover::cs::types::Boolean;

use crate::builder::*;
use crate::codegen::StructVars;
use crate::field::FieldInfo;
use crate::lookups::add_disjunctive_lookup_constraints;
use crate::lookups::add_dynamic_lookup_constraints;
use crate::lookups::add_lookup_constraints_for_table;

/// Trait implemented by types that can emit LLZK IR within a struct `@constrain` function.
pub(crate) trait EmitLlzkInConstrain<'ctx: 'sco, 'sco, F: FieldInfo> {
    type Output;

    fn emit_constrain(
        &self,
        builder: &OpsBuilder<'ctx, 'sco, F>,
        vars: &StructVars<F>,
    ) -> Result<Self::Output>;
}

impl<'ctx: 'sco, 'sco, F: FieldInfo, T: EmitLlzkInConstrain<'ctx, 'sco, F, Output = ()>>
    EmitLlzkInConstrain<'ctx, 'sco, F> for Vec<T>
{
    type Output = ();

    fn emit_constrain(
        &self,
        builder: &OpsBuilder<'ctx, 'sco, F>,
        vars: &StructVars<F>,
    ) -> Result<Self::Output> {
        self.iter()
            .try_for_each(|t| t.emit_constrain(builder, vars))
    }
}

/// Extension trait for [`StructDefOpLike`] that adds a method for filling the `@constrain`
/// function.
pub(crate) trait AddConstraints<'ctx: 'op, 'op, F: FieldInfo>:
    StructDefOpLike<'ctx, 'op>
{
    /// Invokes the callback scoped in `@constrain`.
    ///
    /// All ops added with the [`OpsBuilder`] are automatically added to that function.
    fn add_constraints(
        &'op self,
        env: &'ctx ModuleEnv<'ctx, F>,
        f: impl FnOnce(&mut OpsBuilder<'ctx, 'op, F>) -> anyhow::Result<()>,
    ) -> anyhow::Result<()> {
        let constrain_fn = self.get_constrain_func().ok_or_else(|| {
            anyhow!(
                "struct {} is missing its @constrain function",
                StructDefOpLike::name(self)
            )
        })?;
        let mut ops_builder = OpsBuilder::new(env, constrain_fn);
        f(&mut ops_builder)
    }
}

impl<'ctx: 'op, 'op, F: FieldInfo, T: StructDefOpMutLike<'ctx, 'op>> AddConstraints<'ctx, 'op, F>
    for T
{
}

impl<'ctx: 'sco, 'sco, F: FieldInfo> EmitLlzkInConstrain<'ctx, 'sco, F> for RangeCheckQuery<F> {
    type Output = ();

    fn emit_constrain(
        &self,
        builder: &OpsBuilder<'ctx, 'sco, F>,
        vars: &StructVars<F>,
    ) -> Result<Self::Output> {
        match &self.input {
            LookupInput::Variable(variable) => {
                let val = vars.get_constrain_val(builder, variable)?;
                builder.append_range_constraint(val, self.width)?;
            }
            LookupInput::Expression { .. } => {
                panic!("range checks over lookup expressions are not yet supported")
            }
        }
        Ok(())
    }
}

impl<'ctx: 'sco, 'sco, F: FieldInfo> EmitLlzkInConstrain<'ctx, 'sco, F> for (Constraint<F>, bool) {
    type Output = ();

    fn emit_constrain(
        &self,
        builder: &OpsBuilder<'ctx, 'sco, F>,
        vars: &StructVars<F>,
    ) -> Result<Self::Output> {
        let (constraint, _prevent_optimization) = self;

        let zero = builder.get_constant_from_start(builder.felt_type(), 0)?;
        let values = constraint
            .terms
            .iter()
            .enumerate()
            .map(|(term_idx, term)| {
                builder.with_column_offset(term_idx, || term.emit_constrain(builder, vars))
            })
            .collect::<Result<Vec<Value<'_, '_>>>>()?;
        let sum = builder.append_sum_here(&values)?;
        builder.append_constrain_eq_here(sum, zero)
    }
}

impl<'ctx: 'sco, 'sco, F: FieldInfo> EmitLlzkInConstrain<'ctx, 'sco, F> for Term<F> {
    type Output = Value<'ctx, 'sco>;

    fn emit_constrain(
        &self,
        builder: &OpsBuilder<'ctx, 'sco, F>,
        vars: &StructVars<F>,
    ) -> Result<Self::Output> {
        match self {
            Term::Constant(c) => {
                let coeff = c.as_u64_reduced();
                let coeff_opp = F::CHARACTERISTICS - coeff;
                Ok(if coeff < coeff_opp {
                    builder.get_constant_from_start(builder.felt_type(), coeff)?
                } else {
                    let coeff_opp_val =
                        builder.get_constant_from_start(builder.felt_type(), coeff_opp)?;
                    builder.append_op_with_result(felt::neg(
                        builder.current_location(),
                        coeff_opp_val,
                    )?)?
                })
            }
            Term::Expression {
                coeff,
                inner,
                degree,
            } => {
                let coeff = coeff.as_u64_reduced();

                let coeff_opp = F::CHARACTERISTICS - coeff;
                let mut monomial = builder.get_constant_from_start(builder.felt_type(), 1)?;
                for var in inner.iter().take(*degree) {
                    let var_val = vars.get_constrain_val(builder, var)?;
                    let mul = felt::mul(builder.current_location(), monomial, var_val)?;
                    monomial = builder.append_op_with_result(mul)?;
                }

                Ok(if coeff < coeff_opp {
                    if coeff == 1 {
                        monomial
                    } else {
                        let coeff_val =
                            builder.get_constant_from_start(builder.felt_type(), coeff)?;
                        let mul = felt::mul(builder.current_location(), coeff_val, monomial)?;
                        builder.append_op_with_result(mul)?
                    }
                } else if coeff_opp == 1 {
                    builder
                        .append_op_with_result(felt::neg(builder.current_location(), monomial)?)?
                } else {
                    let coeff_opp_val =
                        builder.get_constant_from_start(builder.felt_type(), coeff_opp)?;
                    let mul = builder.append_op_with_result(felt::mul(
                        builder.current_location(),
                        coeff_opp_val,
                        monomial,
                    )?)?;
                    builder.append_op_with_result(felt::neg(builder.current_location(), mul)?)?
                })
            }
        }
    }
}

impl<'ctx: 'sco, 'sco, F: FieldInfo> EmitLlzkInConstrain<'ctx, 'sco, F> for LookupInput<F> {
    type Output = Value<'ctx, 'sco>;

    fn emit_constrain(
        &self,
        builder: &OpsBuilder<'ctx, 'sco, F>,
        vars: &StructVars<F>,
    ) -> Result<Self::Output> {
        match self {
            LookupInput::Variable(var) => vars.get_constrain_val(builder, var),
            LookupInput::Expression {
                linear_terms,
                constant_coeff,
            } => {
                let init = builder.get_constant_from_start(
                    builder.felt_type(),
                    constant_coeff.as_u64_reduced(),
                )?;
                linear_terms
                    .iter()
                    .enumerate()
                    .map(|(term_idx, (coeff, var))| {
                        builder.with_column_offset(term_idx, || {
                            let coeff_val = builder.get_constant_from_start(
                                builder.felt_type(),
                                coeff.as_u64_reduced(),
                            )?;
                            builder.append_op_with_result(felt::mul(
                                builder.current_location(),
                                coeff_val,
                                vars.get_constrain_val(builder, var)?,
                            )?)
                        })
                    })
                    .try_fold(init, |sum, term_val| {
                        builder.append_op_with_result(felt::add(
                            builder.current_location(),
                            sum,
                            term_val?,
                        )?)
                    })
            }
        }
    }
}

impl<'ctx: 'sco, 'sco, F: FieldInfo> EmitLlzkInConstrain<'ctx, 'sco, F> for PicusExpr<F> {
    type Output = Value<'ctx, 'sco>;

    fn emit_constrain(
        &self,
        builder: &OpsBuilder<'ctx, 'sco, F>,
        vars: &StructVars<F>,
    ) -> Result<Self::Output> {
        match self {
            PicusExpr::Variable(variable) => vars.get_constrain_val(builder, variable),
            PicusExpr::Constant(constant) => {
                builder.get_constant_from_start(builder.felt_type(), constant.as_u64_reduced())
            }
            PicusExpr::Add(lhs, rhs) => {
                let lhs = lhs.emit_constrain(builder, vars)?;
                let rhs = rhs.emit_constrain(builder, vars)?;
                builder.append_op_with_result(felt::add(builder.current_location(), lhs, rhs)?)
            }
            PicusExpr::Sub(lhs, rhs) => {
                let lhs = lhs.emit_constrain(builder, vars)?;
                let rhs = rhs.emit_constrain(builder, vars)?;
                builder.append_op_with_result(felt::sub(builder.current_location(), lhs, rhs)?)
            }
            PicusExpr::Mul(lhs, rhs) => {
                let lhs = lhs.emit_constrain(builder, vars)?;
                let rhs = rhs.emit_constrain(builder, vars)?;
                builder.append_op_with_result(felt::mul(builder.current_location(), lhs, rhs)?)
            }
        }
    }
}

impl<'ctx: 'sco, 'sco, F: FieldInfo> EmitLlzkInConstrain<'ctx, 'sco, F>
    for PicusStructuredConstraint<F>
{
    type Output = ();

    fn emit_constrain(
        &self,
        builder: &OpsBuilder<'ctx, 'sco, F>,
        vars: &StructVars<F>,
    ) -> Result<Self::Output> {
        match self {
            PicusStructuredConstraint::Eq { lhs, rhs } => {
                let lhs = lhs.emit_constrain(builder, vars)?;
                let rhs = rhs.emit_constrain(builder, vars)?;
                builder.append_constrain_eq_here(lhs, rhs)
            }
        }
    }
}

impl<'ctx: 'sco, 'sco, F: FieldInfo> EmitLlzkInConstrain<'ctx, 'sco, F> for LookupQuery<F> {
    type Output = ();

    fn emit_constrain(
        &self,
        builder: &OpsBuilder<'ctx, 'sco, F>,
        vars: &StructVars<F>,
    ) -> Result<Self::Output> {
        match self.table {
            LookupQueryTableType::Variable(variable) => {
                add_dynamic_lookup_constraints(builder, vars, self, variable, None, None)
            }
            LookupQueryTableType::Constant(table_type) => {
                add_lookup_constraints_for_table(builder, vars, self, table_type, None, None)
            }
        }
    }
}

impl<'ctx: 'sco, 'sco, F: FieldInfo> EmitLlzkInConstrain<'ctx, 'sco, F> for DisjunctiveLookup<F> {
    type Output = ();

    fn emit_constrain(
        &self,
        builder: &OpsBuilder<'ctx, 'sco, F>,
        vars: &StructVars<F>,
    ) -> Result<Self::Output> {
        add_disjunctive_lookup_constraints(builder, vars, self)
    }
}

impl<'ctx: 'sco, 'sco, F: FieldInfo> EmitLlzkInConstrain<'ctx, 'sco, F> for Boolean {
    type Output = Value<'ctx, 'sco>;

    fn emit_constrain(
        &self,
        builder: &OpsBuilder<'ctx, 'sco, F>,
        vars: &StructVars<F>,
    ) -> Result<Self::Output> {
        match self {
            Boolean::Is(variable) => vars.get_constrain_val(builder, variable),
            Boolean::Not(variable) => builder.append_op_with_result(felt::sub(
                builder.current_location(),
                builder.get_felt_constant_from_start(1)?,
                vars.get_constrain_val(builder, variable)?,
            )?),
            Boolean::Constant(c) => builder.get_felt_constant_from_start(*c as u64),
        }
    }
}

#[cfg(test)]
mod tests {
    use prover::cs::definitions::Variable;
    use prover::field::Mersenne31Field;
    use prover::field::PrimeField;

    use super::*;
    use crate::builder::OpsBuilder;
    use crate::builder::SemanticLocation;
    use crate::codegen::StructVars;
    use crate::test_helpers::assert_full_ir_eq;
    use crate::test_helpers::emit_test_constrain_ir;
    use crate::test_helpers::emit_test_constrain_ir_with_debug_info;

    /// Convert `value` to a field element in [`Mersenne31Field`].
    fn field(value: u64) -> Mersenne31Field {
        Mersenne31Field::from_u64_unchecked(value)
    }

    /// Emit a synthetic `@constrain` body with `num_inputs` felt inputs and `num_members` felt
    /// members, then compare the resulting IR against an exact fixture.
    ///
    /// The generated member names are deterministic and follow the pattern `member_<idx>`. The
    /// `emit` closure receives the synthetic input and member variables as slices so each test can
    /// assert the expected layout explicitly before building the expression under test.
    fn assert_constrain_fixture(
        num_inputs: usize,
        num_members: usize,
        expected: &str,
        emit: impl FnOnce(
            &OpsBuilder<'_, '_, Mersenne31Field>,
            &StructVars<Mersenne31Field>,
            &[Variable],
            &[Variable],
        ) -> Result<()>,
    ) {
        let inputs = (0..num_inputs)
            .map(|offset| Variable(u64::try_from(offset).expect("input count overflowed u64")))
            .collect::<Vec<_>>();
        let members = (0..num_members)
            .map(|offset| {
                Variable(u64::try_from(num_inputs + offset).expect("member count overflowed u64"))
            })
            .collect::<Vec<_>>();
        let member_names = members
            .iter()
            .enumerate()
            .map(|(idx, member)| (*member, format!("member_{idx}")))
            .collect::<Vec<_>>();
        let member_refs = member_names
            .iter()
            .map(|(member, name)| (*member, name.as_str()))
            .collect::<Vec<_>>();

        let ir = emit_test_constrain_ir("constraint_test", &inputs, &member_refs, |ops, vars| {
            emit(ops, vars, &inputs, &members)
        });
        assert_full_ir_eq(&ir, expected);
    }

    #[test]
    fn boolean_not_on_input_emits_sub_from_one() {
        assert_constrain_fixture(
            1,
            0,
            include_str!("../testdata/constraints/boolean_not_on_input_emits_sub_from_one.mlir"),
            |ops, vars, inputs, members| {
                assert_eq!(inputs.len(), 1);
                assert!(members.is_empty());
                let _ = Boolean::Not(inputs[0]).emit_constrain(ops, vars)?;
                Ok(())
            },
        );
    }

    #[test]
    fn term_with_negative_unit_coefficient_emits_neg() {
        let neg_one = field(Mersenne31Field::CHARACTERISTICS - 1);
        assert_constrain_fixture(
            1,
            0,
            include_str!(
                "../testdata/constraints/term_with_negative_unit_coefficient_emits_neg.mlir"
            ),
            |ops, vars, inputs, members| {
                assert_eq!(inputs.len(), 1);
                assert!(members.is_empty());
                let term = Term::from((neg_one, inputs[0]));
                let _ = term.emit_constrain(ops, vars)?;
                Ok(())
            },
        );
    }

    #[test]
    fn negative_constant_term_emits_negated_small_constant() {
        let neg_one = field(Mersenne31Field::CHARACTERISTICS - 1);
        assert_constrain_fixture(
            0,
            0,
            include_str!(
                "../testdata/constraints/negative_constant_term_emits_negated_small_constant.mlir"
            ),
            |ops, vars, inputs, members| {
                assert!(inputs.is_empty());
                assert!(members.is_empty());
                let term = Term::Constant(neg_one);
                let _ = term.emit_constrain(ops, vars)?;
                Ok(())
            },
        );
    }

    #[test]
    fn lookup_expression_emits_mul_and_add_chain() {
        assert_constrain_fixture(
            2,
            0,
            include_str!("../testdata/constraints/lookup_expression_emits_mul_and_add_chain.mlir"),
            |ops, vars, inputs, members| {
                assert_eq!(inputs.len(), 2);
                assert!(members.is_empty());
                let input = LookupInput::Expression {
                    linear_terms: vec![(field(3), inputs[0]), (field(4), inputs[1])],
                    constant_coeff: field(5),
                };
                let _ = input.emit_constrain(ops, vars)?;
                Ok(())
            },
        );
    }

    #[test]
    fn constrain_access_reads_member_when_variable_is_not_input() {
        assert_constrain_fixture(
            0,
            1,
            include_str!(
                "../testdata/constraints/constrain_access_reads_member_when_variable_is_not_input.mlir"
            ),
            |ops, vars, inputs, members| {
                assert!(inputs.is_empty());
                assert_eq!(members.len(), 1);
                let _ = Boolean::Is(members[0]).emit_constrain(ops, vars)?;
                Ok(())
            },
        );
    }

    #[test]
    fn range_check_query_emits_compare_and_constraint() {
        assert_constrain_fixture(
            1,
            0,
            include_str!(
                "../testdata/constraints/range_check_query_emits_compare_and_constraint.mlir"
            ),
            |ops, vars, inputs, members| {
                assert_eq!(inputs.len(), 1);
                assert!(members.is_empty());
                let query = RangeCheckQuery::new(inputs[0], 8);
                query.emit_constrain(ops, vars)
            },
        );
    }

    #[test]
    fn constrain_debug_locations_use_semantic_virtual_paths() {
        let inputs = [Variable(0)];
        let ir = emit_test_constrain_ir_with_debug_info(
            "constraint_debug_locations",
            &inputs,
            &[],
            |ops, vars| {
                ops.with_semantic_location(SemanticLocation::constrain_constraint(1), || {
                    let constraint = Constraint {
                        terms: vec![Term::from((field(1), inputs[0])), Term::Constant(field(7))],
                    };
                    (constraint, false).emit_constrain(ops, vars)
                })
            },
        );

        assert!(ir.contains("llzk://constrain/constraints\":1:0"));
        assert!(ir.contains("llzk://constrain/constraints\":1:1"));
    }
}
