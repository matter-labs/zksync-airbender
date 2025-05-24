mod boolean;
mod field;
mod integer;

use core::hash::Hash;
use std::assert_matches::assert_matches;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::HashMap;

use super::*;
use crate::definitions::Variable;
use ::field::PrimeField;

pub use self::boolean::*;
pub use self::field::*;
pub use self::integer::*;

use super::WitnessPlacer;

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum Expression<F: PrimeField> {
    Bool(BoolNodeExpression<F>),
    Field(FieldNodeExpression<F>),
    U8(FixedWidthIntegerNodeExpression<F>),
    U16(FixedWidthIntegerNodeExpression<F>),
    U32(FixedWidthIntegerNodeExpression<F>),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum RawExpression<F: PrimeField> {
    Bool(BoolNodeExpression<F>),
    Field(FieldNodeExpression<F>),
    Integer(FixedWidthIntegerNodeExpression<F>),
    PerformLookup {
        input_subexpr_idxes: Box<[usize]>, // subexpressions
        table_id_subexpr_idx: usize,
        num_outputs: usize,
        lookup_mapping_idx: usize,
    },
    MaybePerformLookup {
        input_subexpr_idxes: Box<[usize]>, // subexpressions
        table_id_subexpr_idx: usize,
        mask_id_subexpr_idx: usize,
        num_outputs: usize,
    },
    AccessLookup {
        subindex: usize,
        output_index: usize,
    },
    WriteVariable {
        into_variable: Variable,
        source_subexpr: Expression<F>, // it'll be only subexpression, but we need type
        condition_subexpr_idx: Option<usize>,
    },
}

impl<F: PrimeField> Expression<F> {
    pub fn report_origins(
        &self,
        dst: &mut BTreeSet<Variable>,
        oracles: &mut BTreeSet<(Placeholder, usize)>,
        lookup_fn: &impl Fn(usize, usize) -> Vec<Expression<F>>,
    ) {
        match self {
            Self::Bool(inner) => {
                inner.report_origins(dst, oracles, lookup_fn);
            }
            Self::Field(inner) => {
                inner.report_origins(dst, oracles, lookup_fn);
            }
            Self::U8(inner) => {
                inner.report_origins(dst, oracles, lookup_fn);
            }
            Self::U16(inner) => {
                inner.report_origins(dst, oracles, lookup_fn);
            }
            _ => {
                unreachable!()
            }
        }
    }

    pub fn make_subexpressions(
        &mut self,
        set: &mut SubexpressionsMapper<F>,
        lookup_fn: &impl Fn(usize, usize) -> Vec<Expression<F>>,
    ) {
        match self {
            Self::Bool(inner) => {
                inner.make_subexpressions(set, lookup_fn);
            }
            Self::Field(inner) => {
                inner.make_subexpressions(set, lookup_fn);
            }
            Self::U8(inner) => {
                inner.make_subexpressions(set, lookup_fn);
            }
            Self::U16(inner) => {
                inner.make_subexpressions(set, lookup_fn);
            }
            _ => {
                unreachable!()
            }
        }
    }

    pub fn get_subexpr_index(&self) -> Option<usize> {
        match self {
            Self::Bool(inner) => {
                let BoolNodeExpression::SubExpression(idx) = inner else {
                    return None;
                };

                Some(*idx)
            }
            Self::Field(inner) => {
                let FieldNodeExpression::SubExpression(idx) = inner else {
                    return None;
                };

                Some(*idx)
            }
            Self::U8(inner) => {
                let FixedWidthIntegerNodeExpression::U8SubExpression(idx) = inner else {
                    return None;
                };

                Some(*idx)
            }
            Self::U16(inner) => {
                let FixedWidthIntegerNodeExpression::U16SubExpression(idx) = inner else {
                    return None;
                };

                Some(*idx)
            }
            _ => {
                unreachable!()
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum AssignedExpression<F: PrimeField> {
    Unconditional(Expression<F>),
    Conditional {
        temporary_assignments: Vec<(BoolNodeExpression<F>, Expression<F>)>,
        final_assignment: Option<Expression<F>>,
    },
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub enum SingleAssignment<F: PrimeField> {
    Unconditional(Expression<F>),
    Conditional {
        condition: BoolNodeExpression<F>,
        value: Expression<F>,
    },
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct ResolverDetails<F: PrimeField> {
    pub inputs: BTreeMap<Variable, Expression<F>>,
    pub lookup_inputs: BTreeMap<
        usize,
        (
            Box<[FieldNodeExpression<F>]>,
            FixedWidthIntegerNodeExpression<F>,
            usize,
        ),
    >,
    pub maybe_lookup_inputs: BTreeMap<
        usize,
        (
            Box<[FieldNodeExpression<F>]>,
            FixedWidthIntegerNodeExpression<F>,
            BoolNodeExpression<F>,
            usize,
        ),
    >,
    pub oracles: Vec<Expression<F>>,
    pub quasi_outputs_for_lookup_enforcements: Vec<usize>, // index into self.lookups
    pub outputs: BTreeMap<Variable, SingleAssignment<F>>,
}

impl<F: PrimeField> ResolverDetails<F> {
    pub fn new() -> Self {
        Self {
            inputs: BTreeMap::new(),
            oracles: Vec::new(),
            lookup_inputs: BTreeMap::new(),
            maybe_lookup_inputs: BTreeMap::new(),
            outputs: BTreeMap::new(),
            quasi_outputs_for_lookup_enforcements: Vec::new(),
        }
    }
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct WitnessGraphCreator<F: PrimeField> {
    pub values: Vec<Option<AssignedExpression<F>>>,
    // a sequence of lookup expressions that are unconditional (would be used for multiplicity counting)
    pub lookups: Vec<(
        Box<[FieldNodeExpression<F>]>,
        FixedWidthIntegerNodeExpression<F>,
        usize,
    )>,
    // a sequence of the lookups that are conditional and will be used to only assign values
    pub maybe_lookups: Vec<(
        Box<[FieldNodeExpression<F>]>,
        FixedWidthIntegerNodeExpression<F>,
        BoolNodeExpression<F>,
        usize,
    )>,
    current_stats_resolver: Option<ResolverDetails<F>>,
    pub resolvers_data: Vec<ResolverDetails<F>>,
    _marker: core::marker::PhantomData<F>,
}

pub struct SubexpressionsMapper<F: PrimeField> {
    ssa_expr_set: HashMap<RawExpression<F>, usize>,
    ssa_form: Vec<RawExpression<F>>,
    known_lookups: BTreeMap<
        usize,
        (
            Box<[FieldNodeExpression<F>]>,
            FixedWidthIntegerNodeExpression<F>,
            usize,
        ),
    >,
    known_maybe_lookups: BTreeMap<
        usize,
        (
            Box<[FieldNodeExpression<F>]>,
            FixedWidthIntegerNodeExpression<F>,
            BoolNodeExpression<F>,
            usize,
        ),
    >,
}

impl<F: PrimeField> SubexpressionsMapper<F> {
    fn new() -> Self {
        Self {
            ssa_expr_set: HashMap::new(),
            ssa_form: Vec::new(),
            known_lookups: BTreeMap::new(),
            known_maybe_lookups: BTreeMap::new(),
        }
    }

    pub(crate) fn enforce_lookup_relation_inner(
        &mut self,
        lookup_idx: usize,
        lookup_inputs: &mut [FieldNodeExpression<F>],
        table_id: &mut FixedWidthIntegerNodeExpression<F>,
        num_outputs: usize,
    ) -> usize {
        // make subexpressions
        let mut input_subexpr_idxes = vec![];
        for input in lookup_inputs.iter_mut() {
            input.make_subexpressions(self, &|_, _| vec![]);
            let FieldNodeExpression::SubExpression(idx) = input else {
                unreachable!()
            };
            input_subexpr_idxes.push(*idx);
        }
        table_id.make_subexpressions(self, &|_, _| vec![]);
        let FixedWidthIntegerNodeExpression::U16SubExpression(idx) = table_id else {
            unreachable!()
        };
        let table_id_subexpr_idx = *idx;
        // now add expression for lookup

        let t = RawExpression::PerformLookup {
            input_subexpr_idxes: input_subexpr_idxes.into_boxed_slice(),
            table_id_subexpr_idx,
            num_outputs: num_outputs,
            lookup_mapping_idx: lookup_idx,
        };
        let subexpr_idx = if self.ssa_expr_set.contains_key(&t) == false {
            let subexpr_idx = self.ssa_form.len();
            self.ssa_form.push(t.clone());
            self.ssa_expr_set.insert(t, subexpr_idx);

            subexpr_idx
        } else {
            let subexpr_idx = *self.ssa_expr_set.get(&t).unwrap();

            subexpr_idx
        };

        subexpr_idx
    }

    pub(crate) fn add_field_subexprs(&mut self, el: &mut FieldNodeExpression<F>) {
        if let FieldNodeExpression::LookupOutput {
            lookup_idx,
            output_idx,
        } = el.clone()
        {
            // we should somehow describe a lookup expression
            let (mut lookup_inputs, mut table_id, num_outputs) =
                self.known_lookups.get(&lookup_idx).unwrap().clone();

            // println!("Add unconditional lookup index {} with inputs {:?}, table ID = {:?} and {} outputs", lookup_idx, &lookup_inputs, &table_id, num_outputs);

            let subexpr_idx = self.enforce_lookup_relation_inner(
                lookup_idx,
                &mut *lookup_inputs,
                &mut table_id,
                num_outputs,
            );

            let t = RawExpression::AccessLookup {
                subindex: subexpr_idx,
                output_index: output_idx,
            };
            if self.ssa_expr_set.contains_key(&t) == false {
                let idx = self.ssa_form.len();
                self.ssa_form.push(t.clone());
                self.ssa_expr_set.insert(t, idx);
                *el = FieldNodeExpression::SubExpression(idx);
            } else {
                let idx = *self.ssa_expr_set.get(&t).unwrap();
                *el = FieldNodeExpression::SubExpression(idx);
            };

            return;
        }

        // and conditional lookup
        if let FieldNodeExpression::MaybeLookupOutput {
            lookup_idx,
            output_idx,
        } = el.clone()
        {
            // we should somehow describe a lookup expression
            let (mut lookup_inputs, mut table_id, mut condition, num_outputs) =
                self.known_maybe_lookups.get(&lookup_idx).unwrap().clone();
            // make subexpressions
            let mut input_subexpr_idxes = vec![];
            for input in lookup_inputs.iter_mut() {
                input.make_subexpressions(self, &|_, _| vec![]);
                let FieldNodeExpression::SubExpression(idx) = input else {
                    unreachable!()
                };
                input_subexpr_idxes.push(*idx);
            }
            table_id.make_subexpressions(self, &|_, _| vec![]);
            let FixedWidthIntegerNodeExpression::U16SubExpression(idx) = table_id else {
                unreachable!()
            };
            let table_id_subexpr_idx = idx;
            // now add expression for lookup
            condition.make_subexpressions(self, &|_, _| vec![]);
            let BoolNodeExpression::SubExpression(idx) = condition else {
                unreachable!()
            };
            let condition_subexpr_idx = idx;

            let t = RawExpression::MaybePerformLookup {
                input_subexpr_idxes: input_subexpr_idxes.into_boxed_slice(),
                table_id_subexpr_idx,
                mask_id_subexpr_idx: condition_subexpr_idx,
                num_outputs,
            };
            let subexpr_idx = if self.ssa_expr_set.contains_key(&t) == false {
                let subexpr_idx = self.ssa_form.len();
                self.ssa_form.push(t.clone());
                self.ssa_expr_set.insert(t, subexpr_idx);

                subexpr_idx
            } else {
                let subexpr_idx = *self.ssa_expr_set.get(&t).unwrap();

                subexpr_idx
            };

            let t = RawExpression::AccessLookup {
                subindex: subexpr_idx,
                output_index: output_idx,
            };
            if self.ssa_expr_set.contains_key(&t) == false {
                let idx = self.ssa_form.len();
                self.ssa_form.push(t.clone());
                self.ssa_expr_set.insert(t, idx);
                *el = FieldNodeExpression::SubExpression(idx);
            } else {
                let idx = *self.ssa_expr_set.get(&t).unwrap();
                *el = FieldNodeExpression::SubExpression(idx);
            };

            return;
        }

        if matches!(el, FieldNodeExpression::SubExpression(..)) {
            return;
        }
        let t = RawExpression::Field(el.clone());
        if self.ssa_expr_set.contains_key(&t) == false {
            let idx = self.ssa_form.len();
            self.ssa_form.push(t.clone());
            self.ssa_expr_set.insert(t, idx);
            *el = FieldNodeExpression::SubExpression(idx);
        } else {
            // it is present and we just need to match
            let idx = *self.ssa_expr_set.get(&t).unwrap();
            *el = FieldNodeExpression::SubExpression(idx);
        }
    }

    pub(crate) fn add_boolean_subexprs(&mut self, el: &mut BoolNodeExpression<F>) {
        if matches!(el, BoolNodeExpression::SubExpression(..)) {
            return;
        }
        let t = RawExpression::Bool(el.clone());
        if self.ssa_expr_set.contains_key(&t) == false {
            let idx = self.ssa_form.len();
            self.ssa_form.push(t.clone());
            self.ssa_expr_set.insert(t, idx);
            *el = BoolNodeExpression::SubExpression(idx);
        } else {
            // it is present and we just need to match
            let idx = *self.ssa_expr_set.get(&t).unwrap();
            *el = BoolNodeExpression::SubExpression(idx);
        }
    }

    pub(crate) fn add_integer_subexprs(&mut self, el: &mut FixedWidthIntegerNodeExpression<F>) {
        if matches!(el, FixedWidthIntegerNodeExpression::U8SubExpression(..))
            || matches!(el, FixedWidthIntegerNodeExpression::U16SubExpression(..))
            || matches!(el, FixedWidthIntegerNodeExpression::U32SubExpression(..))
        {
            return;
        }
        let original_width = el.bit_width();
        let t = RawExpression::Integer(el.clone());
        if self.ssa_expr_set.contains_key(&t) == false {
            let idx = self.ssa_form.len();
            self.ssa_form.push(t.clone());
            self.ssa_expr_set.insert(t, idx);
            match original_width {
                8 => {
                    *el = FixedWidthIntegerNodeExpression::U8SubExpression(idx);
                }
                16 => {
                    *el = FixedWidthIntegerNodeExpression::U16SubExpression(idx);
                }
                32 => {
                    *el = FixedWidthIntegerNodeExpression::U32SubExpression(idx);
                }
                _ => {
                    unreachable!()
                }
            }
        } else {
            // it is present and we just need to match
            let idx = *self.ssa_expr_set.get(&t).unwrap();
            match original_width {
                8 => {
                    *el = FixedWidthIntegerNodeExpression::U8SubExpression(idx);
                }
                16 => {
                    *el = FixedWidthIntegerNodeExpression::U16SubExpression(idx);
                }
                32 => {
                    *el = FixedWidthIntegerNodeExpression::U32SubExpression(idx);
                }
                _ => {
                    unreachable!()
                }
            }
        }
    }
}

impl<F: PrimeField> WitnessGraphCreator<F> {
    pub fn new() -> Self {
        Self {
            values: Vec::new(),
            lookups: Vec::new(),
            maybe_lookups: Vec::new(),
            current_stats_resolver: None,
            resolvers_data: Vec::new(),
            _marker: core::marker::PhantomData,
        }
    }

    fn resize_to_assign(&mut self, variable: Variable) -> usize {
        if variable.is_placeholder() {
            panic!("variable is placeholder");
        }
        let idx = variable.0 as usize;
        if idx >= self.values.len() {
            self.values.resize(idx + 1, None);
        }

        idx
    }

    pub fn compute_resolution_order(
        &self,
    ) -> (
        BTreeMap<usize, ResolverDetails<F>>,
        Vec<Vec<RawExpression<F>>>,
    ) {
        let mut unconditionally_resolved_variables = BTreeSet::new();
        let mut conditionally_resolved_variables = BTreeMap::new();
        let mut conditional_with_unconditional_overwrites = BTreeSet::new();

        for (idx, el) in self.values.iter().enumerate() {
            let variable = Variable(idx as u64);
            let Some(el) = el else {
                panic!("unassigned value for variable {:?}", variable);
            };

            match el {
                AssignedExpression::Unconditional(_expr) => {
                    // easy
                    unconditionally_resolved_variables.insert(variable);
                }
                AssignedExpression::Conditional {
                    temporary_assignments,
                    final_assignment,
                } => {
                    if let Some(_final_assignment) = final_assignment {
                        unconditionally_resolved_variables.insert(variable);
                        conditional_with_unconditional_overwrites.insert(variable);
                    } else {
                        assert!(unconditionally_resolved_variables.contains(&variable) == false);
                        assert!(
                            conditional_with_unconditional_overwrites.contains(&variable) == false
                        );

                        let entry = conditionally_resolved_variables
                            .entry(variable)
                            .or_insert(vec![]);
                        // well, it's some other invariant that we want from this variable, and we have to consider all origins
                        for (mask, value) in temporary_assignments.iter() {
                            entry.push((mask.clone(), value.clone()));
                        }
                    }
                }
            }
        }

        let total_vars =
            unconditionally_resolved_variables.len() + conditionally_resolved_variables.len();
        assert!(
            unconditionally_resolved_variables.is_disjoint(&BTreeSet::from_iter(
                conditionally_resolved_variables.keys().copied()
            ))
        );

        let mut unresolved_variables = BTreeSet::new();
        let mut resolved_variables = BTreeSet::new();
        for idx in 0..total_vars {
            unresolved_variables.insert(Variable(idx as u64));
        }

        let mut resolution_sequence = BTreeMap::new();
        let mut idxes_to_skip = BTreeSet::new();

        loop {
            if unresolved_variables.is_empty() {
                break;
            }

            let initial_num_resolved = resolved_variables.len();
            let initial_len = resolution_sequence.len();
            let initial_skipped = idxes_to_skip.len();
            let initial_conditional_resolved: usize = conditionally_resolved_variables
                .iter()
                .map(|el| el.1.len())
                .sum();

            for (resolver_idx, details) in self.resolvers_data.iter().enumerate() {
                if idxes_to_skip.contains(&resolver_idx) {
                    continue;
                }

                let has_outputs = details.outputs.len() > 0;

                // check if all outputs will be eventually overwritten
                let can_skip_due_to_overwrite = details
                    .outputs
                    .iter()
                    .all(|(var, _)| conditional_with_unconditional_overwrites.contains(var));

                if has_outputs && can_skip_due_to_overwrite {
                    let mut skip_as_only_temporary_assignments = true;
                    for (_variable, expr) in details.outputs.iter() {
                        // quick check if this resolver can be skipped completely as it only assignments
                        // into variables, that are unconditionally overwritten at some point
                        match expr {
                            SingleAssignment::Unconditional(..) => {
                                // println!("Found unconditional assignment for variable {:?}", variable);

                                // it's meaningful, so we will continue below
                                skip_as_only_temporary_assignments = false;
                            }
                            SingleAssignment::Conditional { .. } => {
                                // we can skip this resolver at all
                                // println!("Skip conditional assignment for variable {:?}", variable);
                            }
                        }
                    }

                    if skip_as_only_temporary_assignments {
                        // println!("Resolver {} will be skipped in the future from considerations as it only does temporary assignments", resolver_idx);
                        idxes_to_skip.insert(resolver_idx);
                        continue;
                    }
                }

                // there can be multiple resolvers potentially writing into the same variable,
                // so we should check that either
                // - there are multiple conditional assignments and no unconditional
                // - there are multiple conditional assignments and then unconditional, and in this case
                // we should give preference to the last one

                let mut can_resolve = true;
                for (variable, _) in details.inputs.iter() {
                    if resolved_variables.contains(variable) {
                        continue;
                    } else {
                        // we didn't mark it fully resolved yet
                        if unconditionally_resolved_variables.contains(variable) {
                            // println!("Resolver {} depend on unconditional variable {:?}", resolver_idx, variable);
                            can_resolve = false;
                            // break;
                        } else {
                            // variable is conditionally assignable, so we will try to consider that
                            // we want all resolvers to write to it before allowing any further progress
                            if conditionally_resolved_variables.contains_key(variable) {
                                // println!("Resolver {} depend on conditional variable {:?}", resolver_idx, variable);
                                can_resolve = false;
                                // break;
                            }
                        }
                    }
                }

                if can_resolve == false {
                    // try next resolver
                    continue;
                }

                for (variable, expr) in details.outputs.iter() {
                    // There can be some re-assignments, but all those should be conditional only at worst
                    assert!(
                        unresolved_variables.contains(variable),
                        "Variable {:?} should not be considered resolved yet",
                        variable
                    );

                    // println!("Will resolve variable {:?}", variable);

                    if unconditionally_resolved_variables.contains(variable) {
                        // easy case - immediately fully resolved
                        // println!("Variable {:?} is now fully resolved", variable);

                        unresolved_variables.remove(variable);
                        resolved_variables.insert(*variable);
                    } else {
                        // we must wait for all "overwrites" to finish to actually remove a variable
                        let entry = conditionally_resolved_variables.get_mut(variable).unwrap();
                        let SingleAssignment::Conditional { condition, value } = expr else {
                            unreachable!()
                        };
                        let idx = entry
                            .iter()
                            .position(|(mask, el)| mask == condition && el == value)
                            .unwrap();
                        entry.remove(idx);

                        if entry.is_empty() {
                            // println!("Variable {:?} is now fully resolved as all conditional cases passed", variable);
                            conditionally_resolved_variables.remove(variable);
                            unresolved_variables.remove(variable);
                            resolved_variables.insert(*variable);
                        }
                    }
                }

                // skip this resolver in the future
                // println!("Resolver {} will be skipped in the future from considerations", resolver_idx);
                idxes_to_skip.insert(resolver_idx);

                let idx = resolution_sequence.len();
                resolution_sequence.insert(idx, details.clone());
            }

            let final_num_resolved = resolved_variables.len();
            let final_len = resolution_sequence.len();
            let final_skipped = idxes_to_skip.len();
            let final_conditional_resolved: usize = conditionally_resolved_variables
                .iter()
                .map(|el| el.1.len())
                .sum();

            let made_progress = final_num_resolved > initial_num_resolved
                || final_len > initial_len
                || final_skipped > initial_skipped
                || initial_conditional_resolved > final_conditional_resolved;

            if made_progress == false {
                println!("Left unresolved: {:?}", unresolved_variables);
                for var in unresolved_variables.iter() {
                    if unconditionally_resolved_variables.contains(var) {
                        println!("Variable {:?} should be unconditionally resolved", var);
                    } else {
                        assert!(conditionally_resolved_variables.contains_key(var));
                        let set = &conditionally_resolved_variables[var];
                        assert!(set.len() > 0);
                        println!("Variable {:?} should be conditionally resolved", var);
                    }
                    for (resolver_idx, resolver) in self.resolvers_data.iter().enumerate() {
                        if resolver.outputs.contains_key(var) {
                            println!(
                                "Variable {:?} must have been resolved in resolver number {}",
                                var, resolver_idx
                            );
                        }
                    }
                }

                panic!("Graph resolver is stuck");
            }
        }

        assert!(unresolved_variables.is_empty());
        assert_eq!(resolved_variables.len(), total_vars);

        // now we can do SSA

        let mut ssa_forms = vec![];

        let lookup_fn = |_, _| vec![];

        for (_, exprs) in resolution_sequence.iter() {
            // in general it is enough for us to:
            // - read inputs
            // - iterate between lookups and writes to get final values

            let mut mapper = SubexpressionsMapper::new();
            mapper.known_lookups = exprs.lookup_inputs.clone();
            mapper.known_maybe_lookups = exprs.maybe_lookup_inputs.clone();

            for input_expr in exprs.oracles.iter() {
                match input_expr {
                    Expression::Field(inner) => match inner {
                        a @ FieldNodeExpression::OracleValue { .. } => {
                            let mut subexpr = a.clone();
                            mapper.add_field_subexprs(&mut subexpr);
                            assert_matches!(subexpr, FieldNodeExpression::SubExpression(..));
                        }
                        _ => {
                            unreachable!();
                        }
                    },
                    Expression::U32(inner) => match inner {
                        a @ FixedWidthIntegerNodeExpression::U32OracleValue { .. } => {
                            let mut subexpr = a.clone();
                            mapper.add_integer_subexprs(&mut subexpr);
                            assert_matches!(
                                subexpr,
                                FixedWidthIntegerNodeExpression::U32SubExpression(..)
                            );
                        }
                        _ => {
                            unreachable!();
                        }
                    },
                    Expression::U16(inner) => match inner {
                        a @ FixedWidthIntegerNodeExpression::U16OracleValue { .. } => {
                            let mut subexpr = a.clone();
                            mapper.add_integer_subexprs(&mut subexpr);
                            assert_matches!(
                                subexpr,
                                FixedWidthIntegerNodeExpression::U16SubExpression(..)
                            );
                        }
                        _ => {
                            unreachable!();
                        }
                    },
                    Expression::Bool(inner) => match inner {
                        a @ BoolNodeExpression::OracleValue { .. } => {
                            let mut subexpr = a.clone();
                            mapper.add_boolean_subexprs(&mut subexpr);
                            assert_matches!(subexpr, BoolNodeExpression::SubExpression(..));
                        }
                        _ => {
                            unreachable!();
                        }
                    },
                    a @ _ => {
                        panic!("expression {:?} in oracle accesses", a);
                    }
                }
            }

            for (input_var, input_expr) in exprs.inputs.iter() {
                match input_expr {
                    Expression::Field(inner) => match inner {
                        a @ FieldNodeExpression::Place(input_var_2) => {
                            assert_eq!(input_var, input_var_2);
                            let mut subexpr = a.clone();
                            mapper.add_field_subexprs(&mut subexpr);
                            assert_matches!(subexpr, FieldNodeExpression::SubExpression(..));
                        }
                        _ => {
                            unreachable!();
                        }
                    },
                    Expression::Bool(inner) => match inner {
                        a @ BoolNodeExpression::Place(input_var_2) => {
                            assert_eq!(input_var, input_var_2);
                            let mut subexpr = a.clone();
                            mapper.add_boolean_subexprs(&mut subexpr);
                            assert_matches!(subexpr, BoolNodeExpression::SubExpression(..));
                        }
                        _ => {
                            unreachable!();
                        }
                    },
                    Expression::U8(inner) => match inner {
                        a @ FixedWidthIntegerNodeExpression::U8Place(input_var_2) => {
                            assert_eq!(input_var, input_var_2);
                            let mut subexpr = a.clone();
                            mapper.add_integer_subexprs(&mut subexpr);
                            assert_matches!(
                                subexpr,
                                FixedWidthIntegerNodeExpression::U8SubExpression(..)
                            );
                        }
                        _ => {
                            unreachable!();
                        }
                    },
                    Expression::U16(inner) => match inner {
                        a @ FixedWidthIntegerNodeExpression::U16Place(input_var_2) => {
                            assert_eq!(input_var, input_var_2);
                            let mut subexpr = a.clone();
                            mapper.add_integer_subexprs(&mut subexpr);
                            assert_matches!(
                                subexpr,
                                FixedWidthIntegerNodeExpression::U16SubExpression(..)
                            );
                        }
                        _ => {
                            unreachable!();
                        }
                    },
                    _ => {
                        todo!();
                    }
                }
            }

            if exprs.outputs.len() > 0 {
                assert_eq!(exprs.quasi_outputs_for_lookup_enforcements.len(), 0);
                // check that we do not have lookups that are just enforcements
                for el in exprs.lookup_inputs.iter() {
                    let (_idx, (_inputs, _table_id, num_outputs)) = el;
                    assert!(*num_outputs > 0, "not yet supported");
                }
            } else {
                // very basic logic for now
                assert!(exprs.lookup_inputs.len() == 1);
                assert!(exprs.maybe_lookup_inputs.is_empty());
                assert!(exprs.quasi_outputs_for_lookup_enforcements.len() > 0);
                assert_eq!(exprs.quasi_outputs_for_lookup_enforcements.len(), 1);

                // in this case we should just record lookups
                let lookup_index = exprs.quasi_outputs_for_lookup_enforcements[0];
                let (mut inputs, mut table_type, num_outputs) =
                    exprs.lookup_inputs[&lookup_index].clone();
                assert_eq!(num_outputs, 0);

                // println!("Add lookup enforcement at index {} with inputs {:?}, table ID = {:?} and {} outputs", lookup_index, &inputs, &table_type, num_outputs);

                let _ = mapper.enforce_lookup_relation_inner(
                    lookup_index,
                    &mut *inputs,
                    &mut table_type,
                    num_outputs,
                );

                ssa_forms.push(mapper.ssa_form);
                continue;
            }

            // now all the outputs will just trigger SSA (including materializing lookups)
            for (output_var, output_expr) in exprs.outputs.iter() {
                match output_expr {
                    SingleAssignment::Unconditional(expr) => {
                        let mut expr = expr.clone();
                        expr.make_subexpressions(&mut mapper, &lookup_fn);
                        match expr {
                            Expression::Field(FieldNodeExpression::SubExpression(_idx))
                            | Expression::Bool(BoolNodeExpression::SubExpression(_idx))
                            | Expression::U8(FixedWidthIntegerNodeExpression::U8SubExpression(
                                _idx,
                            ))
                            | Expression::U16(FixedWidthIntegerNodeExpression::U16SubExpression(
                                _idx,
                            ))
                            | Expression::U32(FixedWidthIntegerNodeExpression::U32SubExpression(
                                _idx,
                            )) => {
                                let write_expr = RawExpression::WriteVariable {
                                    into_variable: *output_var,
                                    source_subexpr: expr,
                                    condition_subexpr_idx: None,
                                };
                                mapper.ssa_form.push(write_expr)
                            }
                            a @ _ => {
                                println!("Full SSA:\n{:?}", &mapper.ssa_form);
                                panic!("Unexpected output expression {:?}", a);
                            }
                        }
                    }
                    SingleAssignment::Conditional { condition, value } => {
                        let mut condition = condition.clone();
                        condition.make_subexpressions(&mut mapper, &lookup_fn);

                        let mut value = value.clone();
                        value.make_subexpressions(&mut mapper, &lookup_fn);

                        let BoolNodeExpression::SubExpression(condition_idx) = condition else {
                            unreachable!()
                        };

                        match value {
                            Expression::Field(FieldNodeExpression::SubExpression(_idx))
                            | Expression::Bool(BoolNodeExpression::SubExpression(_idx))
                            | Expression::U8(FixedWidthIntegerNodeExpression::U8SubExpression(
                                _idx,
                            ))
                            | Expression::U16(FixedWidthIntegerNodeExpression::U16SubExpression(
                                _idx,
                            ))
                            | Expression::U32(FixedWidthIntegerNodeExpression::U32SubExpression(
                                _idx,
                            )) => {
                                let write_expr = RawExpression::WriteVariable {
                                    into_variable: *output_var,
                                    source_subexpr: value.clone(),
                                    condition_subexpr_idx: Some(condition_idx),
                                };
                                mapper.ssa_form.push(write_expr)
                            }
                            a @ _ => {
                                println!("Full SSA:\n{:?}", &mapper.ssa_form);
                                panic!("Unexpected output expression {:?}", a);
                            }
                        }
                    }
                }
            }

            ssa_forms.push(mapper.ssa_form);
        }

        (resolution_sequence, ssa_forms)
    }
}

impl<F: PrimeField> WitnessTypeSet<F> for WitnessGraphCreator<F> {
    const CAN_BRANCH: bool = false;
    const MERGE_LOOKUP_AND_MULTIPLICITY_COUNT: bool = true;

    type Mask = BoolNodeExpression<F>;
    type Field = FieldNodeExpression<F>;
    type I32 = FixedWidthIntegerNodeExpression<F>;
    type U32 = FixedWidthIntegerNodeExpression<F>;
    type U16 = FixedWidthIntegerNodeExpression<F>;
    type U8 = FixedWidthIntegerNodeExpression<F>;

    #[inline(always)]
    #[track_caller]
    fn branch(_mask: &Self::Mask) -> bool {
        unreachable!()
    }
}

impl<F: PrimeField> WitnessPlacer<F> for WitnessGraphCreator<F> {
    fn record_resolver(&mut self, resolver: impl WitnessResolutionDescription<F, Self>) {
        assert!(self.current_stats_resolver.is_none());
        self.current_stats_resolver = Some(ResolverDetails::new());
        resolver.evaluate(self);
        let resolver = self.current_stats_resolver.take().unwrap();
        self.resolvers_data.push(resolver);
    }

    fn get_oracle_field(&mut self, placeholder: Placeholder, subindex: usize) -> Self::Field {
        let expr = FieldNodeExpression::OracleValue {
            placeholder,
            subindex,
        };
        if let Some(stats) = self.current_stats_resolver.as_mut() {
            stats.oracles.push(Expression::Field(expr.clone()));
        }

        expr
    }
    fn get_oracle_u32(&mut self, placeholder: Placeholder) -> Self::U32 {
        let expr = FixedWidthIntegerNodeExpression::U32OracleValue { placeholder };

        if let Some(stats) = self.current_stats_resolver.as_mut() {
            stats.oracles.push(Expression::U32(expr.clone()));
        }

        expr
    }
    fn get_oracle_u16(&mut self, placeholder: Placeholder) -> Self::U16 {
        let expr = FixedWidthIntegerNodeExpression::U16OracleValue { placeholder };

        if let Some(stats) = self.current_stats_resolver.as_mut() {
            stats.oracles.push(Expression::U16(expr.clone()));
        }

        expr
    }
    fn get_oracle_u8(&mut self, placeholder: Placeholder) -> Self::U8 {
        let expr = FixedWidthIntegerNodeExpression::U8OracleValue { placeholder };

        if let Some(stats) = self.current_stats_resolver.as_mut() {
            stats.oracles.push(Expression::U8(expr.clone()));
        }

        expr
    }
    fn get_oracle_boolean(&mut self, placeholder: Placeholder) -> Self::Mask {
        let expr = BoolNodeExpression::OracleValue { placeholder };

        if let Some(stats) = self.current_stats_resolver.as_mut() {
            stats.oracles.push(Expression::Bool(expr.clone()));
        }

        expr
    }

    #[track_caller]
    fn get_field(&mut self, variable: Variable) -> Self::Field {
        let _ = self.resize_to_assign(variable);

        let value = FieldNodeExpression::Place(variable);
        if let Some(stats) = self.current_stats_resolver.as_mut() {
            stats
                .inputs
                .insert(variable, Expression::Field(value.clone()));
        }

        value
    }

    #[track_caller]
    fn get_boolean(&mut self, variable: Variable) -> Self::Mask {
        let _ = self.resize_to_assign(variable);

        let value = BoolNodeExpression::Place(variable);
        if let Some(stats) = self.current_stats_resolver.as_mut() {
            stats
                .inputs
                .insert(variable, Expression::Bool(value.clone()));
        }

        value
    }

    #[track_caller]
    fn get_u16(&mut self, variable: Variable) -> Self::U16 {
        let _ = self.resize_to_assign(variable);

        let value = FixedWidthIntegerNodeExpression::U16Place(variable);
        if let Some(stats) = self.current_stats_resolver.as_mut() {
            stats
                .inputs
                .insert(variable, Expression::U16(value.clone()));
        }

        value
    }

    #[track_caller]
    fn get_u8(&mut self, variable: Variable) -> Self::U8 {
        let _ = self.resize_to_assign(variable);

        let value = FixedWidthIntegerNodeExpression::U8Place(variable);
        if let Some(stats) = self.current_stats_resolver.as_mut() {
            stats.inputs.insert(variable, Expression::U8(value.clone()));
        }

        value
    }

    #[track_caller]
    fn assign_mask(&mut self, variable: Variable, value: &Self::Mask) {
        let idx = self.resize_to_assign(variable);
        if let Some(expr) = self.values[idx].as_mut() {
            match expr {
                AssignedExpression::Unconditional(..) => {
                    panic!("unconditional reassignement of {:?}", variable);
                }
                AssignedExpression::Conditional {
                    temporary_assignments,
                    final_assignment,
                } => {
                    assert!(temporary_assignments.len() > 0);
                    // NOTE: this is fine - we make it precise AFTER we potentially used all other temporaries
                    // for other intermediate witnesses. We can also postprocess such graph to only evaluate unconditional case
                    assert!(final_assignment.is_none());

                    *final_assignment = Some(Expression::Bool(value.clone()));

                    if let Some(stats) = self.current_stats_resolver.as_mut() {
                        stats.outputs.insert(
                            variable,
                            SingleAssignment::Unconditional(Expression::Bool(value.clone())),
                        );
                    }
                }
            }
        } else {
            let expr = AssignedExpression::Unconditional(Expression::Bool(value.clone()));
            self.values[idx] = Some(expr);

            if let Some(stats) = self.current_stats_resolver.as_mut() {
                stats.outputs.insert(
                    variable,
                    SingleAssignment::Unconditional(Expression::Bool(value.clone())),
                );
            }
        }
    }

    #[track_caller]
    fn assign_field(&mut self, variable: Variable, value: &Self::Field) {
        let idx = self.resize_to_assign(variable);
        if let Some(expr) = self.values[idx].as_mut() {
            match expr {
                AssignedExpression::Unconditional(..) => {
                    panic!("unconditional reassignement of {:?}", variable);
                }
                AssignedExpression::Conditional {
                    temporary_assignments,
                    final_assignment,
                } => {
                    assert!(temporary_assignments.len() > 0);
                    // NOTE: this is fine - we make it precise AFTER we potentially used all other temporaries
                    // for other intermediate witnesses. We can also postprocess such graph to only evaluate unconditional case
                    assert!(final_assignment.is_none());

                    *final_assignment = Some(Expression::Field(value.clone()));

                    if let Some(stats) = self.current_stats_resolver.as_mut() {
                        stats.outputs.insert(
                            variable,
                            SingleAssignment::Unconditional(Expression::Field(value.clone())),
                        );
                    }
                }
            }
        } else {
            let expr = AssignedExpression::Unconditional(Expression::Field(value.clone()));
            self.values[idx] = Some(expr);

            if let Some(stats) = self.current_stats_resolver.as_mut() {
                stats.outputs.insert(
                    variable,
                    SingleAssignment::Unconditional(Expression::Field(value.clone())),
                );
            }
        }
    }

    #[track_caller]
    fn assign_u16(&mut self, variable: Variable, value: &Self::U16) {
        let idx = self.resize_to_assign(variable);
        if let Some(expr) = self.values[idx].as_mut() {
            match expr {
                AssignedExpression::Unconditional(..) => {
                    panic!("unconditional reassignement of {:?}", variable);
                }
                AssignedExpression::Conditional {
                    temporary_assignments,
                    final_assignment,
                } => {
                    assert!(temporary_assignments.len() > 0);
                    // NOTE: this is fine - we make it precise AFTER we potentially used all other temporaries
                    // for other intermediate witnesses. We can also postprocess such graph to only evaluate unconditional case
                    assert!(final_assignment.is_none());

                    *final_assignment = Some(Expression::U16(value.clone()));

                    if let Some(stats) = self.current_stats_resolver.as_mut() {
                        stats.outputs.insert(
                            variable,
                            SingleAssignment::Unconditional(Expression::U16(value.clone())),
                        );
                    }
                }
            }
        } else {
            let expr = AssignedExpression::Unconditional(Expression::U16(value.clone()));
            self.values[idx] = Some(expr);

            if let Some(stats) = self.current_stats_resolver.as_mut() {
                stats.outputs.insert(
                    variable,
                    SingleAssignment::Unconditional(Expression::U16(value.clone())),
                );
            }
        }
    }

    #[track_caller]
    fn assign_u8(&mut self, variable: Variable, value: &Self::U8) {
        let idx = self.resize_to_assign(variable);
        if let Some(expr) = self.values[idx].as_mut() {
            match expr {
                AssignedExpression::Unconditional(..) => {
                    panic!("unconditional reassignement of {:?}", variable);
                }
                AssignedExpression::Conditional {
                    temporary_assignments,
                    final_assignment,
                } => {
                    assert!(temporary_assignments.len() > 0);
                    // NOTE: this is fine - we make it precise AFTER we potentially used all other temporaries
                    // for other intermediate witnesses. We can also postprocess such graph to only evaluate unconditional case
                    assert!(final_assignment.is_none());

                    *final_assignment = Some(Expression::U8(value.clone()));

                    if let Some(stats) = self.current_stats_resolver.as_mut() {
                        stats.outputs.insert(
                            variable,
                            SingleAssignment::Unconditional(Expression::U8(value.clone())),
                        );
                    }
                }
            }
        } else {
            let expr = AssignedExpression::Unconditional(Expression::U8(value.clone()));
            self.values[idx] = Some(expr);

            if let Some(stats) = self.current_stats_resolver.as_mut() {
                stats.outputs.insert(
                    variable,
                    SingleAssignment::Unconditional(Expression::U8(value.clone())),
                );
            }
        }
    }

    #[track_caller]
    fn conditionally_assign_mask(
        &mut self,
        variable: Variable,
        mask: &Self::Mask,
        value: &Self::Mask,
    ) {
        let idx = self.resize_to_assign(variable);
        if let Some(expr) = self.values[idx].as_mut() {
            let AssignedExpression::Conditional {
                temporary_assignments,
                final_assignment,
            } = expr
            else {
                panic!(
                    "conditional reassignement of unconditionally assigned variable {:?}",
                    variable
                );
            };
            assert!(final_assignment.is_none());
            assert_matches!(
                temporary_assignments.last().unwrap(),
                (_, Expression::Bool(..))
            );
            temporary_assignments.push((mask.clone(), Expression::Bool(value.clone())));
        } else {
            let expr = AssignedExpression::Conditional {
                temporary_assignments: vec![(mask.clone(), Expression::Bool(value.clone()))],
                final_assignment: None,
            };
            self.values[idx] = Some(expr);
        }

        if let Some(stats) = self.current_stats_resolver.as_mut() {
            let expr = SingleAssignment::Conditional {
                condition: mask.clone(),
                value: Expression::Bool(value.clone()),
            };
            stats.outputs.insert(variable, expr);
        }
    }

    #[track_caller]
    fn conditionally_assign_field(
        &mut self,
        variable: Variable,
        mask: &Self::Mask,
        value: &Self::Field,
    ) {
        let idx = self.resize_to_assign(variable);
        if let Some(expr) = self.values[idx].as_mut() {
            let AssignedExpression::Conditional {
                temporary_assignments,
                final_assignment,
            } = expr
            else {
                panic!(
                    "conditional reassignement of unconditionally assigned variable {:?}",
                    variable
                );
            };
            assert!(final_assignment.is_none());
            assert_matches!(
                temporary_assignments.last().unwrap(),
                (_, Expression::Field(..))
            );
            temporary_assignments.push((mask.clone(), Expression::Field(value.clone())));
        } else {
            let expr = AssignedExpression::Conditional {
                temporary_assignments: vec![(mask.clone(), Expression::Field(value.clone()))],
                final_assignment: None,
            };
            self.values[idx] = Some(expr);
        }

        if let Some(stats) = self.current_stats_resolver.as_mut() {
            let expr = SingleAssignment::Conditional {
                condition: mask.clone(),
                value: Expression::Field(value.clone()),
            };
            stats.outputs.insert(variable, expr);
        }
    }

    #[track_caller]
    fn conditionally_assign_u16(
        &mut self,
        variable: Variable,
        mask: &Self::Mask,
        value: &Self::U16,
    ) {
        let idx = self.resize_to_assign(variable);
        if let Some(expr) = self.values[idx].as_mut() {
            let AssignedExpression::Conditional {
                temporary_assignments,
                final_assignment,
            } = expr
            else {
                panic!(
                    "conditional reassignement of unconditionally assigned variable {:?}",
                    variable
                );
            };
            assert!(final_assignment.is_none());
            assert_matches!(
                temporary_assignments.last().unwrap(),
                (_, Expression::U16(..))
            );
            temporary_assignments.push((mask.clone(), Expression::U16(value.clone())));
        } else {
            let expr = AssignedExpression::Conditional {
                temporary_assignments: vec![(mask.clone(), Expression::U16(value.clone()))],
                final_assignment: None,
            };
            self.values[idx] = Some(expr);
        }

        if let Some(stats) = self.current_stats_resolver.as_mut() {
            let expr = SingleAssignment::Conditional {
                condition: mask.clone(),
                value: Expression::U16(value.clone()),
            };
            stats.outputs.insert(variable, expr);
        }
    }

    #[track_caller]
    fn conditionally_assign_u8(&mut self, variable: Variable, mask: &Self::Mask, value: &Self::U8) {
        let idx = self.resize_to_assign(variable);
        if let Some(expr) = self.values[idx].as_mut() {
            let AssignedExpression::Conditional {
                temporary_assignments,
                final_assignment,
            } = expr
            else {
                panic!(
                    "conditional reassignement of unconditionally assigned variable {:?}",
                    variable
                );
            };
            assert!(final_assignment.is_none());
            assert_matches!(
                temporary_assignments.last().unwrap(),
                (_, Expression::U8(..))
            );
            temporary_assignments.push((mask.clone(), Expression::U8(value.clone())));
        } else {
            let expr = AssignedExpression::Conditional {
                temporary_assignments: vec![(mask.clone(), Expression::U8(value.clone()))],
                final_assignment: None,
            };
            self.values[idx] = Some(expr);
        }

        if let Some(stats) = self.current_stats_resolver.as_mut() {
            let expr = SingleAssignment::Conditional {
                condition: mask.clone(),
                value: Expression::U8(value.clone()),
            };
            stats.outputs.insert(variable, expr);
        }
    }

    #[track_caller]
    fn lookup<const M: usize, const N: usize>(
        &mut self,
        inputs: &[Self::Field; M],
        table_id: &Self::U16,
    ) -> [Self::Field; N] {
        let inputs = inputs.to_vec().into_boxed_slice();
        let lookup_idx = self.lookups.len();
        // println!(
        //     "Normal lookup with {} outputs and table ID {:?} at index {}",
        //     N, table_id, lookup_idx
        // );
        let lookup = (inputs.clone(), table_id.clone(), N);
        self.lookups.push(lookup.clone());

        if let Some(stats) = self.current_stats_resolver.as_mut() {
            stats.lookup_inputs.insert(lookup_idx, lookup);
        }

        std::array::from_fn(|i| FieldNodeExpression::LookupOutput {
            lookup_idx,
            output_idx: i,
        })
    }

    #[track_caller]
    fn maybe_lookup<const M: usize, const N: usize>(
        &mut self,
        inputs: &[Self::Field; M],
        table_id: &Self::U16,
        mask: &Self::Mask,
    ) -> [Self::Field; N] {
        let inputs = inputs.to_vec().into_boxed_slice();
        let lookup_idx = self.maybe_lookups.len();
        let lookup = (inputs.clone(), table_id.clone(), mask.clone(), N);
        self.maybe_lookups.push(lookup.clone());

        if let Some(stats) = self.current_stats_resolver.as_mut() {
            stats.maybe_lookup_inputs.insert(lookup_idx, lookup);
        }

        std::array::from_fn(|i| FieldNodeExpression::MaybeLookupOutput {
            lookup_idx,
            output_idx: i,
        })
    }

    #[track_caller]
    fn lookup_enforce<const M: usize>(&mut self, inputs: &[Self::Field; M], table_id: &Self::U16) {
        let inputs = inputs.to_vec().into_boxed_slice();
        let lookup_idx = self.lookups.len();
        // println!("Lookup enforcement with table ID {:?} at index {}", table_id, lookup_idx);
        let lookup = (inputs.clone(), table_id.clone(), 0);
        self.lookups.push(lookup.clone());

        if let Some(stats) = self.current_stats_resolver.as_mut() {
            stats.lookup_inputs.insert(lookup_idx, lookup);
            // record that even though it'll never get an output expression, it must be followed
            stats.quasi_outputs_for_lookup_enforcements.push(lookup_idx);
        }
    }
}

pub fn witness_early_branch_if_possible<
    F: PrimeField,
    W: WitnessPlacer<F>,
    T: WitnessResolutionDescription<F, W>,
>(
    branch_mask: W::Mask,
    placer: &mut W,
    node: &T,
) {
    if W::CAN_BRANCH {
        if W::branch(&branch_mask) {
            node.evaluate(placer);
        }
    } else {
        // we should use conditional assignment anyway
        node.evaluate(placer);
    }
}
