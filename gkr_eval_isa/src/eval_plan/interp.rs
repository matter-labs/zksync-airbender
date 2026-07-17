//! Value-authoritative interpreter for symbolic evaluation plans.

use std::collections::HashMap;

use cs::gkr_compiler::dag_ir::{DagLayer, Ext, Resolvers, RootId, SinkInfo, eval_layer_expr};
use field::Field;

use super::{
    CacheStoreFrom, EvalOp, EvalPlan, MaterializeFrom, Operand, RootKey, TempId, ValueFingerprint,
    ValueRef,
};

#[derive(Clone, Debug, PartialEq)]
pub struct RootObservation {
    pub root_id: Option<RootId>,
    pub root: RootKey,
    pub sink: Option<SinkInfo>,
    pub value: Ext,
}

#[derive(Clone, Debug, PartialEq)]
pub struct PlanExecution {
    pub roots: Vec<RootObservation>,
    pub residents: HashMap<ValueFingerprint, Ext>,
    /// Values materialized by `CacheStore`, in execution order. This makes the
    /// absence of an independently-materialized fused product directly testable.
    pub stored_values: Vec<ValueRef>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PlanInterpError {
    MissingAccumulator,
    DuplicateTemp(TempId),
    MissingTemp(TempId),
    MissingResident(ValueFingerprint),
    MissingDroppedResident(ValueFingerprint),
    CacheStoreValueMismatch(ValueFingerprint),
    LiveTempsAtEnd(Vec<TempId>),
}

/// Execute a symbolic plan for one row. Source values are resolved through the
/// canonical DAG evaluator, while accumulator/cache/temp behavior is interpreted
/// from the plan itself.
pub fn interpret_plan(
    plan: &EvalPlan,
    layer: &DagLayer,
    row: usize,
    resolvers: &Resolvers<'_>,
) -> Result<PlanExecution, PlanInterpError> {
    let mut machine = Machine {
        layer,
        row,
        resolvers,
        acc: None,
        temps: HashMap::new(),
        residents: HashMap::new(),
        roots: Vec::new(),
        stored_values: Vec::new(),
    };
    for op in &plan.ops {
        machine.execute(op)?;
    }
    if !machine.temps.is_empty() {
        let mut live: Vec<TempId> = machine.temps.keys().copied().collect();
        live.sort_by_key(|temp| temp.0);
        return Err(PlanInterpError::LiveTempsAtEnd(live));
    }
    Ok(PlanExecution {
        roots: machine.roots,
        residents: machine.residents,
        stored_values: machine.stored_values,
    })
}

struct Machine<'a> {
    layer: &'a DagLayer,
    row: usize,
    resolvers: &'a Resolvers<'a>,
    acc: Option<Ext>,
    temps: HashMap<TempId, Ext>,
    residents: HashMap<ValueFingerprint, Ext>,
    roots: Vec<RootObservation>,
    stored_values: Vec<ValueRef>,
}

impl Machine<'_> {
    fn execute(&mut self, op: &EvalOp) -> Result<(), PlanInterpError> {
        match op {
            EvalOp::AccInit(operand) => {
                self.acc = Some(self.operand(*operand)?);
            }
            EvalOp::AccAdd { sign, operand } => {
                let rhs = self.operand(*operand)?;
                let acc = self
                    .acc
                    .as_mut()
                    .ok_or(PlanInterpError::MissingAccumulator)?;
                match sign {
                    crate::fwd::isa::Sign::Plus => acc.add_assign(&rhs),
                    crate::fwd::isa::Sign::Minus => acc.sub_assign(&rhs),
                };
            }
            EvalOp::AccMul(operand) => {
                let rhs = self.operand(*operand)?;
                let acc = self
                    .acc
                    .as_mut()
                    .ok_or(PlanInterpError::MissingAccumulator)?;
                acc.mul_assign(&rhs);
            }
            EvalOp::AccFma { sign, lhs, rhs } => {
                let mut product = self.operand(*lhs)?;
                let rhs = self.operand(*rhs)?;
                product.mul_assign(&rhs);
                let acc = self
                    .acc
                    .as_mut()
                    .ok_or(PlanInterpError::MissingAccumulator)?;
                match sign {
                    crate::fwd::isa::Sign::Plus => acc.add_assign(&product),
                    crate::fwd::isa::Sign::Minus => acc.sub_assign(&product),
                };
            }
            EvalOp::AccNeg => {
                self.acc
                    .as_mut()
                    .ok_or(PlanInterpError::MissingAccumulator)?
                    .negate();
            }
            EvalOp::SaveAcc(temp) => {
                let value = self.acc.ok_or(PlanInterpError::MissingAccumulator)?;
                if self.temps.insert(temp.id, value).is_some() {
                    return Err(PlanInterpError::DuplicateTemp(temp.id));
                }
            }
            EvalOp::CacheStore { value, from } => {
                let stored = match from {
                    CacheStoreFrom::Acc => self.acc.ok_or(PlanInterpError::MissingAccumulator)?,
                    CacheStoreFrom::Source => self.source(*value),
                };
                // Cache stores are semantic checkpoints: the claimed value must
                // equal the authoritative expression regardless of its origin.
                if stored != eval_layer_expr(self.layer, value.expr, self.row, self.resolvers) {
                    return Err(PlanInterpError::CacheStoreValueMismatch(value.fingerprint));
                }
                self.residents.insert(value.fingerprint, stored);
                self.stored_values.push(*value);
            }
            EvalOp::CacheDrop(value) => {
                if self.residents.remove(&value.fingerprint).is_none() {
                    return Err(PlanInterpError::MissingDroppedResident(value.fingerprint));
                }
            }
            EvalOp::Commit {
                root_id,
                root,
                sink,
                from,
            } => {
                let value = match from {
                    MaterializeFrom::Acc => self.acc.ok_or(PlanInterpError::MissingAccumulator)?,
                    MaterializeFrom::Source(value) => self.source(*value),
                };
                self.roots.push(RootObservation {
                    root_id: Some(*root_id),
                    root: root.clone(),
                    sink: Some(sink.clone()),
                    value,
                });
            }
            EvalOp::ReturnAcc { root } => {
                let value = self.acc.ok_or(PlanInterpError::MissingAccumulator)?;
                self.roots.push(RootObservation {
                    root_id: None,
                    root: root.clone(),
                    sink: None,
                    value,
                });
            }
        }
        Ok(())
    }

    fn operand(&mut self, operand: Operand) -> Result<Ext, PlanInterpError> {
        match operand {
            Operand::Source(value) => Ok(self.source(value)),
            Operand::Resident(value) => self
                .residents
                .get(&value.fingerprint)
                .copied()
                .ok_or(PlanInterpError::MissingResident(value.fingerprint)),
            Operand::Temp(temp) => self
                .temps
                .remove(&temp.id)
                .ok_or(PlanInterpError::MissingTemp(temp.id)),
            Operand::Unit { negative } => {
                let mut value = Ext::ONE;
                if negative {
                    value.negate();
                }
                Ok(value)
            }
        }
    }

    fn source(&self, value: ValueRef) -> Ext {
        eval_layer_expr(self.layer, value.expr, self.row, self.resolvers)
    }
}
