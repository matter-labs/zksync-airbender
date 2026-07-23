use std::collections::HashMap;

use cs::gkr_compiler::dag_ir::{eval_layer_expr, DagLayer, Ext, Resolvers, RootId, SinkInfo};
use field::Field;

use crate::bwd::distill::DistilledLayer;
use crate::bwd::source::BwdSpecialTable;

use super::interp::resolve_backward_special;
use super::{
    CacheStoreFrom, MaterializeFrom, Operand, PackedEvalOp, PackedEvalPlan, PlanExecution,
    PlanInterpError, RootKey, RootObservation, TempId, ValueFingerprint, ValueRef,
};

/// Execute the grouped accumulator operations directly. This does not expand
/// them back into scalar `EvalOp`s, so value parity checks exercise the actual
/// multi-arity Add/Mul/FMA semantics produced by the packer.
pub fn interpret_packed_plan(
    plan: &PackedEvalPlan,
    layer: &DagLayer,
    row: usize,
    resolvers: &Resolvers<'_>,
) -> Result<PlanExecution, PlanInterpError> {
    let mut machine = PackedMachine {
        layer,
        row,
        resolvers,
        backward: None,
        acc: None,
        batch_acc: Ext::ZERO,
        batch_sinks: 0,
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

pub fn interpret_backward_packed_plan(
    plan: &PackedEvalPlan,
    distilled: &DistilledLayer,
    specials: &BwdSpecialTable,
    acc_init_desc: Option<u16>,
    row: usize,
    resolvers: &Resolvers<'_>,
) -> Result<PlanExecution, PlanInterpError> {
    let batch_acc = acc_init_desc
        .map(|desc| resolve_backward_special(desc, distilled, specials, resolvers))
        .transpose()?
        .unwrap_or(Ext::ZERO);
    let mut machine = PackedMachine {
        layer: &distilled.layer,
        row,
        resolvers,
        backward: Some((distilled, specials)),
        acc: None,
        batch_acc,
        batch_sinks: 0,
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

struct PackedMachine<'a> {
    layer: &'a DagLayer,
    row: usize,
    resolvers: &'a Resolvers<'a>,
    backward: Option<(&'a DistilledLayer, &'a BwdSpecialTable)>,
    acc: Option<Ext>,
    batch_acc: Ext,
    batch_sinks: usize,
    temps: HashMap<TempId, Ext>,
    residents: HashMap<ValueFingerprint, Ext>,
    roots: Vec<RootObservation>,
    stored_values: Vec<ValueRef>,
}

impl PackedMachine<'_> {
    fn execute(&mut self, op: &PackedEvalOp) -> Result<(), PlanInterpError> {
        match op {
            PackedEvalOp::AccInit(operand) => {
                self.acc = Some(self.operand(*operand)?);
            }
            PackedEvalOp::AccAdd { sign, operands, .. } => {
                for &operand in operands {
                    let rhs = self.operand(operand)?;
                    let acc = self
                        .acc
                        .as_mut()
                        .ok_or(PlanInterpError::MissingAccumulator)?;
                    match sign {
                        crate::fwd::isa::Sign::Plus => acc.add_assign(&rhs),
                        crate::fwd::isa::Sign::Minus => acc.sub_assign(&rhs),
                    };
                }
            }
            PackedEvalOp::AccMul { sign, operands, .. } => {
                if *sign == crate::fwd::isa::Sign::Minus {
                    self.acc
                        .as_mut()
                        .ok_or(PlanInterpError::MissingAccumulator)?
                        .negate();
                }
                for &operand in operands {
                    let rhs = self.operand(operand)?;
                    self.acc
                        .as_mut()
                        .ok_or(PlanInterpError::MissingAccumulator)?
                        .mul_assign(&rhs);
                }
            }
            PackedEvalOp::AccFma { sign, pairs, .. } => {
                for &(lhs, rhs) in pairs {
                    let mut product = self.operand(lhs)?;
                    product.mul_assign(&self.operand(rhs)?);
                    let acc = self
                        .acc
                        .as_mut()
                        .ok_or(PlanInterpError::MissingAccumulator)?;
                    match sign {
                        crate::fwd::isa::Sign::Plus => acc.add_assign(&product),
                        crate::fwd::isa::Sign::Minus => acc.sub_assign(&product),
                    };
                }
            }
            PackedEvalOp::SaveAcc(temp) => {
                let value = self.acc.ok_or(PlanInterpError::MissingAccumulator)?;
                if self.temps.insert(temp.id, value).is_some() {
                    return Err(PlanInterpError::DuplicateTemp(temp.id));
                }
            }
            PackedEvalOp::CacheStore { value, from } => {
                let stored = match from {
                    CacheStoreFrom::Acc => self.acc.ok_or(PlanInterpError::MissingAccumulator)?,
                    CacheStoreFrom::Source => self.source(*value),
                };
                if stored != eval_layer_expr(self.layer, value.expr, self.row, self.resolvers) {
                    return Err(PlanInterpError::CacheStoreValueMismatch(value.fingerprint));
                }
                self.residents.insert(value.fingerprint, stored);
                self.stored_values.push(*value);
            }
            PackedEvalOp::CacheDrop(value) => {
                if self.residents.remove(&value.fingerprint).is_none() {
                    return Err(PlanInterpError::MissingDroppedResident(value.fingerprint));
                }
            }
            PackedEvalOp::Commit {
                root_id,
                root,
                sink,
                from,
            } => {
                let value = match from {
                    MaterializeFrom::Acc => self.acc.ok_or(PlanInterpError::MissingAccumulator)?,
                    MaterializeFrom::Source(value) => self.source(*value),
                };
                self.observe(Some(*root_id), root, Some(sink.clone()), value);
            }
            PackedEvalOp::BatchAccumulate {
                coefficient_desc, ..
            } => {
                let contribution = self.acc.ok_or(PlanInterpError::MissingAccumulator)?;
                let mut contribution = contribution;
                if let Some(desc) = coefficient_desc {
                    let (distilled, specials) = self
                        .backward
                        .ok_or(PlanInterpError::BackwardSpecialRequiresBindings { desc: *desc })?;
                    contribution.mul_assign(&resolve_backward_special(
                        *desc,
                        distilled,
                        specials,
                        self.resolvers,
                    )?);
                }
                self.batch_acc.add_assign(&contribution);
                self.batch_sinks += 1;
            }
            PackedEvalOp::ReturnBatch { root } => {
                if self.batch_sinks == 0 {
                    return Err(PlanInterpError::SinkFreeBatch);
                }
                self.observe(None, root, None, self.batch_acc);
            }
            PackedEvalOp::ReturnAcc { root } => {
                let value = self.acc.ok_or(PlanInterpError::MissingAccumulator)?;
                self.observe(None, root, None, value);
            }
        }
        Ok(())
    }

    fn observe(
        &mut self,
        root_id: Option<RootId>,
        root: &RootKey,
        sink: Option<SinkInfo>,
        value: Ext,
    ) {
        self.roots.push(RootObservation {
            root_id,
            root: root.clone(),
            sink,
            value,
        });
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
            Operand::BackwardSpecial { desc } => {
                let (distilled, specials) = self
                    .backward
                    .ok_or(PlanInterpError::BackwardSpecialRequiresBindings { desc })?;
                resolve_backward_special(desc, distilled, specials, self.resolvers)
            }
        }
    }

    fn source(&self, value: ValueRef) -> Ext {
        eval_layer_expr(self.layer, value.expr, self.row, self.resolvers)
    }
}
