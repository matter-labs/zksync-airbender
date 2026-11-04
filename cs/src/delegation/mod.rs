use crate::constraint::*;
use crate::cs::circuit::{BatchedMemoryAccessType, Circuit};
use crate::tables::TableDriver;
use crate::tables::TableType;
use crate::types::*;
use field::PrimeField;

pub mod bigint_with_control;
pub mod blake2_round_with_extended_control;
pub mod blake2_single_round;
pub mod keccak_special5;

pub fn dump_ssa_witness_eval_form_for_delegation<F: PrimeField, T: Sized>(
    definition_fn: impl Fn(
        &mut crate::cs::cs_reference::BasicAssembly<
            F,
            crate::cs::witness_placer::graph_description::WitnessGraphCreator<F>,
        >,
    ) -> T,
) -> Vec<Vec<crate::cs::witness_placer::graph_description::RawExpression<F>>> {
    use crate::cs::cs_reference::BasicAssembly;
    use crate::cs::witness_placer::graph_description::WitnessGraphCreator;
    let mut cs = BasicAssembly::<F, WitnessGraphCreator<F>>::new();
    cs.witness_placer = Some(WitnessGraphCreator::<F>::new());
    definition_fn(&mut cs);
    let (_, witness_placer) = cs.finalize();

    let graph = witness_placer.unwrap();
    let (_resolution_order, ssa_forms) = graph.compute_resolution_order();

    ssa_forms
}
