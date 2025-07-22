pub mod decoder;

pub use self::decoder::*;
use super::*;

pub mod add_sub_lui_auipc_mop;
pub mod inits_and_teardowns;
pub mod jump_branch_slt;
pub mod load_store;
pub mod load_store_subword_only;
pub mod load_store_word_only;
pub mod mul_div;
pub mod shift_binary_csr;

use crate::cs::witness_placer::graph_description::WitnessGraphCreator;
use crate::{definitions::*, one_row_compiler::CompiledCircuitArtifact};

pub fn compile_unrolled_circuit_state_transition<F: PrimeField>(
    table_addition_fn: &dyn Fn(&mut crate::cs::cs_reference::BasicAssembly<F>) -> (),
    circuit_fn: &dyn Fn(&mut crate::cs::cs_reference::BasicAssembly<F>) -> (),
    max_bytecode_size_in_words: usize,
    trace_len_log2: usize,
) -> CompiledCircuitArtifact<F> {
    use crate::cs::cs_reference::BasicAssembly;
    use crate::one_row_compiler::OneRowCompiler;

    let mut cs = BasicAssembly::<F>::new();
    (table_addition_fn)(&mut cs);
    (circuit_fn)(&mut cs);

    let (cs_output, _) = cs.finalize();

    let compiler = OneRowCompiler::default();
    let compiled = compiler.compile_executor_circuit_assuming_preprocessed_bytecode(
        cs_output,
        max_bytecode_size_in_words,
        trace_len_log2,
    );

    compiled
}
// impl<F: PrimeField> From<OpcodeFamilyCircuitState<F>> for FamilyInput<F>{
//     fn from(inputs: OpcodeFamilyCircuitState<F>) -> Self {
//         Self {
//             pc: Register(inputs.cycle_start_state.pc.map(|x| Num::Var(x))),
//             f3: inputs.decoder_data.funct3,
//             bitmask: inputs.decoder_data.circuit_family_extra_mask,
//             rs1_index: inputs.decoder_data.rs1_index,
//             rs2_index: inputs.decoder_data.rs2_index,
//             rd_index: inputs.decoder_data.rd_index,
//             immediate: Register(inputs.decoder_data.imm.map(Num::Var)),
//             is_rd_x0: Boolean::Is(inputs.decoder_data.rd_is_zero)
//         }
//     }
// }

pub fn dump_wintess_graph_for_unrolled_circuit<F: PrimeField>(
    table_addition_fn: &dyn Fn(
        &mut crate::cs::cs_reference::BasicAssembly<F, WitnessGraphCreator<F>>,
    ) -> (),
    circuit_fn: &dyn Fn(
        &mut crate::cs::cs_reference::BasicAssembly<F, WitnessGraphCreator<F>>,
    ) -> (),
) -> WitnessGraphCreator<F> {
    use crate::cs::cs_reference::BasicAssembly;
    let mut cs = BasicAssembly::<F, WitnessGraphCreator<F>>::new();
    cs.witness_placer = Some(WitnessGraphCreator::<F>::new());
    (table_addition_fn)(&mut cs);
    (circuit_fn)(&mut cs);

    let (_, witness_placer) = cs.finalize();

    witness_placer.unwrap()
}

pub fn dump_ssa_witness_eval_form_for_unrolled_circuit<F: PrimeField>(
    table_addition_fn: &dyn Fn(
        &mut crate::cs::cs_reference::BasicAssembly<F, WitnessGraphCreator<F>>,
    ) -> (),
    circuit_fn: &dyn Fn(
        &mut crate::cs::cs_reference::BasicAssembly<F, WitnessGraphCreator<F>>,
    ) -> (),
) -> Vec<Vec<crate::cs::witness_placer::graph_description::RawExpression<F>>> {
    let graph = dump_wintess_graph_for_unrolled_circuit(table_addition_fn, circuit_fn);
    let (_resolution_order, ssa_forms) = graph.compute_resolution_order();
    ssa_forms
}

const OPCODES_ARE_IN_ROM: bool = true;
