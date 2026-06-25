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
pub mod reduced_machine_ops;
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

pub fn compile_unified_circuit_state_transition<F: PrimeField>(
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
    let compiled = compiler
        .compile_executor_circuit_assuming_preprocessed_bytecode_with_inits_and_teardowns(
            cs_output,
            max_bytecode_size_in_words,
            1,
            trace_len_log2,
        );

    compiled
}

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

#[cfg(all(test, feature = "picus"))]
mod tests {
    use super::*;
    use crate::cs::cs_reference::BasicAssembly;
    use crate::machine::machine_configurations::create_csr_table_for_delegation;
    use crate::machine::ops::unrolled::add_sub_lui_auipc_mop::{
        add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode,
        add_sub_lui_auipc_mop_table_addition_fn,
    };
    use crate::machine::ops::unrolled::jump_branch_slt::{
        jump_branch_slt_circuit_with_preprocessed_bytecode, jump_branch_slt_table_addition_fn,
    };
    use crate::machine::ops::unrolled::load_store::{
        create_load_store_special_tables, load_store_circuit_with_preprocessed_bytecode,
        load_store_table_addition_fn,
    };
    use crate::machine::ops::unrolled::load_store_subword_only::{
        subword_only_load_store_circuit_with_preprocessed_bytecode,
        subword_only_load_store_table_addition_fn,
    };
    use crate::machine::ops::unrolled::load_store_word_only::{
        create_word_only_load_store_special_tables,
        word_only_load_store_circuit_with_preprocessed_bytecode,
        word_only_load_store_table_addition_fn,
    };
    use crate::machine::ops::unrolled::mul_div::{
        mul_div_circuit_with_preprocessed_bytecode, mul_div_table_addition_fn,
    };
    use crate::machine::ops::unrolled::reduced_machine_ops::{
        create_reduced_machine_special_tables, reduced_machine_circuit_with_preprocessed_bytecode,
        reduced_machine_table_addition_fn,
    };
    use crate::machine::ops::unrolled::shift_binary_csr::{
        shift_binop_csrrw_circuit_with_preprocessed_bytecode, shift_binop_csrrw_table_addition_fn,
    };
    use crate::machine::UNIMP_OPCODE;
    use crate::one_row_compiler::{
        CompiledCircuitArtifact, OneRowCompiler, ProtectedConstraintSnapshot,
    };
    use crate::tables::{LookupWrapper, TableType};
    use field::Mersenne31Field;

    const DUMMY_BYTECODE: &[u32] = &[UNIMP_OPCODE];

    fn compile_unrolled_circuit_state_transition_with_protected_constraints(
        table_addition_fn: &dyn Fn(&mut BasicAssembly<Mersenne31Field>) -> (),
        circuit_fn: &dyn Fn(&mut BasicAssembly<Mersenne31Field>) -> (),
        max_bytecode_size_in_words: usize,
        num_inits_and_teardowns: usize,
        trace_len_log2: usize,
    ) -> (
        CompiledCircuitArtifact<Mersenne31Field>,
        ProtectedConstraintSnapshot<Mersenne31Field>,
    ) {
        let mut cs = BasicAssembly::<Mersenne31Field>::new();
        (table_addition_fn)(&mut cs);
        (circuit_fn)(&mut cs);

        let (cs_output, _) = cs.finalize();

        OneRowCompiler::default()
            .compile_executor_circuit_assuming_preprocessed_bytecode_with_inits_and_teardowns_and_protected_constraints(
                cs_output,
                max_bytecode_size_in_words,
                num_inits_and_teardowns,
                trace_len_log2,
            )
    }

    fn compile_unified_circuit_state_transition_with_protected_constraints(
        table_addition_fn: &dyn Fn(&mut BasicAssembly<Mersenne31Field>) -> (),
        circuit_fn: &dyn Fn(&mut BasicAssembly<Mersenne31Field>) -> (),
        max_bytecode_size_in_words: usize,
        trace_len_log2: usize,
    ) -> (
        CompiledCircuitArtifact<Mersenne31Field>,
        ProtectedConstraintSnapshot<Mersenne31Field>,
    ) {
        let mut cs = BasicAssembly::<Mersenne31Field>::new();
        (table_addition_fn)(&mut cs);
        (circuit_fn)(&mut cs);

        let (cs_output, _) = cs.finalize();

        OneRowCompiler::default()
            .compile_executor_circuit_assuming_preprocessed_bytecode_with_inits_and_teardowns_and_protected_constraints(
                cs_output,
                max_bytecode_size_in_words,
                1,
                trace_len_log2,
            )
    }

    fn assert_all_protected_constraints_are_present(
        artifact: &CompiledCircuitArtifact<Mersenne31Field>,
        protected: &ProtectedConstraintSnapshot<Mersenne31Field>,
    ) {
        for constraint in protected.degree_1_constraints.iter() {
            assert!(
                artifact.degree_1_constraints.contains(constraint),
                "missing protected degree-1 constraint: {:?}",
                constraint
            );
        }
        for constraint in protected.degree_2_constraints.iter() {
            assert!(
                artifact.degree_2_constraints.contains(constraint),
                "missing protected degree-2 constraint: {:?}",
                constraint
            );
        }
    }

    #[test]
    fn unrolled_family_sweep_keeps_all_protected_constraints() {
        let (artifact, protected) =
            compile_unrolled_circuit_state_transition_with_protected_constraints(
                &|cs| add_sub_lui_auipc_mop_table_addition_fn(cs),
                &|cs| add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode(cs),
                1 << 20,
                0,
                24,
            );
        assert_all_protected_constraints_are_present(&artifact, &protected);

        let (artifact, protected) =
            compile_unrolled_circuit_state_transition_with_protected_constraints(
                &|cs| jump_branch_slt_table_addition_fn(cs),
                &|cs| jump_branch_slt_circuit_with_preprocessed_bytecode::<_, _, true>(cs),
                1 << 20,
                0,
                24,
            );
        assert_all_protected_constraints_are_present(&artifact, &protected);

        let csr_table = create_csr_table_for_delegation::<Mersenne31Field>(
            true,
            &[],
            TableType::SpecialCSRProperties.to_table_id(),
        );
        let (artifact, protected) =
            compile_unrolled_circuit_state_transition_with_protected_constraints(
                &|cs| {
                    shift_binop_csrrw_table_addition_fn(cs);
                    cs.add_table_with_content(
                        TableType::SpecialCSRProperties,
                        LookupWrapper::Dimensional3(csr_table.clone()),
                    );
                },
                &|cs| shift_binop_csrrw_circuit_with_preprocessed_bytecode(cs),
                1 << 20,
                0,
                24,
            );
        assert_all_protected_constraints_are_present(&artifact, &protected);

        let (artifact, protected) =
            compile_unrolled_circuit_state_transition_with_protected_constraints(
                &|cs| {
                    load_store_table_addition_fn(cs);
                    for (table_type, table) in create_load_store_special_tables::<
                        _,
                        { common_constants::ROM_SECOND_WORD_BITS },
                    >(DUMMY_BYTECODE)
                    {
                        cs.add_table_with_content(table_type, table);
                    }
                },
                &|cs| {
                    load_store_circuit_with_preprocessed_bytecode::<
                        _,
                        _,
                        { common_constants::ROM_SECOND_WORD_BITS },
                    >(cs)
                },
                1 << 20,
                0,
                24,
            );
        assert_all_protected_constraints_are_present(&artifact, &protected);

        let (artifact, protected) =
            compile_unrolled_circuit_state_transition_with_protected_constraints(
                &|cs| {
                    word_only_load_store_table_addition_fn(cs);
                    for (table_type, table) in create_word_only_load_store_special_tables::<
                        _,
                        { common_constants::ROM_SECOND_WORD_BITS },
                    >(DUMMY_BYTECODE)
                    {
                        cs.add_table_with_content(table_type, table);
                    }
                },
                &|cs| {
                    word_only_load_store_circuit_with_preprocessed_bytecode::<
                        _,
                        _,
                        { common_constants::ROM_SECOND_WORD_BITS },
                    >(cs)
                },
                1 << 20,
                0,
                24,
            );
        assert_all_protected_constraints_are_present(&artifact, &protected);

        let (artifact, protected) =
            compile_unrolled_circuit_state_transition_with_protected_constraints(
                &|cs| {
                    subword_only_load_store_table_addition_fn(cs);
                    for (table_type, table) in create_load_store_special_tables::<
                        _,
                        { common_constants::ROM_SECOND_WORD_BITS },
                    >(DUMMY_BYTECODE)
                    {
                        cs.add_table_with_content(table_type, table);
                    }
                },
                &|cs| {
                    subword_only_load_store_circuit_with_preprocessed_bytecode::<
                        _,
                        _,
                        { common_constants::ROM_SECOND_WORD_BITS },
                    >(cs)
                },
                1 << 20,
                0,
                24,
            );
        assert_all_protected_constraints_are_present(&artifact, &protected);

        let (artifact, protected) =
            compile_unrolled_circuit_state_transition_with_protected_constraints(
                &|cs| mul_div_table_addition_fn(cs),
                &|cs| mul_div_circuit_with_preprocessed_bytecode::<_, _, true>(cs),
                1 << 20,
                0,
                24,
            );
        assert_all_protected_constraints_are_present(&artifact, &protected);

        let (artifact, protected) =
            compile_unrolled_circuit_state_transition_with_protected_constraints(
                &|cs| mul_div_table_addition_fn(cs),
                &|cs| mul_div_circuit_with_preprocessed_bytecode::<_, _, false>(cs),
                1 << 20,
                0,
                24,
            );
        assert_all_protected_constraints_are_present(&artifact, &protected);

        let (artifact, protected) =
            compile_unrolled_circuit_state_transition_with_protected_constraints(
                &|cs| {
                    reduced_machine_table_addition_fn(cs);
                    let extra_tables = create_reduced_machine_special_tables::<
                        _,
                        { common_constants::ROM_SECOND_WORD_BITS },
                    >(
                        DUMMY_BYTECODE,
                        &[
                            common_constants::NON_DETERMINISM_CSR,
                            BLAKE2S_DELEGATION_CSR_REGISTER,
                        ],
                    );
                    for (table_type, table) in extra_tables {
                        cs.add_table_with_content(table_type, table);
                    }
                },
                &|cs| {
                    reduced_machine_circuit_with_preprocessed_bytecode::<
                        _,
                        _,
                        { common_constants::ROM_SECOND_WORD_BITS },
                    >(cs)
                },
                1 << 20,
                1,
                23,
            );
        assert_all_protected_constraints_are_present(&artifact, &protected);

        let (artifact, protected) =
            compile_unified_circuit_state_transition_with_protected_constraints(
                &|cs| {
                    reduced_machine_table_addition_fn(cs);
                    let extra_tables = create_reduced_machine_special_tables::<
                        _,
                        { common_constants::ROM_SECOND_WORD_BITS },
                    >(
                        DUMMY_BYTECODE,
                        &[
                            common_constants::NON_DETERMINISM_CSR,
                            BLAKE2S_DELEGATION_CSR_REGISTER,
                        ],
                    );
                    for (table_type, table) in extra_tables {
                        cs.add_table_with_content(table_type, table);
                    }
                },
                &|cs| {
                    reduced_machine_circuit_with_preprocessed_bytecode::<
                        _,
                        _,
                        { common_constants::ROM_SECOND_WORD_BITS },
                    >(cs)
                },
                1 << 20,
                23,
            );
        assert_all_protected_constraints_are_present(&artifact, &protected);

        let compiler = OneRowCompiler::<Mersenne31Field>::default();
        let _artifact = compiler.compile_init_and_teardown_circuit(6, 24);
    }
}
