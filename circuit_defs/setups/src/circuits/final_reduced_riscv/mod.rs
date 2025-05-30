use super::*;

pub fn get_final_reduced_riscv_circuit_setup<A: GoodAllocator, B: GoodAllocator>(
    bytecode: &[u32],
    worker: &Worker,
) -> MainCircuitPrecomputations<IWithoutByteAccessIsaConfig, A, B> {
    let delegation_csrs = IWithoutByteAccessIsaConfig::ALLOWED_DELEGATION_CSRS;
    let machine: cs::one_row_compiler::CompiledCircuitArtifact<Mersenne31Field> =
        ::final_reduced_risc_v_machine::get_machine(bytecode, delegation_csrs);
    let table_driver = ::final_reduced_risc_v_machine::get_table_driver(bytecode, delegation_csrs);

    let twiddles: Twiddles<_, A> =
        Twiddles::new(::final_reduced_risc_v_machine::DOMAIN_SIZE, &worker);
    let lde_precomputations = LdePrecomputations::new(
        ::final_reduced_risc_v_machine::DOMAIN_SIZE,
        ::final_reduced_risc_v_machine::LDE_FACTOR,
        ::final_reduced_risc_v_machine::LDE_SOURCE_COSETS,
        &worker,
    );
    let setup =
        SetupPrecomputations::<DEFAULT_TRACE_PADDING_MULTIPLE, A, DefaultTreeConstructor>::from_tables_and_trace_len(
            &table_driver,
            ::final_reduced_risc_v_machine::DOMAIN_SIZE,
            &machine.setup_layout,
            &twiddles,
            &lde_precomputations,
            ::final_reduced_risc_v_machine::LDE_FACTOR,
            ::final_reduced_risc_v_machine::TREE_CAP_SIZE,
            &worker,
        );

    MainCircuitPrecomputations {
        compiled_circuit: machine,
        table_driver,
        twiddles,
        lde_precomputations,
        setup,
        witness_eval_fn_for_gpu_tracer:
            ::final_reduced_risc_v_machine::witness_eval_fn_for_gpu_tracer,
    }
}
