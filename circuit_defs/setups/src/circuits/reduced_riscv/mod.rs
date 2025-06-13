use super::*;

pub fn get_reduced_riscv_circuit_setup<A: GoodAllocator, B: GoodAllocator>(
    bytecode: &[u32],
    worker: &Worker,
) -> MainCircuitPrecomputations<IWithoutByteAccessIsaConfigWithDelegation, A, B> {
    let delegation_csrs = IWithoutByteAccessIsaConfigWithDelegation::ALLOWED_DELEGATION_CSRS;
    let machine: cs::one_row_compiler::CompiledCircuitArtifact<Mersenne31Field> =
        ::reduced_risc_v_machine::get_machine(bytecode, delegation_csrs);
    let table_driver = ::reduced_risc_v_machine::get_table_driver(bytecode, delegation_csrs);

    let twiddles: Twiddles<_, A> = Twiddles::new(::reduced_risc_v_machine::DOMAIN_SIZE, &worker);
    let lde_precomputations = LdePrecomputations::new(
        ::reduced_risc_v_machine::DOMAIN_SIZE,
        ::reduced_risc_v_machine::LDE_FACTOR,
        ::reduced_risc_v_machine::LDE_SOURCE_COSETS,
        &worker,
    );
    let setup =
        SetupPrecomputations::<DEFAULT_TRACE_PADDING_MULTIPLE, A, DefaultTreeConstructor>::from_tables_and_trace_len(
            &table_driver,
            ::reduced_risc_v_machine::DOMAIN_SIZE,
            &machine.setup_layout,
            &twiddles,
            &lde_precomputations,
            ::reduced_risc_v_machine::LDE_FACTOR,
            ::reduced_risc_v_machine::TREE_CAP_SIZE,
            &worker,
        );

    MainCircuitPrecomputations {
        compiled_circuit: machine,
        table_driver,
        twiddles,
        lde_precomputations,
        setup,
        witness_eval_fn_for_gpu_tracer: ::reduced_risc_v_machine::witness_eval_fn_for_gpu_tracer,
    }
}
