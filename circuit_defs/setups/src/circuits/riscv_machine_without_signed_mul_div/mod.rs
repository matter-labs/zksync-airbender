use super::*;

pub fn get_riscv_without_signed_mul_div_circuit_setup<A: GoodAllocator, B: GoodAllocator>(
    bytecode: &[u32],
    worker: &Worker,
) -> MainCircuitPrecomputations<IMWithoutSignedMulDivIsaConfig, A, B> {
    let delegation_csrs = IMWithoutSignedMulDivIsaConfig::ALLOWED_DELEGATION_CSRS;
    let machine: cs::one_row_compiler::CompiledCircuitArtifact<Mersenne31Field> =
        ::machine_without_signed_mul_div::get_machine(bytecode, delegation_csrs);
    let table_driver =
        ::machine_without_signed_mul_div::get_table_driver(bytecode, delegation_csrs);

    let twiddles: Twiddles<_, A> =
        Twiddles::new(::machine_without_signed_mul_div::DOMAIN_SIZE, &worker);
    let lde_precomputations = LdePrecomputations::new(
        ::machine_without_signed_mul_div::DOMAIN_SIZE,
        ::machine_without_signed_mul_div::LDE_FACTOR,
        ::machine_without_signed_mul_div::LDE_SOURCE_COSETS,
        &worker,
    );
    let setup =
        SetupPrecomputations::<DEFAULT_TRACE_PADDING_MULTIPLE, A, DefaultTreeConstructor>::from_tables_and_trace_len(
            &table_driver,
            ::machine_without_signed_mul_div::DOMAIN_SIZE,
            &machine.setup_layout,
            &twiddles,
            &lde_precomputations,
            ::machine_without_signed_mul_div::LDE_FACTOR,
            ::machine_without_signed_mul_div::TREE_CAP_SIZE,
            &worker,
        );

    MainCircuitPrecomputations {
        compiled_circuit: machine,
        table_driver,
        twiddles,
        lde_precomputations,
        setup,
        witness_eval_fn_for_gpu_tracer:
            ::machine_without_signed_mul_div::witness_eval_fn_for_gpu_tracer,
    }
}
