use super::*;

/// Build the GKR [`CircuitSetup`] for the 2^22 unified reduced-machine circuit
/// of the compression layers (`ProofProfile::CompressionFinal`). Same decoder table and
/// table driver as [`unified_reduced_machine_circuit_setup`]; the compiled
/// artifact and the setup are the 2^22 ones.
pub fn unified_reduced_machine_2_22_circuit_setup<A: GoodAllocator + 'static>(
    binary_image: &[u32],
    text_section: &[u32],
    use_caches: bool,
    worker: &Worker,
) -> CircuitSetup<A> {
    let compiled_circuit = ::unified_reduced_machine_2_22::get_circuit(use_caches);
    let table_driver = ::unified_reduced_machine_2_22::get_table_driver(binary_image);
    let trace_len = 1
        << <::unified_reduced_machine_2_22::UnifiedReducedMachineCircuit2_22 as RiscVCycleCircuit<
            BabyBearField,
            true,
        >>::trace_len_log2();
    super::unifier_reduced_machine_circuit::unified_circuit_setup_from_parts::<A>(
        compiled_circuit,
        table_driver,
        trace_len,
        text_section,
        ::unified_reduced_machine_2_22::witness_eval_fn,
        <::unified_reduced_machine_2_22::UnifiedReducedMachineCircuit2_22 as RiscVCycleCircuit<
            BabyBearField,
            true,
        >>::geometry(),
        worker,
    )
}

/// Construct the 2^22 circuit from shared decoder rows.
pub fn unified_reduced_machine_2_22_circuit_setup_from_decoder<A: GoodAllocator + 'static>(
    binary_image: &[u32],
    decoder_table: Vec<Option<cs::gkr_circuits::ExecutorFamilyDecoderData>, A>,
    use_caches: bool,
    worker: &Worker,
) -> CircuitSetup<A> {
    let compiled_circuit = ::unified_reduced_machine_2_22::get_circuit(use_caches);
    let table_driver = ::unified_reduced_machine_2_22::get_table_driver(binary_image);
    let trace_len = 1
        << <::unified_reduced_machine_2_22::UnifiedReducedMachineCircuit2_22 as RiscVCycleCircuit<
            BabyBearField,
            true,
        >>::trace_len_log2();
    super::unifier_reduced_machine_circuit::unified_circuit_setup_from_decoder_parts::<A>(
        compiled_circuit,
        table_driver,
        trace_len,
        decoder_table,
        ::unified_reduced_machine_2_22::witness_eval_fn,
        <::unified_reduced_machine_2_22::UnifiedReducedMachineCircuit2_22 as RiscVCycleCircuit<
            BabyBearField,
            true,
        >>::geometry(),
        worker,
    )
}
