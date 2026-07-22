use super::{build_unified_setup_direct, config_logs_for_circuit, CircuitPrecomputations};
use gpu_core::primitives::field::BF;
use gpu_core::primitives::machine_type::MachineType;
use gpu_trace::witness::circuit_type::CircuitType;
use gpu_trace::witness::circuit_type::{
    DelegationCircuitType, UnrolledCircuitType, UnrolledMemoryCircuitType,
    UnrolledNonMemoryCircuitType,
};

use crate::upstream::{
    opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization,
    opcodes_for_reduced_machine, process_binary_into_separate_tables_ext,
    CSExecutorFamilyDecoderData, CpuGKRSetup, GKRCircuitArtifact, SecurityLevel,
};
use worker::Worker;

pub(crate) fn build_unrolled_circuit_precomputation(
    machine_type: MachineType,
    circuit_type: UnrolledCircuitType,
    binary_image: &[u32],
    text_section: &[u32],
    worker: &Worker,
    security_level: SecurityLevel,
) -> CircuitPrecomputations {
    let setup = build_unrolled_setup(
        machine_type,
        circuit_type,
        binary_image,
        text_section,
        worker,
    );
    let (circuit, cpu_setup, decoder_data) = match setup {
        UnrolledSetup::Memory(s) => (s.compiled_circuit, s.setup, s.decoder_data),
        UnrolledSetup::NonMemory(s) => (s.compiled_circuit, s.setup, s.decoder_data),
        UnrolledSetup::Unified(s) => (s.compiled_circuit, s.setup, s.decoder_data),
    };
    let circuit_type = CircuitType::Unrolled(circuit_type);
    let (log_lde_factor, log_rows_per_leaf, log_tree_cap_size) =
        config_logs_for_circuit(circuit_type, security_level);
    CircuitPrecomputations::new(
        circuit_type,
        circuit,
        cpu_setup,
        Some(decoder_data.as_slice()),
        log_lde_factor,
        log_rows_per_leaf,
        log_tree_cap_size,
    )
    .unwrap()
}

struct UnrolledMemorySetup {
    compiled_circuit: GKRCircuitArtifact<BF>,
    setup: CpuGKRSetup<BF>,
    decoder_data: Vec<CSExecutorFamilyDecoderData>,
}

struct UnrolledNonMemorySetup {
    compiled_circuit: GKRCircuitArtifact<BF>,
    setup: CpuGKRSetup<BF>,
    decoder_data: Vec<CSExecutorFamilyDecoderData>,
}

pub(crate) struct UnrolledUnifiedSetup {
    pub(crate) compiled_circuit: GKRCircuitArtifact<BF>,
    pub(crate) setup: CpuGKRSetup<BF>,
    pub(crate) decoder_data: Vec<CSExecutorFamilyDecoderData>,
}

enum UnrolledSetup {
    Memory(UnrolledMemorySetup),
    NonMemory(UnrolledNonMemorySetup),
    Unified(UnrolledUnifiedSetup),
}

/// Wraps a per-family memory-circuit setup's `(compiled_circuit, setup)`
/// pair together with its decoder data, mirroring the shape every
/// `UnrolledCircuitType::Memory` arm in `build_unrolled_setup` produces.
fn wrap_memory_setup(
    compiled_circuit: GKRCircuitArtifact<BF>,
    setup: CpuGKRSetup<BF>,
    decoder_data: Vec<CSExecutorFamilyDecoderData>,
) -> UnrolledSetup {
    UnrolledSetup::Memory(UnrolledMemorySetup {
        compiled_circuit,
        setup,
        decoder_data,
    })
}

/// Non-memory counterpart of [`wrap_memory_setup`]; mirrors every
/// `UnrolledCircuitType::NonMemory` arm in `build_unrolled_setup`.
fn wrap_non_memory_setup(
    compiled_circuit: GKRCircuitArtifact<BF>,
    setup: CpuGKRSetup<BF>,
    decoder_data: Vec<CSExecutorFamilyDecoderData>,
) -> UnrolledSetup {
    UnrolledSetup::NonMemory(UnrolledNonMemorySetup {
        compiled_circuit,
        setup,
        decoder_data,
    })
}

fn build_unrolled_setup(
    machine_type: MachineType,
    circuit_type: UnrolledCircuitType,
    binary_image: &[u32],
    text_section: &[u32],
    worker: &Worker,
) -> UnrolledSetup {
    // The unified circuit is built directly from the unified cs/prover sources
    // (mirroring `UnifiedRiscvCircuitOracle::new` + `build_unified_artifact`),
    // not via the per-family decoder preprocessing below. Short-circuit before
    // any per-family work runs.
    if let UnrolledCircuitType::Unified = circuit_type {
        return UnrolledSetup::Unified(build_unified_setup_direct(
            binary_image,
            text_section,
            worker,
        ));
    }
    use riscv_transpiler::ir::{FullUnsignedMachineDecoderConfig, ReducedMachineDecoderConfig};
    use std::alloc::Global;

    let supported_csrs: Vec<u16> =
        DelegationCircuitType::get_delegation_types_for_machine_type(machine_type)
            .iter()
            .map(DelegationCircuitType::get_delegation_type_id)
            .collect();
    let preprocessing = match machine_type {
        MachineType::Full | MachineType::FullUnsigned => {
            process_binary_into_separate_tables_ext::<
                BF,
                FullUnsignedMachineDecoderConfig,
                true,
                Global,
            >(
                text_section,
                &opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization(),
                common_constants::ROM_WORD_SIZE,
                &supported_csrs,
            )
        }
        MachineType::Reduced => process_binary_into_separate_tables_ext::<
            BF,
            ReducedMachineDecoderConfig,
            true,
            Global,
        >(
            text_section,
            &opcodes_for_reduced_machine(),
            common_constants::ROM_WORD_SIZE,
            &supported_csrs,
        ),
    };
    let family_idx = match circuit_type {
        UnrolledCircuitType::Memory(c) => c.get_family_idx(),
        UnrolledCircuitType::NonMemory(c) => c.get_family_idx(),
        // `Unified` is handled by the early return above; this per-family path is
        // for memory/non-memory circuits only.
        UnrolledCircuitType::InitsAndTeardowns | UnrolledCircuitType::Unified => {
            panic!("build_unrolled_setup is for memory/non-memory circuits only")
        }
    };
    let table_data = preprocessing
        .get(&family_idx)
        .expect("missing decoder data for circuit family")
        .clone();
    let decoder_data_from_table: Vec<CSExecutorFamilyDecoderData> = table_data
        .iter()
        .map(|el| el.as_ref().copied().unwrap_or_default())
        .collect();
    match circuit_type {
        UnrolledCircuitType::Memory(UnrolledMemoryCircuitType::LoadStoreWordOnly) => {
            let s = crate::upstream::load_store_word_only_circuit_setup::<Global>(
                &table_data,
                binary_image,
                true,
                worker,
            );
            wrap_memory_setup(s.compiled_circuit, s.setup, decoder_data_from_table)
        }
        UnrolledCircuitType::Memory(UnrolledMemoryCircuitType::LoadStoreSubwordOnly) => {
            let s = crate::upstream::load_store_subword_only_circuit_setup::<Global>(
                &table_data,
                binary_image,
                true,
                worker,
            );
            wrap_memory_setup(s.compiled_circuit, s.setup, decoder_data_from_table)
        }
        UnrolledCircuitType::NonMemory(UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop) => {
            let s = crate::upstream::add_sub_lui_auipc_mop_circuit_setup::<Global>(
                &table_data,
                true,
                worker,
            );
            wrap_non_memory_setup(s.compiled_circuit, s.setup, decoder_data_from_table)
        }
        UnrolledCircuitType::NonMemory(UnrolledNonMemoryCircuitType::JumpBranchSlt) => {
            let s =
                crate::upstream::jump_branch_slt_circuit_setup::<Global>(&table_data, true, worker);
            wrap_non_memory_setup(s.compiled_circuit, s.setup, decoder_data_from_table)
        }
        UnrolledCircuitType::NonMemory(UnrolledNonMemoryCircuitType::ShiftBinaryCsr) => {
            let s =
                crate::upstream::shift_binary_circuit_setup::<Global>(&table_data, true, worker);
            wrap_non_memory_setup(s.compiled_circuit, s.setup, decoder_data_from_table)
        }
        UnrolledCircuitType::NonMemory(UnrolledNonMemoryCircuitType::MulDivUnsigned) => {
            let s = crate::upstream::mul_div_unsigned_circuit_setup::<Global>(
                &table_data,
                true,
                worker,
            );
            wrap_non_memory_setup(s.compiled_circuit, s.setup, decoder_data_from_table)
        }
        UnrolledCircuitType::InitsAndTeardowns | UnrolledCircuitType::Unified => unreachable!(),
    }
}
