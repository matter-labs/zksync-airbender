use gpu_core::allocator::host::ConcurrentStaticHostAllocator;
use gpu_core::primitives::field::BF;
use gpu_core::primitives::machine_type::MachineType;
use gpu_core::primitives::static_host::{alloc_static_pinned_box_uninit, StaticPinnedBox};
use circuit_prover::prover::gkr::setup::GpuGKRSetupHost;
use circuit_prover::prover::ProverContext;
use circuit_prover::witness::circuit_type::CircuitType;
use circuit_prover::witness::circuit_type::UnrolledCircuitType::InitsAndTeardowns;
use circuit_prover::witness::circuit_type::{
    DelegationCircuitType, UnrolledCircuitType, UnrolledMemoryCircuitType,
    UnrolledNonMemoryCircuitType,
};
use circuit_prover::witness::trace_unrolled::ExecutorFamilyDecoderData;

use era_cudart::result::CudaResult;

use crate::upstream::{
    opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization,
    opcodes_for_reduced_machine, process_binary_into_separate_tables_ext,
    CSExecutorFamilyDecoderData, CpuGKRSetup, GKRCircuitArtifact, SecurityLevel,
};
use std::collections::BTreeMap;
use std::sync::{Arc, OnceLock};
use worker::Worker;

/// Lazy GPU-side setup host: the CPU setup and the geometry needed to
/// produce a `GpuGKRSetupHost` are stored here, and the actual
/// `GpuGKRSetupHost::precompute_from_cpu_setup` call (which does GPU LDE +
/// commit + D2H of partial trees and the unified cap) runs on first use
/// inside the GPU worker, against that worker's already-initialized
/// `ProverContext`. Uses a `OnceLock` so concurrent workers race once and
/// the loser drops its Arc instead of installing a duplicate.
///
/// The `Arc` wrapper around `GpuGKRSetupHost` is what subsequent workers
/// clone — every prove() that uses this circuit picks up the same cached
/// pinned-host buffers.
pub(crate) struct LazyGpuGKRSetupHost {
    inner: OnceLock<Arc<GpuGKRSetupHost>>,
    cpu_setup: Arc<CpuGKRSetup<BF>>,
    log_lde_factor: u32,
    log_rows_per_leaf: u32,
    log_tree_cap_size: u32,
}

impl LazyGpuGKRSetupHost {
    pub fn new(
        cpu_setup: Arc<CpuGKRSetup<BF>>,
        log_lde_factor: u32,
        log_rows_per_leaf: u32,
        log_tree_cap_size: u32,
    ) -> Self {
        Self {
            inner: OnceLock::new(),
            cpu_setup,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
        }
    }

    /// First call: builds the host on `context` (one-shot stream sync inside
    /// `precompute_from_cpu_setup`); subsequent calls return the cached Arc.
    /// `OnceLock::get_or_try_init` is atomic: concurrent workers race once and
    /// the loser drops its Arc instead of installing a duplicate.
    ///
    /// Returns `None` when the CPU setup has no columns (e.g.
    /// InitsAndTeardowns has `generic_lookup_tables_width == 0` and no
    /// decoder table). The proof flow already treats `setup_transfer` as
    /// optional, so a column-less circuit simply has no setup to transfer
    /// or commit.
    pub fn get_or_init(&self, context: &ProverContext) -> CudaResult<Option<Arc<GpuGKRSetupHost>>> {
        if self.cpu_setup.hypercube_evals.is_empty() {
            return Ok(None);
        }
        self.inner
            .get_or_try_init(|| {
                Ok(Arc::new(GpuGKRSetupHost::precompute_from_cpu_setup(
                    &self.cpu_setup,
                    self.log_lde_factor,
                    self.log_rows_per_leaf,
                    self.log_tree_cap_size,
                    context,
                )?))
            })
            .map(|arc| Some(Arc::clone(arc)))
    }
}

/// Per-circuit precomputations cached across `prove()` invocations.
/// `setup_host` is a `LazyGpuGKRSetupHost` populated on first GPU-worker
/// use; the decoder table is host-only and built eagerly in this
/// constructor.
#[derive(Clone)]
pub(crate) struct CircuitPrecomputations {
    pub compiled_circuit: Arc<GKRCircuitArtifact<BF>>,
    pub setup_host: Arc<LazyGpuGKRSetupHost>,
    pub decoder_host: Option<Arc<StaticPinnedBox<ExecutorFamilyDecoderData>>>,
}

impl CircuitPrecomputations {
    /// Build the per-circuit precomputations. The GPU-side `GpuGKRSetupHost`
    /// is *not* materialized here — `setup_host.get_or_init(context)` does
    /// that on first use inside a GPU worker.
    pub fn new(
        circuit_type: CircuitType,
        compiled_circuit: GKRCircuitArtifact<BF>,
        cpu_setup: CpuGKRSetup<BF>,
        decoder_table_data: Option<&[CSExecutorFamilyDecoderData]>,
        log_lde_factor: u32,
        log_rows_per_leaf: u32,
        log_tree_cap_size: u32,
    ) -> CudaResult<Self> {
        assert_eq!(
            compiled_circuit.trace_len,
            circuit_type.get_domain_size(),
            "compiled circuit trace_len disagrees with CircuitType geometry for {circuit_type:?}"
        );
        let setup_host = Arc::new(LazyGpuGKRSetupHost::new(
            Arc::new(cpu_setup),
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
        ));
        let decoder_host = match decoder_table_data {
            Some(rows) if !rows.is_empty() => {
                let mut buf =
                    alloc_static_pinned_box_uninit::<ExecutorFamilyDecoderData>(rows.len())?;
                for (slot, src) in buf.iter_mut().zip(rows.iter().copied()) {
                    *slot = src.into();
                }
                Some(Arc::new(buf))
            }
            _ => None,
        };
        Ok(Self {
            compiled_circuit: Arc::new(compiled_circuit),
            setup_host,
            decoder_host,
        })
    }
}

/// Build the binary-independent precomputations: every delegation circuit
/// and inits-and-teardowns. CPU-only — no GPU context needed; the
/// `GpuGKRSetupHost` for each circuit is materialized lazily on first GPU
/// worker use.
///
/// `whir_logs_for_circuit` is invoked per-`CircuitType` and must return
/// `(log_lde_factor, log_rows_per_leaf, log_tree_cap_size)` matching the
/// schedule the GPU worker will use at `prove()` time. Different circuits
/// use different WHIR schedules, so a single global triple is wrong for the
/// shared map.
pub(crate) fn get_common_precomputations<F>(
    whir_logs_for_circuit: F,
    worker: &Worker,
) -> CudaResult<BTreeMap<CircuitType, CircuitPrecomputations>>
where
    F: Fn(CircuitType) -> (u32, u32, u32),
{
    let mut out = BTreeMap::new();
    for delegation_type in DelegationCircuitType::get_all_delegation_types()
        .iter()
        .copied()
    {
        let setup = match delegation_type {
            DelegationCircuitType::BigIntWithControl => {
                crate::upstream::get_bigint_with_control_circuit_setup(true, worker)
            }
            DelegationCircuitType::Blake2WithCompression => {
                crate::upstream::get_blake2_with_compression_circuit_setup(true, worker)
            }
            DelegationCircuitType::Blake2GFunction => {
                crate::upstream::get_blake2_g_function_circuit_setup(true, worker)
            }
            DelegationCircuitType::KeccakSpecial5 => {
                crate::upstream::get_keccak_special5_circuit_setup(true, worker)
            }
        };
        let circuit_type = CircuitType::Delegation(delegation_type);
        let (log_lde_factor, log_rows_per_leaf, log_tree_cap_size) =
            whir_logs_for_circuit(circuit_type);
        let precomp = CircuitPrecomputations::new(
            circuit_type,
            setup.compiled_circuit,
            setup.setup,
            None,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
        )?;
        out.insert(circuit_type, precomp);
    }
    let it_setup = crate::upstream::inits_and_teardowns_circuit_setup::<
        ConcurrentStaticHostAllocator,
    >(true, worker);
    let circuit_type = CircuitType::Unrolled(InitsAndTeardowns);
    let (log_lde_factor, log_rows_per_leaf, log_tree_cap_size) =
        whir_logs_for_circuit(circuit_type);
    let precomp = CircuitPrecomputations::new(
        circuit_type,
        it_setup.compiled_circuit,
        it_setup.setup,
        None,
        log_lde_factor,
        log_rows_per_leaf,
        log_tree_cap_size,
    )?;
    out.insert(circuit_type, precomp);
    Ok(out)
}

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

pub(crate) fn get_common_precomputations_for_all(
    worker: &Worker,
    security_level: SecurityLevel,
) -> BTreeMap<CircuitType, CircuitPrecomputations> {
    get_common_precomputations(
        move |ct| config_logs_for_circuit(ct, security_level),
        worker,
    )
    .unwrap()
}

fn config_logs_for_circuit(
    circuit_type: CircuitType,
    security_level: SecurityLevel,
) -> (u32, u32, u32) {
    let prover_config = circuit_prover::prover::config::prover_config(circuit_type, security_level)
        .expect("ExecutionProverConfiguration validated GPU security level before precomputation");
    (
        prover_config.lde_factor.trailing_zeros(),
        prover_config.base_oracles_values_per_leaf.trailing_zeros(),
        prover_config.cap_size.trailing_zeros(),
    )
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

enum UnrolledSetup {
    Memory(UnrolledMemorySetup),
    NonMemory(UnrolledNonMemorySetup),
}

fn build_unrolled_setup(
    machine_type: MachineType,
    circuit_type: UnrolledCircuitType,
    binary_image: &[u32],
    text_section: &[u32],
    worker: &Worker,
) -> UnrolledSetup {
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
            UnrolledSetup::Memory(UnrolledMemorySetup {
                compiled_circuit: s.compiled_circuit,
                setup: s.setup,
                decoder_data: decoder_data_from_table,
            })
        }
        UnrolledCircuitType::Memory(UnrolledMemoryCircuitType::LoadStoreSubwordOnly) => {
            let s = crate::upstream::load_store_subword_only_circuit_setup::<Global>(
                &table_data,
                binary_image,
                true,
                worker,
            );
            UnrolledSetup::Memory(UnrolledMemorySetup {
                compiled_circuit: s.compiled_circuit,
                setup: s.setup,
                decoder_data: decoder_data_from_table,
            })
        }
        UnrolledCircuitType::NonMemory(UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop) => {
            let s = crate::upstream::add_sub_lui_auipc_mop_circuit_setup::<Global>(
                &table_data,
                true,
                worker,
            );
            UnrolledSetup::NonMemory(UnrolledNonMemorySetup {
                compiled_circuit: s.compiled_circuit,
                setup: s.setup,
                decoder_data: decoder_data_from_table,
            })
        }
        UnrolledCircuitType::NonMemory(UnrolledNonMemoryCircuitType::JumpBranchSlt) => {
            let s =
                crate::upstream::jump_branch_slt_circuit_setup::<Global>(&table_data, true, worker);
            UnrolledSetup::NonMemory(UnrolledNonMemorySetup {
                compiled_circuit: s.compiled_circuit,
                setup: s.setup,
                decoder_data: decoder_data_from_table,
            })
        }
        UnrolledCircuitType::NonMemory(UnrolledNonMemoryCircuitType::ShiftBinaryCsr) => {
            let s =
                crate::upstream::shift_binary_circuit_setup::<Global>(&table_data, true, worker);
            UnrolledSetup::NonMemory(UnrolledNonMemorySetup {
                compiled_circuit: s.compiled_circuit,
                setup: s.setup,
                decoder_data: decoder_data_from_table,
            })
        }
        UnrolledCircuitType::NonMemory(UnrolledNonMemoryCircuitType::MulDivUnsigned) => {
            let s = crate::upstream::mul_div_unsigned_circuit_setup::<Global>(
                &table_data,
                true,
                worker,
            );
            UnrolledSetup::NonMemory(UnrolledNonMemorySetup {
                compiled_circuit: s.compiled_circuit,
                setup: s.setup,
                decoder_data: decoder_data_from_table,
            })
        }
        UnrolledCircuitType::InitsAndTeardowns | UnrolledCircuitType::Unified => unreachable!(),
    }
}
