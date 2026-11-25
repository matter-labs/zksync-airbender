use std::collections::HashMap;
use std::sync::{Arc, Mutex};

use riscv_transpiler::vm::SimpleTape;
use type_map::concurrent::TypeMap;

use crate::backend::ExecutionBackend;
use crate::config::SoundnessMode;
use crate::ProofProfile;
use common_constants::rom::RomGeometry;
use execution_prover_model::circuit_type::{CircuitType, UnrolledCircuitType};
use execution_prover_model::MachineType;

/// Specifies the execution mode for the prover.
///
/// - `Unrolled`: per-family circuits (split memory / non-memory / I&T).
/// - `Unified`: the 2^23 reduced-machine unified circuit (single circuit
///   family, `MachineType::Reduced` only, `ProofProfile::Standard` and/or
///   `ProofProfile::Compression`).
/// - `Unified22`: the 2^22 unified circuit of the compression layers
///   (`MachineType::Reduced`, exactly `ProofProfile::CompressionFinal`).
/// - `L1Wrap`: the mode-specific Proth120 L1 wrap (`MachineType::Reduced`, exactly
///   `ProofProfile::L1Wrap`).
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ExecutionKind {
    Unrolled,
    Unified,
    Unified22,
    L1Wrap,
}

impl ExecutionKind {
    /// The circuit every chunk of a unified-style execution is proven in;
    /// `None` for the per-family unrolled execution.
    pub fn unified_circuit_in_mode(self, soundness_mode: SoundnessMode) -> Option<CircuitType> {
        match self {
            Self::Unrolled => None,
            Self::Unified => Some(CircuitType::Unrolled(UnrolledCircuitType::Unified)),
            Self::Unified22 => Some(CircuitType::Unrolled(UnrolledCircuitType::Unified22)),
            Self::L1Wrap => Some(match soundness_mode {
                SoundnessMode::PessimisticConjecture => CircuitType::L1Wrap21,
                SoundnessMode::EthproofsSoundnessCalc => CircuitType::L1Wrap22,
            }),
        }
    }

    pub fn is_unified(self) -> bool {
        matches!(self, Self::Unified | Self::Unified22)
    }

    pub fn is_l1_wrap(self) -> bool {
        matches!(self, Self::L1Wrap)
    }

    /// The ROM geometry the execution's circuits are built for.
    pub fn rom(self, soundness_mode: SoundnessMode) -> RomGeometry {
        self.unified_circuit_in_mode(soundness_mode)
            .map_or(common_constants::rom::REGULAR_ROM, |circuit| circuit.rom())
    }
}

pub(super) struct BinaryHolder<B: ExecutionBackend> {
    pub(super) execution_kind: ExecutionKind,
    pub(super) profiles: Vec<ProofProfile>,
    pub(super) machine_type: MachineType,
    pub(super) binary_image: Arc<Box<[u32]>>,
    pub(super) text_section: Arc<Box<[u32]>>,
    pub(super) cycles_bound: Option<u32>,
    pub(super) jit_cache: Arc<Mutex<TypeMap>>,
    pub(super) instruction_tape: Arc<SimpleTape>,
    /// The BabyBear RISC-V family circuits; empty for `ExecutionKind::L1Wrap`.
    pub(super) precomputations: HashMap<UnrolledCircuitType, B::Precomputations>,
    /// The Proth120 wrap circuit; `Some` for `ExecutionKind::L1Wrap` only.
    pub(super) l1_wrap_precomputations: Option<B::Precomputations>,
}
