#[repr(C, u32)]
#[derive(Clone, Copy)]
#[allow(dead_code)]
pub enum Placeholder {
    XregsInit,
    XregsFin,
    XregInit(u32),
    XregFin(u32),
    Instruction,
    MemSlot,
    PcInit,
    PcFin,
    StatusInit,
    StatusFin,
    IeInit,
    IeFin,
    IpInit,
    IpFin,
    TvecInit,
    TvecFin,
    ScratchInit,
    ScratchFin,
    EpcInit,
    EpcFin,
    CauseInit,
    CauseFin,
    TvalInit,
    TvalFin,
    ModeInit,
    ModeFin,
    MemorySaptInit,
    MemorySaptFin,
    ContinueExecutionInit,
    ContinueExecutionFin,
    ExternalOracle,
    Trapped,
    InvalidEncoding,
    FirstRegMem,
    SecondRegMem,
    WriteRegMemReadWitness,
    WriteRegMemWriteValue,
    MemoryLoadOp,
    WriteRdReadSetWitness,
    ShuffleRamLazyInitAddressThis,
    ShuffleRamLazyInitAddressNext,
    ShuffleRamAddress(u32),
    ShuffleRamReadTimestamp(u32),
    ShuffleRamReadValue(u32),
    ShuffleRamIsRegisterAccess(u32),
    ShuffleRamWriteValue(u32),
    ExecuteDelegation,
    DelegationType,
    DelegationABIOffset,
    DelegationWriteTimestamp,
    DelegationMemoryReadValue(u32),
    DelegationMemoryReadTimestamp(u32),
    DelegationMemoryWriteValue(u32),
    DelegationRegisterReadValue(u32),
    DelegationRegisterReadTimestamp(u32),
    DelegationRegisterWriteValue(u32),
    DelegationIndirectReadValue {
        register_index: u32,
        word_index: u32,
    },
    DelegationIndirectReadTimestamp {
        register_index: u32,
        word_index: u32,
    },
    DelegationIndirectWriteValue {
        register_index: u32,
        word_index: u32,
    },
    DelegationNondeterminismAccess(u32),
    DelegationNondeterminismAccessNoSplits(u32),
    ExecuteOpcodeFamilyCycle,
    OpcodeFamilyCycleInitialTimestamp,
    OpcodeFamilyCycleFinalTimestamp,
    RS1Index,
    RS2Index,
    MemLoadAddress,
    RDIndex,
    RDIsZero,
    DecodedImm,
    DecodedFunct3,
    DecodedFunct7,
    DecodedExecutorFamilyMask,
    LoadStoreRamValue,
    MemStoreAddress,
    DelegationIndirectAccessVariableOffset {
        variable_index: u32,
    },
}

impl Default for Placeholder {
    fn default() -> Self {
        Placeholder::XregsInit
    }
}

type CSPlaceholder = cs::cs::placeholder::Placeholder;

impl From<CSPlaceholder> for Placeholder {
    fn from(value: CSPlaceholder) -> Self {
        match value {
            CSPlaceholder::XregsInit => Placeholder::XregsInit,
            CSPlaceholder::XregsFin => Placeholder::XregsFin,
            CSPlaceholder::XregInit(x) => Placeholder::XregInit(x as u32),
            CSPlaceholder::XregFin(x) => Placeholder::XregFin(x as u32),
            CSPlaceholder::Instruction => Placeholder::Instruction,
            CSPlaceholder::MemSlot => Placeholder::MemSlot,
            CSPlaceholder::PcInit => Placeholder::PcInit,
            CSPlaceholder::PcFin => Placeholder::PcFin,
            CSPlaceholder::StatusInit => Placeholder::StatusInit,
            CSPlaceholder::StatusFin => Placeholder::StatusFin,
            CSPlaceholder::IeInit => Placeholder::IeInit,
            CSPlaceholder::IeFin => Placeholder::IeFin,
            CSPlaceholder::IpInit => Placeholder::IpInit,
            CSPlaceholder::IpFin => Placeholder::IpFin,
            CSPlaceholder::TvecInit => Placeholder::TvecInit,
            CSPlaceholder::TvecFin => Placeholder::TvecFin,
            CSPlaceholder::ScratchInit => Placeholder::ScratchInit,
            CSPlaceholder::ScratchFin => Placeholder::ScratchFin,
            CSPlaceholder::EpcInit => Placeholder::EpcInit,
            CSPlaceholder::EpcFin => Placeholder::EpcFin,
            CSPlaceholder::CauseInit => Placeholder::CauseInit,
            CSPlaceholder::CauseFin => Placeholder::CauseFin,
            CSPlaceholder::TvalInit => Placeholder::TvalInit,
            CSPlaceholder::TvalFin => Placeholder::TvalFin,
            CSPlaceholder::ModeInit => Placeholder::ModeInit,
            CSPlaceholder::ModeFin => Placeholder::ModeFin,
            CSPlaceholder::MemorySaptInit => Placeholder::MemorySaptInit,
            CSPlaceholder::MemorySaptFin => Placeholder::MemorySaptFin,
            CSPlaceholder::ContinueExecutionInit => Placeholder::ContinueExecutionInit,
            CSPlaceholder::ContinueExecutionFin => Placeholder::ContinueExecutionFin,
            CSPlaceholder::ExternalOracle => Placeholder::ExternalOracle,
            CSPlaceholder::Trapped => Placeholder::Trapped,
            CSPlaceholder::InvalidEncoding => Placeholder::InvalidEncoding,
            CSPlaceholder::FirstRegMem => Placeholder::FirstRegMem,
            CSPlaceholder::SecondRegMem => Placeholder::SecondRegMem,
            CSPlaceholder::WriteRegMemReadWitness => Placeholder::WriteRegMemReadWitness,
            CSPlaceholder::WriteRegMemWriteValue => Placeholder::WriteRegMemWriteValue,
            CSPlaceholder::MemoryLoadOp => Placeholder::MemoryLoadOp,
            CSPlaceholder::WriteRdReadSetWitness => Placeholder::WriteRdReadSetWitness,
            CSPlaceholder::ShuffleRamLazyInitAddressThis => {
                Placeholder::ShuffleRamLazyInitAddressThis
            }
            CSPlaceholder::ShuffleRamLazyInitAddressNext => {
                Placeholder::ShuffleRamLazyInitAddressNext
            }
            CSPlaceholder::ShuffleRamAddress(x) => Placeholder::ShuffleRamAddress(x as u32),
            CSPlaceholder::ShuffleRamReadTimestamp(x) => {
                Placeholder::ShuffleRamReadTimestamp(x as u32)
            }
            CSPlaceholder::ShuffleRamReadValue(x) => Placeholder::ShuffleRamReadValue(x as u32),
            CSPlaceholder::ShuffleRamIsRegisterAccess(x) => {
                Placeholder::ShuffleRamIsRegisterAccess(x as u32)
            }
            CSPlaceholder::ShuffleRamWriteValue(x) => Placeholder::ShuffleRamWriteValue(x as u32),
            CSPlaceholder::ExecuteDelegation => Placeholder::ExecuteDelegation,
            CSPlaceholder::DelegationType => Placeholder::DelegationType,
            CSPlaceholder::DelegationABIOffset => Placeholder::DelegationABIOffset,
            CSPlaceholder::DelegationWriteTimestamp => Placeholder::DelegationWriteTimestamp,
            CSPlaceholder::DelegationMemoryReadValue(x) => {
                Placeholder::DelegationMemoryReadValue(x as u32)
            }
            CSPlaceholder::DelegationMemoryReadTimestamp(x) => {
                Placeholder::DelegationMemoryReadTimestamp(x as u32)
            }
            CSPlaceholder::DelegationMemoryWriteValue(x) => {
                Placeholder::DelegationMemoryWriteValue(x as u32)
            }
            CSPlaceholder::DelegationRegisterReadValue(x) => {
                Placeholder::DelegationRegisterReadValue(x as u32)
            }
            CSPlaceholder::DelegationRegisterReadTimestamp(x) => {
                Placeholder::DelegationRegisterReadTimestamp(x as u32)
            }
            CSPlaceholder::DelegationRegisterWriteValue(x) => {
                Placeholder::DelegationRegisterWriteValue(x as u32)
            }
            CSPlaceholder::DelegationIndirectReadValue {
                register_index,
                word_index,
            } => Placeholder::DelegationIndirectReadValue {
                register_index: register_index as u32,
                word_index: word_index as u32,
            },
            CSPlaceholder::DelegationIndirectReadTimestamp {
                register_index,
                word_index,
            } => Placeholder::DelegationIndirectReadTimestamp {
                register_index: register_index as u32,
                word_index: word_index as u32,
            },
            CSPlaceholder::DelegationIndirectWriteValue {
                register_index,
                word_index,
            } => Placeholder::DelegationIndirectWriteValue {
                register_index: register_index as u32,
                word_index: word_index as u32,
            },
            CSPlaceholder::DelegationNondeterminismAccess(x) => {
                Placeholder::DelegationNondeterminismAccess(x as u32)
            }
            CSPlaceholder::DelegationNondeterminismAccessNoSplits(x) => {
                Placeholder::DelegationNondeterminismAccessNoSplits(x as u32)
            }
            CSPlaceholder::ExecuteOpcodeFamilyCycle => Placeholder::ExecuteOpcodeFamilyCycle,
            CSPlaceholder::OpcodeFamilyCycleInitialTimestamp => {
                Placeholder::OpcodeFamilyCycleInitialTimestamp
            }
            CSPlaceholder::OpcodeFamilyCycleFinalTimestamp => {
                Placeholder::OpcodeFamilyCycleFinalTimestamp
            }
            CSPlaceholder::RS1Index => Placeholder::RS1Index,
            CSPlaceholder::RS2Index => Placeholder::RS2Index,
            CSPlaceholder::MemLoadAddress => Placeholder::MemLoadAddress,
            CSPlaceholder::RDIndex => Placeholder::RDIndex,
            CSPlaceholder::RDIsZero => Placeholder::RDIsZero,
            CSPlaceholder::DecodedImm => Placeholder::DecodedImm,
            CSPlaceholder::DecodedFunct3 => Placeholder::DecodedFunct3,
            CSPlaceholder::DecodedFunct7 => Placeholder::DecodedFunct7,
            CSPlaceholder::DecodedExecutorFamilyMask => Placeholder::DecodedExecutorFamilyMask,
            CSPlaceholder::LoadStoreRamValue => Placeholder::LoadStoreRamValue,
            CSPlaceholder::MemStoreAddress => Placeholder::MemStoreAddress,
            CSPlaceholder::DelegationIndirectAccessVariableOffset { variable_index } => {
                Placeholder::DelegationIndirectAccessVariableOffset {
                    variable_index: variable_index as u32,
                }
            }
        }
    }
}
