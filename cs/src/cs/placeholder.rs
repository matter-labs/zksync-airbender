#[repr(u8)]
#[derive(
    Debug, Clone, Copy, Eq, Hash, PartialEq, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
pub enum Placeholder {
    XregsInit,
    XregsFin,
    XregInit(usize),
    XregFin(usize),
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
    ShuffleRamAddress(usize),
    ShuffleRamReadTimestamp(usize),
    ShuffleRamReadValue(usize),
    ShuffleRamIsRegisterAccess(usize),
    ShuffleRamWriteValue(usize),
    ExecuteDelegation,
    DelegationType,
    DelegationABIOffset,
    DelegationWriteTimestamp,
    DelegationMemoryReadValue(usize),
    DelegationMemoryReadTimestamp(usize),
    DelegationMemoryWriteValue(usize),
    DelegationRegisterReadValue(usize), // TODO: change to named field to indicate that we use register index
    DelegationRegisterReadTimestamp(usize),
    DelegationRegisterWriteValue(usize),
    DelegationIndirectReadValue {
        register_index: usize,
        word_index: usize,
    },
    DelegationIndirectReadTimestamp {
        register_index: usize,
        word_index: usize,
    },
    DelegationIndirectWriteValue {
        register_index: usize,
        word_index: usize,
    },
    DelegationNondeterminismAccess(usize),
    DelegationNondeterminismAccessNoSplits(usize),
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
        variable_index: usize,
    },
}

impl std::fmt::Display for Placeholder {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let str_repr = match self {
            Placeholder::XregsInit | Placeholder::XregsFin => String::from("xregs"),
            Placeholder::XregInit(idx) | Placeholder::XregFin(idx) => format!("xreg[{}]", idx),
            Placeholder::Instruction => String::from("insn"),
            Placeholder::MemSlot => String::from("mem_slot"),
            Placeholder::PcInit | Placeholder::PcFin => String::from("pc"),
            Placeholder::ContinueExecutionInit | Placeholder::ContinueExecutionFin => {
                String::from("continue execution")
            }
            Placeholder::StatusInit | Placeholder::StatusFin => String::from("status"),
            Placeholder::IeInit | Placeholder::IeFin => String::from("ie"),
            Placeholder::IpInit | Placeholder::IpFin => String::from("ip"),
            Placeholder::TvecInit | Placeholder::TvecFin => String::from("tvec"),
            Placeholder::ScratchInit | Placeholder::ScratchFin => String::from("scratch"),
            Placeholder::EpcInit | Placeholder::EpcFin => String::from("epc"),
            Placeholder::CauseInit | Placeholder::CauseFin => String::from("cause"),
            Placeholder::TvalInit | Placeholder::TvalFin => String::from("tval"),
            Placeholder::ModeInit | Placeholder::ModeFin => String::from("mode"),
            Placeholder::MemorySaptInit | Placeholder::MemorySaptFin => String::from("sapt"),
            Placeholder::ExternalOracle => String::from("external"),
            Placeholder::Trapped => String::from("trapped"),
            Placeholder::InvalidEncoding => String::from("invalid encoding"),
            Placeholder::FirstRegMem => String::from("first register as memory"),
            Placeholder::SecondRegMem => String::from("second register as memory"),
            Placeholder::MemoryLoadOp => String::from("read set value for memory load"),
            Placeholder::WriteRdReadSetWitness => String::from("read set value for rd update"),
            Placeholder::ShuffleRamReadTimestamp(access_idx) => {
                format!("read timestamp for access index {}", access_idx)
            }
            Placeholder::DelegationMemoryReadValue(access_idx) => {
                format!("read value for delegation, offset {}", access_idx)
            }
            Placeholder::DelegationMemoryReadTimestamp(access_idx) => {
                format!("RAM read timestamp for delegation, offset {}", access_idx)
            }
            Placeholder::DelegationMemoryWriteValue(access_idx) => {
                format!("write value for delegation, offset {}", access_idx)
            }
            Placeholder::DelegationNondeterminismAccess(access_idx) => {
                format!(
                    "non-determinism access for delegation number {}",
                    access_idx
                )
            }
            Placeholder::DelegationNondeterminismAccessNoSplits(access_idx) => {
                format!(
                    "non-determinism access for delegation number {} without splitting to words",
                    access_idx
                )
            }
            _ => unreachable!(),
        };
        write!(f, "{}", str_repr)
    }
}

impl Placeholder {
    pub fn specify_idx(&self, idx: usize) -> Self {
        match self {
            Placeholder::XregsInit => Placeholder::XregInit(idx),
            Placeholder::XregsFin => Placeholder::XregFin(idx),
            _ => unreachable!(),
        }
    }

    pub fn is_initial(&self) -> bool {
        match self {
            Placeholder::XregInit(_)
            | Placeholder::Instruction
            | Placeholder::MemSlot
            | Placeholder::PcInit
            | Placeholder::StatusInit
            | Placeholder::IeInit
            | Placeholder::IpInit
            | Placeholder::TvecInit
            | Placeholder::ScratchInit
            | Placeholder::EpcInit
            | Placeholder::CauseInit
            | Placeholder::TvalInit
            | Placeholder::ModeInit
            | Placeholder::MemorySaptInit
            | Placeholder::ContinueExecutionInit
            | Placeholder::ExternalOracle
            | Placeholder::FirstRegMem
            | Placeholder::SecondRegMem => true,
            _ => false,
        }
    }

    pub fn is_final(&self) -> bool {
        match self {
            Placeholder::XregFin(_)
            | Placeholder::PcFin
            | Placeholder::ContinueExecutionFin
            | Placeholder::StatusFin
            | Placeholder::IeFin
            | Placeholder::IpFin
            | Placeholder::TvecFin
            | Placeholder::ScratchFin
            | Placeholder::EpcFin
            | Placeholder::CauseFin
            | Placeholder::TvalFin
            | Placeholder::ModeFin
            | Placeholder::MemorySaptFin => true,
            _ => false,
        }
    }

    pub fn is_debug(&self) -> bool {
        match self {
            Placeholder::Trapped | Placeholder::InvalidEncoding => true,
            _ => false,
        }
    }
}

impl quote::ToTokens for Placeholder {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        use quote::quote;

        let quote = match self {
            Placeholder::Instruction => {
                quote! { Placeholder::Instruction }
            }
            Placeholder::MemSlot => {
                quote! { Placeholder::MemSlot }
            }
            Placeholder::PcInit => {
                quote! { Placeholder::PcInit }
            }
            Placeholder::FirstRegMem => {
                quote! { Placeholder::FirstRegMem }
            }
            Placeholder::SecondRegMem => {
                quote! { Placeholder::SecondRegMem }
            }
            Placeholder::MemoryLoadOp => {
                quote! { Placeholder::MemoryLoadOp }
            }
            Placeholder::WriteRdReadSetWitness => {
                quote! { Placeholder::WriteRdReadSetWitness }
            }
            Placeholder::ExternalOracle => {
                quote! { Placeholder::ExternalOracle }
            }
            Placeholder::ShuffleRamReadTimestamp(access_idx) => {
                quote! { Placeholder::ShuffleRamReadTimestamp( #access_idx ) }
            }
            Placeholder::DelegationMemoryReadValue(access_idx) => {
                quote! { Placeholder::DelegationMemoryReadValue( #access_idx ) }
            }
            Placeholder::DelegationMemoryReadTimestamp(access_idx) => {
                quote! { Placeholder::DelegationMemoryReadTimestamp( #access_idx ) }
            }
            Placeholder::DelegationMemoryWriteValue(access_idx) => {
                quote! { Placeholder::DelegationMemoryWriteValue( #access_idx ) }
            }
            Placeholder::DelegationNondeterminismAccess(access_idx) => {
                quote! { Placeholder::DelegationNondeterminismAccess( #access_idx ) }
            }
            Placeholder::DelegationNondeterminismAccessNoSplits(access_idx) => {
                quote! { Placeholder::DelegationNondeterminismAccessNoSplits( #access_idx ) }
            }
            Placeholder::DelegationIndirectAccessVariableOffset { variable_index } => {
                quote! { Placeholder::DelegationIndirectAccessVariableOffset( variable_index: #variable_index ) }
            }
            a @ _ => {
                panic!("unsupported {:?}", a);
            }
        };

        tokens.extend(quote);
    }
}
