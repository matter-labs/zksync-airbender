use common_constants::{TimestampData, TimestampScalar};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BatchAccessPartialData {
    Read { read_value: u32 },
    Write { read_value: u32, written_value: u32 },
}

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Hash, Default, serde::Serialize, serde::Deserialize,
)]
#[repr(C)]
pub struct RegisterOrIndirectReadData {
    pub read_value: u32,
    pub timestamp: TimestampData,
}

impl RegisterOrIndirectReadData {
    pub const EMPTY: Self = Self {
        read_value: 0,
        timestamp: TimestampData::EMPTY,
    };
}

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Hash, Default, serde::Serialize, serde::Deserialize,
)]
#[repr(C)]
pub struct RegisterOrIndirectReadWriteData {
    pub read_value: u32,
    pub write_value: u32,
    pub timestamp: TimestampData,
}

impl RegisterOrIndirectReadWriteData {
    pub const EMPTY: Self = Self {
        read_value: 0,
        write_value: 0,
        timestamp: TimestampData::EMPTY,
    };
}

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Hash, Default, serde::Serialize, serde::Deserialize,
)]
#[repr(C)]
pub struct RegisterOrIndirectVariableOffsetData {
    pub variable_offset_value: u16,
}

impl RegisterOrIndirectVariableOffsetData {
    pub const EMPTY: Self = Self {
        variable_offset_value: 0,
    };
}

impl From<u16> for RegisterOrIndirectVariableOffsetData {
    fn from(value: u16) -> Self {
        Self {
            variable_offset_value: value,
        }
    }
}

// In general we need to output decoder immediate output, but it's easier to just re-parse it in circuits,
// so we just output PC and timestamp
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
#[repr(C)]
pub struct TracingDecoderData {
    pub pc: u32,
}

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Hash, Default, serde::Serialize, serde::Deserialize,
)]
#[repr(C)]
pub struct NonMemoryOpcodeTracingData {
    pub initial_pc: u32,
    pub rs1_value: u32,
    pub rs2_value: u32,
    pub rd_old_value: u32,
    pub rd_value: u32,
    pub new_pc: u32,
    pub delegation_type: u16,
}

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Hash, Default, serde::Serialize, serde::Deserialize,
)]
#[repr(C)]
pub struct LoadOpcodeTracingData {
    pub initial_pc: u32,
    pub rs1_value: u32,
    pub aligned_ram_address: u32,
    pub aligned_ram_read_value: u32,
    pub rd_old_value: u32,
    pub rd_value: u32,
}

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Hash, Default, serde::Serialize, serde::Deserialize,
)]
#[repr(C)]
pub struct StoreOpcodeTracingData {
    pub initial_pc: u32,
    pub rs1_value: u32,
    pub aligned_ram_address: u32,
    pub aligned_ram_old_value: u32,
    pub rs2_value: u32,
    pub aligned_ram_write_value: u32,
}

const _: () = const {
    assert!(
        core::mem::size_of::<LoadOpcodeTracingData>()
            == core::mem::size_of::<StoreOpcodeTracingData>()
    );
    assert!(
        core::mem::align_of::<LoadOpcodeTracingData>()
            == core::mem::align_of::<StoreOpcodeTracingData>()
    );

    ()
};

pub const MEM_LOAD_TRACE_DATA_MARKER: u16 = 0;
pub const MEM_STORE_TRACE_DATA_MARKER: u16 = MEM_LOAD_TRACE_DATA_MARKER + 1;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
#[repr(C, u32)]
pub enum UnifiedOpcodeTracingDataWithTimestamp {
    NonMem(NonMemoryOpcodeTracingDataWithTimestamp) = 0,
    Mem(MemoryOpcodeTracingDataWithTimestamp),
}

impl Default for UnifiedOpcodeTracingDataWithTimestamp {
    fn default() -> Self {
        Self::NonMem(NonMemoryOpcodeTracingDataWithTimestamp::default())
    }
}

impl UnifiedOpcodeTracingDataWithTimestamp {
    #[inline(always)]
    pub fn initial_pc(&self) -> u32 {
        match self {
            Self::NonMem(inner) => inner.opcode_data.initial_pc,
            Self::Mem(inner) => inner.opcode_data.initial_pc,
        }
    }

    #[inline(always)]
    pub fn final_pc(&self) -> u32 {
        match self {
            Self::NonMem(inner) => inner.opcode_data.new_pc,
            Self::Mem(inner) => inner.opcode_data.initial_pc.wrapping_add(4),
        }
    }

    #[inline(always)]
    pub fn rs2_is_reg(&self) -> bool {
        match self {
            Self::NonMem(..) => true,
            Self::Mem(inner) => {
                if inner.discr == MEM_LOAD_TRACE_DATA_MARKER {
                    false
                } else {
                    debug_assert_eq!(inner.discr, MEM_STORE_TRACE_DATA_MARKER);
                    true
                }
            }
        }
    }

    #[inline(always)]
    pub fn rd_is_reg(&self) -> bool {
        match self {
            Self::NonMem(..) => true,
            Self::Mem(inner) => {
                if inner.discr == MEM_LOAD_TRACE_DATA_MARKER {
                    true
                } else {
                    debug_assert_eq!(inner.discr, MEM_STORE_TRACE_DATA_MARKER);
                    false
                }
            }
        }
    }

    #[inline(always)]
    pub fn delegation_type(&self) -> u16 {
        match self {
            Self::NonMem(inner) => inner.opcode_data.delegation_type,
            Self::Mem(..) => 0,
        }
    }

    #[inline(always)]
    pub fn rs1_read_value(&self) -> u32 {
        match self {
            Self::NonMem(inner) => inner.opcode_data.rs1_value,
            Self::Mem(inner) => inner.opcode_data.rs1_value,
        }
    }

    #[inline(always)]
    pub fn rs2_or_mem_load_read_value(&self) -> u32 {
        match self {
            Self::NonMem(inner) => inner.opcode_data.rs2_value,
            Self::Mem(inner) => {
                if inner.discr == MEM_LOAD_TRACE_DATA_MARKER {
                    inner.opcode_data.aligned_ram_read_value
                } else {
                    debug_assert_eq!(inner.discr, MEM_STORE_TRACE_DATA_MARKER);
                    unsafe {
                        core::mem::transmute::<_, &StoreOpcodeTracingData>(&inner.opcode_data)
                            .rs2_value
                    }
                }
            }
        }
    }

    #[inline(always)]
    pub fn rd_or_mem_store_read_value(&self) -> u32 {
        match self {
            Self::NonMem(inner) => inner.opcode_data.rd_old_value,
            Self::Mem(inner) => {
                if inner.discr == MEM_LOAD_TRACE_DATA_MARKER {
                    inner.opcode_data.rd_old_value
                } else {
                    debug_assert_eq!(inner.discr, MEM_STORE_TRACE_DATA_MARKER);
                    unsafe {
                        core::mem::transmute::<_, &StoreOpcodeTracingData>(&inner.opcode_data)
                            .aligned_ram_old_value
                    }
                }
            }
        }
    }

    #[inline(always)]
    pub fn rd_or_mem_store_write_value(&self) -> u32 {
        match self {
            Self::NonMem(inner) => inner.opcode_data.rd_value,
            Self::Mem(inner) => {
                if inner.discr == MEM_LOAD_TRACE_DATA_MARKER {
                    inner.opcode_data.rd_value
                } else {
                    debug_assert_eq!(inner.discr, MEM_STORE_TRACE_DATA_MARKER);
                    unsafe {
                        core::mem::transmute::<_, &StoreOpcodeTracingData>(&inner.opcode_data)
                            .aligned_ram_write_value
                    }
                }
            }
        }
    }

    #[inline(always)]
    pub fn rs1_read_timestamp(&self) -> TimestampScalar {
        match self {
            Self::NonMem(inner) => inner.rs1_read_timestamp.as_scalar(),
            Self::Mem(inner) => inner.rs1_read_timestamp.as_scalar(),
        }
    }

    #[inline(always)]
    pub fn rs2_or_mem_load_read_timestamp(&self) -> TimestampScalar {
        match self {
            Self::NonMem(inner) => inner.rs2_read_timestamp.as_scalar(),
            Self::Mem(inner) => inner.rs2_or_ram_read_timestamp.as_scalar(),
        }
    }

    #[inline(always)]
    pub fn rd_or_mem_store_read_timestamp(&self) -> TimestampScalar {
        match self {
            Self::NonMem(inner) => inner.rd_read_timestamp.as_scalar(),
            Self::Mem(inner) => inner.rd_or_ram_read_timestamp.as_scalar(),
        }
    }

    #[inline(always)]
    pub fn cycle_timestamp(&self) -> TimestampScalar {
        match self {
            Self::NonMem(inner) => inner.cycle_timestamp.as_scalar(),
            Self::Mem(inner) => inner.cycle_timestamp.as_scalar(),
        }
    }
}

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Hash, Default, serde::Serialize, serde::Deserialize,
)]
#[repr(C)]
pub struct NonMemoryOpcodeTracingDataWithTimestamp {
    pub opcode_data: NonMemoryOpcodeTracingData,
    pub rs1_read_timestamp: TimestampData,
    pub rs2_read_timestamp: TimestampData,
    pub rd_read_timestamp: TimestampData,
    pub cycle_timestamp: TimestampData,
}

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Hash, Default, serde::Serialize, serde::Deserialize,
)]
#[repr(C)]
pub struct MemoryOpcodeTracingDataWithTimestamp {
    pub opcode_data: LoadOpcodeTracingData,
    pub discr: u16,
    pub rs1_read_timestamp: TimestampData,
    pub rs2_or_ram_read_timestamp: TimestampData,
    pub rd_or_ram_read_timestamp: TimestampData,
    pub cycle_timestamp: TimestampData,
}

impl MemoryOpcodeTracingDataWithTimestamp {
    pub fn initial_pc(&self) -> u32 {
        match self.discr {
            MEM_STORE_TRACE_DATA_MARKER => {
                let as_memstore: &StoreOpcodeTracingData =
                    unsafe { core::mem::transmute(&self.opcode_data) };
                as_memstore.initial_pc
            }
            MEM_LOAD_TRACE_DATA_MARKER => self.opcode_data.initial_pc,
            _ => unreachable!(),
        }
    }

    pub fn as_load_data(&self) -> LoadOpcodeTracingData {
        match self.discr {
            MEM_STORE_TRACE_DATA_MARKER => {
                panic!("is store data");
            }
            MEM_LOAD_TRACE_DATA_MARKER => self.opcode_data,
            _ => unreachable!(),
        }
    }

    pub fn as_store_data(&self) -> StoreOpcodeTracingData {
        match self.discr {
            MEM_STORE_TRACE_DATA_MARKER => unsafe { core::mem::transmute(self.opcode_data) },
            MEM_LOAD_TRACE_DATA_MARKER => {
                panic!("is load data");
            }
            _ => unreachable!(),
        }
    }

    pub fn rs2_or_ram_read_value(&self) -> u32 {
        match self.discr {
            MEM_STORE_TRACE_DATA_MARKER => {
                let as_memstore: &StoreOpcodeTracingData =
                    unsafe { core::mem::transmute(&self.opcode_data) };
                as_memstore.rs2_value
            }
            MEM_LOAD_TRACE_DATA_MARKER => self.opcode_data.aligned_ram_read_value,
            _ => unreachable!(),
        }
    }

    pub fn ram_address(&self) -> u32 {
        match self.discr {
            MEM_STORE_TRACE_DATA_MARKER => {
                let as_memstore: &StoreOpcodeTracingData =
                    unsafe { core::mem::transmute(&self.opcode_data) };
                as_memstore.aligned_ram_address
            }
            MEM_LOAD_TRACE_DATA_MARKER => self.opcode_data.aligned_ram_address,
            _ => unreachable!(),
        }
    }

    pub fn rd_or_ram_read_value(&self) -> u32 {
        match self.discr {
            MEM_STORE_TRACE_DATA_MARKER => self.as_store_data().aligned_ram_old_value,
            MEM_LOAD_TRACE_DATA_MARKER => self.opcode_data.rd_old_value,
            _ => unreachable!(),
        }
    }

    pub fn rd_or_ram_write_value(&self) -> u32 {
        match self.discr {
            MEM_STORE_TRACE_DATA_MARKER => self.as_store_data().aligned_ram_write_value,
            MEM_LOAD_TRACE_DATA_MARKER => self.opcode_data.rd_value,
            _ => unreachable!(),
        }
    }
}
