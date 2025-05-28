use crate::cycle::status_registers::TrapReason;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum AccessType {
    Instruction = 0,
    MemLoad = 1,
    MemStore = 2,
    RegReadFirst = 3,
    RegReadSecond = 4,
    RegWrite = 5,
    None = 6,
}
pub const NUM_DIFFERENT_ACCESS_TYPES: usize = 6;

impl AccessType {
    pub fn is_write_access(&self) -> bool {
        match self {
            AccessType::MemStore | AccessType::RegWrite | AccessType::None => true,
            _ => false,
        }
    }

    pub fn is_read_access(&self) -> bool {
        !self.is_write_access()
    }

    pub fn is_reg_access(&self) -> bool {
        match self {
            AccessType::RegReadFirst | AccessType::RegReadSecond | AccessType::RegWrite => true,
            _ => false,
        }
    }

    pub fn from_idx(idx: u32) -> Self {
        match idx {
            0 => AccessType::Instruction,
            1 => AccessType::MemLoad,
            2 => AccessType::MemStore,
            3 => AccessType::RegReadFirst,
            4 => AccessType::RegReadSecond,
            5 => AccessType::RegWrite,
            _ => AccessType::None,
        }
    }
}

pub trait MemorySource {
    fn set(
        &mut self,
        phys_address: u64,
        value: u32,
        access_type: AccessType,
        trap: &mut TrapReason,
    );
    fn get(&self, phys_address: u64, access_type: AccessType, trap: &mut TrapReason) -> u32;

    #[inline(always)]
    fn set_noexcept(&mut self, phys_address: u64, value: u32) {
        self.set(
            phys_address,
            value,
            AccessType::MemStore,
            &mut TrapReason::NoTrap,
        );
    }

    #[inline(always)]
    fn get_noexcept(&self, phys_address: u64) -> u32 {
        self.get(phys_address, AccessType::MemLoad, &mut TrapReason::NoTrap)
    }

    #[inline(always)]
    fn get_opcode_noexcept(&self, phys_address: u64) -> u32 {
        self.get(
            phys_address,
            AccessType::Instruction,
            &mut TrapReason::NoTrap,
        )
    }
}

pub struct VectorMemoryImpl {
    pub inner: Vec<u32>,
}

impl VectorMemoryImpl {
    pub fn new_for_byte_size(bytes: usize) -> Self {
        assert_eq!(bytes % 4, 0);
        let word_size = bytes / 4;
        Self {
            inner: vec![0u32; word_size],
        }
    }

    pub fn populate(&mut self, address: u32, value: u32) {
        assert!(address % 4 == 0);
        self.inner[(address / 4) as usize] = value;
    }

    pub fn load_image<'a, B>(&mut self, entry_point: u32, bytes: B)
    where
        B: Iterator<Item = u8>,
    {
        for (word, dst) in bytes
            .array_chunks::<4>()
            .zip(self.inner[((entry_point / 4) as usize)..].iter_mut())
        {
            *dst = u32::from_le_bytes(word);
        }
    }
}

impl MemorySource for VectorMemoryImpl {
    #[must_use]
    #[inline(always)]
    fn get(&self, phys_address: u64, access_type: AccessType, trap: &mut TrapReason) -> u32 {
        debug_assert_eq!(phys_address % 4, 0);
        if ((phys_address / 4) as usize) < self.inner.len() {
            self.inner[(phys_address / 4) as usize]
        } else {
            match access_type {
                AccessType::Instruction => *trap = TrapReason::InstructionAccessFault,
                AccessType::MemLoad => *trap = TrapReason::LoadAccessFault,
                AccessType::MemStore => *trap = TrapReason::StoreOrAMOAccessFault,
                _ => unreachable!(),
            }

            0
        }
    }

    #[inline(always)]
    fn set(
        &mut self,
        phys_address: u64,
        value: u32,
        access_type: AccessType,
        trap: &mut TrapReason,
    ) {
        debug_assert_eq!(phys_address % 4, 0);
        if ((phys_address / 4) as usize) < self.inner.len() {
            self.inner[(phys_address / 4) as usize] = value;
        } else {
            match access_type {
                AccessType::Instruction => *trap = TrapReason::InstructionAccessFault,
                AccessType::MemLoad => *trap = TrapReason::LoadAccessFault,
                AccessType::MemStore => *trap = TrapReason::StoreOrAMOAccessFault,
                _ => unreachable!(),
            }
        }
    }
}
