use crate::definitions::LazyInitAndTeardown;
use cs::definitions::TimestampScalar;
use fft::GoodAllocator;
use risc_v_simulator::abstractions::memory::*;
use risc_v_simulator::cycle::status_registers::*;
use std::alloc::Global;

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
#[serde(bound = "Vec<LazyInitAndTeardown, A>: serde::Serialize + serde::de::DeserializeOwned")]
pub struct ShuffleRamSetupAndTeardown<A: GoodAllocator = Global> {
    pub lazy_init_data: Vec<LazyInitAndTeardown, A>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RamShuffleMemStateRecord {
    pub last_access_timestamp: TimestampScalar,
    pub current_value: u32,
}

#[derive(Clone, Debug)]
pub struct VectorMemoryImplWithRom {
    ram: Vec<u32>,
    pub rom_bound: usize,
}

impl VectorMemoryImplWithRom {
    pub fn new_for_byte_size(bytes: usize, rom_bound: usize) -> Self {
        assert!(rom_bound.is_power_of_two());

        assert_eq!(rom_bound % 4, 0);
        assert_eq!(bytes % 4, 0);
        assert!(bytes >= rom_bound);
        let allocation_size = std::cmp::max(rom_bound, bytes);

        Self {
            ram: vec![0u32; allocation_size / 4],
            rom_bound,
        }
    }

    pub fn populate(&mut self, address: u32, value: u32) {
        assert!(address % 4 == 0);
        self.ram[(address / 4) as usize] = value;
    }

    pub fn load_image<'a, B>(&mut self, entry_point: u32, bytes: B)
    where
        B: Iterator<Item = u8>,
    {
        let mut address = entry_point;
        for word in bytes.array_chunks::<4>() {
            self.populate(address, u32::from_le_bytes(word));
            address += 1;
        }
    }

    pub fn get_final_ram_state(self) -> Vec<u32> {
        // NOTE: important: even though we use single allocation for ROM and RAM,
        // we should NOT expose ROM values, so we will instead zero-out
        let Self { ram, rom_bound } = self;

        let mut ram = ram;
        let rom_words = rom_bound / 4;
        ram[..rom_words].fill(0);

        ram
    }
}

impl MemorySource for VectorMemoryImplWithRom {
    #[inline(always)]
    fn get(&self, phys_address: u64, access_type: AccessType, trap: &mut TrapReason) -> u32 {
        if phys_address < self.rom_bound as u64 {
            assert!(access_type == AccessType::Instruction || access_type == AccessType::MemLoad);
            self.ram[(phys_address / 4) as usize]
        } else if ((phys_address / 4) as usize) < self.ram.len() {
            self.ram[(phys_address / 4) as usize]
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
        if phys_address < self.rom_bound as u64 {
            panic!(
                "can not set ROM range: requested write into {}, but ROM bound is {}",
                phys_address, self.rom_bound
            );
        } else if ((phys_address / 4) as usize) < self.ram.len() {
            self.ram[(phys_address / 4) as usize] = value;
        } else {
            match access_type {
                AccessType::Instruction => *trap = TrapReason::InstructionAccessFault,
                AccessType::MemLoad => *trap = TrapReason::LoadAccessFault,
                AccessType::MemStore => *trap = TrapReason::StoreOrAMOAccessFault,
                _ => unreachable!(),
            }
        }
    }

    #[inline(always)]
    fn set_noexcept(&mut self, phys_address: u64, value: u32) {
        debug_assert!(phys_address % 4 == 0);
        if phys_address < self.rom_bound as u64 {
            panic!(
                "can not set ROM range: requested write into {}, but ROM bound is {}",
                phys_address, self.rom_bound
            );
        } else if ((phys_address / 4) as usize) < self.ram.len() {
            self.ram[(phys_address / 4) as usize] = value;
        } else {
            panic!("Out of bound memory access at address 0x{:x}", phys_address);
        }
    }

    #[inline(always)]
    fn get_noexcept(&self, phys_address: u64) -> u32 {
        debug_assert!(phys_address % 4 == 0);
        if ((phys_address / 4) as usize) < self.ram.len() {
            self.ram[(phys_address / 4) as usize]
        } else {
            panic!("Out of bound memory access at address 0x{:x}", phys_address);
        }
    }

    #[inline(always)]
    fn get_opcode_noexcept(&self, phys_address: u64) -> u32 {
        debug_assert!(phys_address % 4 == 0);
        debug_assert!(
            phys_address < self.rom_bound as u64,
            "Out of bound opcode access at address 0x{:x}",
            phys_address
        );
        unsafe { *self.ram.get_unchecked((phys_address / 4) as usize) }

        // if phys_address < self.rom_bound as u64 {
        //     unsafe {
        //         *self.ram.get_unchecked((phys_address / 4) as usize)
        //     }
        // } else {
        //     panic!("Out of bound opcode access at address 0x{:x}", phys_address);
        // }
    }
}
