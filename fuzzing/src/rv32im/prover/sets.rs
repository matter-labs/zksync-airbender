use std::collections::BTreeSet;

use prover::common_constants::TimestampScalar;
use prover::common_constants::INITIAL_TIMESTAMP;
use prover::RamShuffleMemStateRecord;
use riscv_transpiler::vm::State;

use crate::rv32im::prover::INITIAL_PC;
use crate::rv32im::types::CountersT;

pub struct ReadSets {
    read_set: BTreeSet<(u32, TimestampScalar)>,
    memory_read_set: BTreeSet<(bool, u32, TimestampScalar, u32)>,
}

impl ReadSets {
    pub fn empty() -> Self {
        Self {
            read_set: BTreeSet::new(),
            memory_read_set: BTreeSet::new(),
        }
    }

    pub fn new(state: State<CountersT>) -> Self {
        let final_pc = state.pc;
        let final_timestamp = state.timestamp;
        let register_final_state = state.registers.map(|el| RamShuffleMemStateRecord {
            last_access_timestamp: el.timestamp,
            current_value: el.value,
        });
        let mut read_set = BTreeSet::<(u32, TimestampScalar)>::new();

        read_set.insert((final_pc, final_timestamp));

        let mut memory_read_set = BTreeSet::new();

        for (i, reg) in register_final_state.iter().enumerate() {
            memory_read_set.insert((true, i as u32, reg.last_access_timestamp, reg.current_value));
        }
        Self {
            read_set,
            memory_read_set,
        }
    }

    pub fn read_set_mut(&mut self) -> &mut BTreeSet<(u32, TimestampScalar)> {
        &mut self.read_set
    }

    pub fn memory_read_set(&self) -> &BTreeSet<(bool, u32, TimestampScalar, u32)> {
        &self.memory_read_set
    }

    pub fn memory_read_set_mut(&mut self) -> &mut BTreeSet<(bool, u32, TimestampScalar, u32)> {
        &mut self.memory_read_set
    }

    pub fn read_set(&self) -> &BTreeSet<(u32, TimestampScalar)> {
        &self.read_set
    }
}

pub struct WriteSets {
    write_set: BTreeSet<(u32, TimestampScalar)>,
    memory_write_set: BTreeSet<(bool, u32, TimestampScalar, u32)>,
}

impl WriteSets {
    pub fn empty() -> Self {
        Self {
            write_set: BTreeSet::new(),
            memory_write_set: BTreeSet::new(),
        }
    }

    pub fn new() -> Self {
        let mut write_set = BTreeSet::<(u32, TimestampScalar)>::new();

        write_set.insert((INITIAL_PC, INITIAL_TIMESTAMP));

        let mut memory_write_set = BTreeSet::new();

        for i in 0..32 {
            memory_write_set.insert((true, i as u32, 0, 0));
        }
        Self {
            write_set,
            memory_write_set,
        }
    }

    pub fn write_set_mut(&mut self) -> &mut BTreeSet<(u32, TimestampScalar)> {
        &mut self.write_set
    }

    pub fn memory_write_set(&self) -> &BTreeSet<(bool, u32, TimestampScalar, u32)> {
        &self.memory_write_set
    }

    pub fn memory_write_set_mut(&mut self) -> &mut BTreeSet<(bool, u32, TimestampScalar, u32)> {
        &mut self.memory_write_set
    }

    pub fn write_set(&self) -> &BTreeSet<(u32, TimestampScalar)> {
        &self.write_set
    }
}
