use cs::definitions::TimestampData;
use fft::GoodAllocator;
use risc_v_simulator::abstractions::tracer::{
    RegisterOrIndirectReadData, RegisterOrIndirectReadWriteData,
    RegisterOrIndirectVariableOffsetData,
};
use std::alloc::Global;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct IndirectAccessLocation {
    pub use_writes: bool,
    pub index: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
#[serde(bound = "\
        Vec<TimestampData, A>: serde::Serialize + serde::de::DeserializeOwned, \
        Vec<RegisterOrIndirectReadData, A>: serde::Serialize + serde::de::DeserializeOwned, \
        Vec<RegisterOrIndirectReadWriteData, A>: serde::Serialize + serde::de::DeserializeOwned, \
        Vec<RegisterOrIndirectVariableOffsetData, A>: serde::Serialize + serde::de::DeserializeOwned\
        ")]
pub struct DelegationWitness<A: GoodAllocator = Global> {
    pub num_requests: usize,
    pub num_register_accesses_per_delegation: usize,
    pub num_indirect_reads_per_delegation: usize,
    pub num_indirect_writes_per_delegation: usize,
    pub num_indirect_access_variable_offsets_per_delegation: usize,
    pub base_register_index: u32,
    pub delegation_type: u16,
    pub indirect_accesses_properties: Vec<Vec<IndirectAccessLocation>>,

    pub write_timestamp: Vec<TimestampData, A>,

    pub register_accesses: Vec<RegisterOrIndirectReadWriteData, A>,
    pub indirect_reads: Vec<RegisterOrIndirectReadData, A>,
    pub indirect_writes: Vec<RegisterOrIndirectReadWriteData, A>,
    pub indirect_offset_variables: Vec<RegisterOrIndirectVariableOffsetData, A>,
}

impl<A: GoodAllocator> DelegationWitness<A> {
    pub fn realloc_to_global(&self) -> DelegationWitness<Global> {
        DelegationWitness {
            num_requests: self.num_requests,
            num_register_accesses_per_delegation: self.num_register_accesses_per_delegation,
            num_indirect_reads_per_delegation: self.num_indirect_reads_per_delegation,
            num_indirect_writes_per_delegation: self.num_indirect_writes_per_delegation,
            num_indirect_access_variable_offsets_per_delegation: self.num_indirect_access_variable_offsets_per_delegation,
            base_register_index: self.base_register_index,
            delegation_type: self.delegation_type,
            indirect_accesses_properties: self.indirect_accesses_properties.clone(),
            write_timestamp: self.write_timestamp[..].to_vec(),
            register_accesses: self.register_accesses[..].to_vec(),
            indirect_reads: self.indirect_reads[..].to_vec(),
            indirect_writes: self.indirect_writes[..].to_vec(),
            indirect_offset_variables: self.indirect_offset_variables[..].to_vec(),
        }
    }

    pub(crate) fn skip_n(&mut self, n: usize) {
            self.write_timestamp = self.write_timestamp[n..].to_vec_in(A::default());
            self.register_accesses = self.register_accesses[(n * self.num_register_accesses_per_delegation)..].to_vec_in(A::default());
            self.indirect_reads = self.indirect_reads[(n * self.num_indirect_reads_per_delegation)..].to_vec_in(A::default());
            self.indirect_writes = self.indirect_writes[(n * self.num_indirect_writes_per_delegation)..].to_vec_in(A::default());
            self.indirect_offset_variables = self.indirect_offset_variables[(n * self.num_indirect_access_variable_offsets_per_delegation)..].to_vec_in(A::default());
    }

    #[inline(always)]
    pub fn assert_consistency(&self) {
        #[cfg(debug_assertions)]
        {
            assert!((self.num_requests + 1).is_power_of_two());
            let baseline = self.write_timestamp.len();

            assert_eq!(
                self.register_accesses.len(),
                baseline * self.num_register_accesses_per_delegation
            );
            assert_eq!(
                self.indirect_reads.len(),
                baseline * self.num_indirect_reads_per_delegation
            );
            assert_eq!(
                self.indirect_writes.len(),
                baseline * self.num_indirect_writes_per_delegation
            );
        }
    }

    pub fn at_capacity(&self) -> bool {
        assert!(self.num_requests >= self.write_timestamp.len());
        self.num_requests == self.write_timestamp.len()
    }

    pub fn is_empty(&self) -> bool {
        self.assert_consistency();
        self.write_timestamp.is_empty()
    }

    pub fn pad(&mut self) {
        todo!();

        // if self.at_capacity() {
        //     return;
        // }
        // self.write_timestamp
        //     .resize(self.num_requests, TimestampData::from_scalar(0));

        // for el in self.register_read_values.iter_mut() {
        //     el.resize(self.num_requests, 0);
        // }
        // for el in self.register_write_values.iter_mut() {
        //     el.resize(self.num_requests, 0);
        // }
        // for el in self.register_read_timestamps.iter_mut() {
        //     el.resize(self.num_requests, TimestampData::from_scalar(0));
        // }

        // for el in self.memory_reads_values.iter_mut() {
        //     el.resize(self.num_requests, 0);
        // }
        // for el in self.memory_write_values.iter_mut() {
        //     el.resize(self.num_requests, 0);
        // }
        // for el in self.memory_read_timestamps.iter_mut() {
        //     el.resize(self.num_requests, TimestampData::from_scalar(0));
        // }
    }
}

// Factory functions below must be consistent with circuits and their ABI

pub fn blake2_with_control_factory_fn<A: GoodAllocator>(
    delegation_type: u16,
    num_requests: usize,
    allocator: A,
) -> DelegationWitness<A> {
    let capacity = num_requests + 1;
    assert!(
        capacity.is_power_of_two(),
        "expected capacity to be power of two, got {}",
        capacity
    );

    let x10_indirect_access_properties: Vec<_> = (0..24)
        .map(|el| IndirectAccessLocation {
            use_writes: true,
            index: el,
        })
        .collect();

    let x11_indirect_access_properties: Vec<_> = (0..16)
        .map(|el| IndirectAccessLocation {
            use_writes: false,
            index: el,
        })
        .collect();

    DelegationWitness {
        num_requests,
        num_register_accesses_per_delegation: 4,
        num_indirect_reads_per_delegation: 16,
        num_indirect_writes_per_delegation: 24,
        num_indirect_access_variable_offsets_per_delegation: 0,
        base_register_index: 10,
        delegation_type,
        indirect_accesses_properties: vec![
            x10_indirect_access_properties,
            x11_indirect_access_properties,
        ], // rest is unreachable

        write_timestamp: Vec::with_capacity_in(capacity, allocator.clone()),

        register_accesses: Vec::with_capacity_in(capacity * 4, allocator.clone()),
        indirect_reads: Vec::with_capacity_in(capacity * 16, allocator.clone()),
        indirect_writes: Vec::with_capacity_in(capacity * 24, allocator.clone()),
        indirect_offset_variables: Vec::with_capacity_in(capacity * 0, allocator.clone()),
    }
}

pub fn bigint_with_control_factory_fn<A: GoodAllocator>(
    delegation_type: u16,
    num_requests: usize,
    allocator: A,
) -> DelegationWitness<A> {
    let capacity = num_requests + 1;
    assert!(
        capacity.is_power_of_two(),
        "expected capacity to be power of two, got {}",
        capacity
    );

    let x10_indirect_access_properties: Vec<_> = (0..8)
        .map(|el| IndirectAccessLocation {
            use_writes: true,
            index: el,
        })
        .collect();

    let x11_indirect_access_properties: Vec<_> = (0..8)
        .map(|el| IndirectAccessLocation {
            use_writes: false,
            index: el,
        })
        .collect();

    DelegationWitness {
        num_requests,
        num_register_accesses_per_delegation: 3,
        num_indirect_reads_per_delegation: 8,
        num_indirect_writes_per_delegation: 8,
        num_indirect_access_variable_offsets_per_delegation: 0,
        base_register_index: 10,
        delegation_type,
        indirect_accesses_properties: vec![
            x10_indirect_access_properties,
            x11_indirect_access_properties,
        ], // rest is unreachable

        write_timestamp: Vec::with_capacity_in(capacity, allocator.clone()),

        register_accesses: Vec::with_capacity_in(capacity * 3, allocator.clone()),
        indirect_reads: Vec::with_capacity_in(capacity * 8, allocator.clone()),
        indirect_writes: Vec::with_capacity_in(capacity * 8, allocator.clone()),
        indirect_offset_variables: Vec::with_capacity_in(capacity * 0, allocator.clone()),
    }
}

pub fn keccak_special5_factory_fn<A: GoodAllocator>(
    delegation_type: u16,
    num_requests: usize,
    allocator: A,
) -> DelegationWitness<A> {
    let capacity = num_requests + 1;
    assert!(
        capacity.is_power_of_two(),
        "expected capacity to be power of two, got {}",
        capacity
    );

    let x11_indirect_access_properties: Vec<_> = (0..12)
        .map(|el| IndirectAccessLocation {
            use_writes: true,
            index: el,
        })
        .collect();

    DelegationWitness {
        num_requests,
        num_register_accesses_per_delegation: 2,
        num_indirect_reads_per_delegation: 0,
        num_indirect_writes_per_delegation: 12,
        num_indirect_access_variable_offsets_per_delegation: 6,
        base_register_index: 10,
        delegation_type,

        // had to add dummy x10 access properties bc he doesn't let me have first register access not be indirect otherwise...
        indirect_accesses_properties: vec![vec![], x11_indirect_access_properties], // rest is unreachable

        write_timestamp: Vec::with_capacity_in(capacity, allocator.clone()),

        register_accesses: Vec::with_capacity_in(capacity * 2, allocator.clone()),
        indirect_reads: Vec::with_capacity_in(capacity * 0, allocator.clone()),
        indirect_writes: Vec::with_capacity_in(capacity * 12, allocator.clone()),
        indirect_offset_variables: Vec::with_capacity_in(capacity * 6, allocator.clone()),
    }
}
