use crate::prover::context::ProverContext;
use cs::definitions::TimestampData;
use era_cudart::slice::CudaSlice;
use fft::GoodAllocator;
use prover::risc_v_simulator::abstractions::tracer::{
    RegisterOrIndirectReadData, RegisterOrIndirectReadWriteData,
    RegisterOrIndirectVariableOffsetData,
};
use prover::tracers::delegation::{DelegationWitness, IndirectAccessLocation};
use std::sync::Arc;

pub struct DelegationTraceDevice<C: ProverContext> {
    pub num_requests: usize,
    pub num_register_accesses_per_delegation: usize,
    pub num_indirect_reads_per_delegation: usize,
    pub num_indirect_writes_per_delegation: usize,
    pub num_indirect_access_variable_offsets_per_delegation: usize,
    pub base_register_index: u32,
    pub delegation_type: u16,
    pub indirect_accesses_properties: Vec<Vec<IndirectAccessLocation>>,
    pub write_timestamp: C::Allocation<TimestampData>,
    pub register_accesses: C::Allocation<RegisterOrIndirectReadWriteData>,
    pub indirect_reads: C::Allocation<RegisterOrIndirectReadData>,
    pub indirect_writes: C::Allocation<RegisterOrIndirectReadWriteData>,
    pub indirect_offset_variables: C::Allocation<RegisterOrIndirectVariableOffsetData>,
}

const MAX_INDIRECT_ACCESS_REGISTERS: usize = 2;
const MAX_INDIRECT_ACCESS_WORDS: usize = 24;

#[repr(C)]
pub(crate) struct DelegationTraceRaw {
    pub num_requests: u32,
    pub num_register_accesses_per_delegation: u32,
    pub num_indirect_reads_per_delegation: u32,
    pub num_indirect_writes_per_delegation: u32,
    pub num_indirect_access_variable_offsets_per_delegation: u32,
    pub base_register_index: u32,
    pub delegation_type: u16,
    pub indirect_accesses_properties:
        [[u32; MAX_INDIRECT_ACCESS_WORDS]; MAX_INDIRECT_ACCESS_REGISTERS],
    pub write_timestamp: *const TimestampData,
    pub register_accesses: *const RegisterOrIndirectReadWriteData,
    pub indirect_reads: *const RegisterOrIndirectReadData,
    pub indirect_writes: *const RegisterOrIndirectReadWriteData,
    pub indirect_offset_variables: *const RegisterOrIndirectVariableOffsetData,
}

impl<C: ProverContext> From<&DelegationTraceDevice<C>> for DelegationTraceRaw {
    fn from(value: &DelegationTraceDevice<C>) -> Self {
        Self {
            num_requests: value.write_timestamp.len() as u32,
            num_register_accesses_per_delegation: value.num_register_accesses_per_delegation as u32,
            num_indirect_reads_per_delegation: value.num_indirect_reads_per_delegation as u32,
            num_indirect_writes_per_delegation: value.num_indirect_writes_per_delegation as u32,
            num_indirect_access_variable_offsets_per_delegation: value
                .num_indirect_access_variable_offsets_per_delegation
                as u32,
            base_register_index: value.base_register_index,
            delegation_type: value.delegation_type,
            indirect_accesses_properties: {
                let mut indirect_accesses_properties =
                    [[0; MAX_INDIRECT_ACCESS_WORDS]; MAX_INDIRECT_ACCESS_REGISTERS];
                for (i, access) in value.indirect_accesses_properties.iter().enumerate() {
                    for (j, access_location) in access.iter().enumerate() {
                        indirect_accesses_properties[i][j] = ((access_location.use_writes as u32)
                            << 31)
                            | (access_location.index as u32);
                    }
                }
                indirect_accesses_properties
            },
            write_timestamp: value.write_timestamp.as_ptr(),
            register_accesses: value.register_accesses.as_ptr(),
            indirect_reads: value.indirect_reads.as_ptr(),
            indirect_writes: value.indirect_writes.as_ptr(),
            indirect_offset_variables: value.indirect_offset_variables.as_ptr(),
        }
    }
}

#[derive(Clone)]
pub struct DelegationTraceHost<A: GoodAllocator> {
    pub num_requests: usize,
    pub num_register_accesses_per_delegation: usize,
    pub num_indirect_reads_per_delegation: usize,
    pub num_indirect_writes_per_delegation: usize,
    pub num_indirect_access_variable_offsets_per_delegation: usize,
    pub base_register_index: u32,
    pub delegation_type: u16,
    pub indirect_accesses_properties: Vec<Vec<IndirectAccessLocation>>,
    pub write_timestamp: Arc<Vec<TimestampData, A>>,
    pub register_accesses: Arc<Vec<RegisterOrIndirectReadWriteData, A>>,
    pub indirect_reads: Arc<Vec<RegisterOrIndirectReadData, A>>,
    pub indirect_writes: Arc<Vec<RegisterOrIndirectReadWriteData, A>>,
    pub indirect_offset_variables: Arc<Vec<RegisterOrIndirectVariableOffsetData, A>>,
}

impl<A: GoodAllocator> From<DelegationWitness<A>> for DelegationTraceHost<A> {
    fn from(value: DelegationWitness<A>) -> Self {
        Self {
            num_requests: value.num_requests,
            num_register_accesses_per_delegation: value.num_register_accesses_per_delegation,
            num_indirect_reads_per_delegation: value.num_indirect_reads_per_delegation,
            num_indirect_writes_per_delegation: value.num_indirect_writes_per_delegation,
            num_indirect_access_variable_offsets_per_delegation: value
                .num_indirect_access_variable_offsets_per_delegation,
            base_register_index: value.base_register_index,
            delegation_type: value.delegation_type,
            indirect_accesses_properties: value.indirect_accesses_properties,
            write_timestamp: Arc::new(value.write_timestamp),
            register_accesses: Arc::new(value.register_accesses),
            indirect_reads: Arc::new(value.indirect_reads),
            indirect_writes: Arc::new(value.indirect_writes),
            indirect_offset_variables: Arc::new(value.indirect_offset_variables),
        }
    }
}

impl<A: GoodAllocator> Into<DelegationWitness<A>> for DelegationTraceHost<A> {
    fn into(self) -> DelegationWitness<A> {
        DelegationWitness {
            num_requests: self.num_requests,
            num_register_accesses_per_delegation: self.num_register_accesses_per_delegation,
            num_indirect_reads_per_delegation: self.num_indirect_reads_per_delegation,
            num_indirect_writes_per_delegation: self.num_indirect_writes_per_delegation,
            num_indirect_access_variable_offsets_per_delegation: self
                .num_indirect_access_variable_offsets_per_delegation,
            base_register_index: self.base_register_index,
            delegation_type: self.delegation_type,
            indirect_accesses_properties: self.indirect_accesses_properties,
            write_timestamp: Arc::into_inner(self.write_timestamp).unwrap(),
            register_accesses: Arc::into_inner(self.register_accesses).unwrap(),
            indirect_reads: Arc::into_inner(self.indirect_reads).unwrap(),
            indirect_writes: Arc::into_inner(self.indirect_writes).unwrap(),
            indirect_offset_variables: Arc::into_inner(self.indirect_offset_variables).unwrap(),
        }
    }
}
