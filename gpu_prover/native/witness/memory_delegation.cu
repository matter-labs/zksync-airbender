#include "layout.cuh"
#include "memory.cuh"
#include "trace_delegation.cuh"

#define MAX_REGISTER_AND_INDIRECT_ACCESSES_COUNT 4

struct DelegationMemorySubtree {
  const DelegationProcessingLayout delegation_processor_layout;
  const u32 register_and_indirect_accesses_count;
  const RegisterAndIndirectAccessDescription register_and_indirect_accesses[MAX_REGISTER_AND_INDIRECT_ACCESSES_COUNT];
};

// #define PRINT_THREAD_IDX 0
// #define PRINT_U16(p, c, v) if (index == PRINT_THREAD_IDX) printf(#p"[%u] <- %u\n", c.offset, v)
// #define PRINT_U32(p, c, v) if (index == PRINT_THREAD_IDX) printf(#p"[%u] <- %u\n"#p"[%u] <- %u\n", c.offset, v & 0xffff, c.offset + 1, v >> 16)
// #define PRINT_TS(p, c, v) if (index == PRINT_THREAD_IDX) printf(#p"[%u] <- %u\n"#p"[%u] <- %u\n", c.offset, v.get_low(), c.offset + 1, v.get_high())

#define PRINT_U16(p, c, v)
#define PRINT_U32(p, c, v)
#define PRINT_TS(p, c, v)

DEVICE_FORCEINLINE void process_delegation_requests_execution(const DelegationMemorySubtree &subtree, const DelegationTrace &trace,
                                                              const matrix_setter<bf, st_modifier::cg> memory, const unsigned index) {
  const auto [multiplicity, abi_mem_offset_high_column, write_timestamp_columns] = subtree.delegation_processor_layout;
  const bool execute_delegation_value = trace.get_witness_from_placeholder<bool>({ExecuteDelegation}, index);
  write_bool_value(multiplicity, execute_delegation_value, memory);
  PRINT_U16(M, multiplicity, execute_delegation_value);
  const u16 abi_mem_offset_high_value = trace.get_witness_from_placeholder<u16>({DelegationABIOffset}, index);
  write_u16_value(abi_mem_offset_high_column, abi_mem_offset_high_value, memory);
  PRINT_U16(M, abi_mem_offset_high_column, abi_mem_offset_high_value);
  const TimestampData delegation_write_timestamp_value = trace.get_witness_from_placeholder<TimestampData>({DelegationWriteTimestamp}, index);
  write_timestamp_value(write_timestamp_columns, delegation_write_timestamp_value, memory);
  PRINT_TS(M, write_timestamp_columns, delegation_write_timestamp_value);
}

template <bool COMPUTE_WITNESS>
DEVICE_FORCEINLINE void process_indirect_memory_accesses(const DelegationMemorySubtree &subtree,
                                                         const RegisterAndIndirectAccessTimestampComparisonAuxVars &aux_vars, const DelegationTrace &trace,
                                                         const matrix_setter<bf, st_modifier::cg> memory, const matrix_setter<bf, st_modifier::cg> witness,
                                                         const unsigned index) {
  const TimestampData write_timestamp =
      COMPUTE_WITNESS ? trace.get_witness_from_placeholder<TimestampData>({DelegationWriteTimestamp}, index) : TimestampData{};
#pragma unroll
  for (u32 i = 0; i < MAX_REGISTER_AND_INDIRECT_ACCESSES_COUNT; ++i) {
    if (i == subtree.register_and_indirect_accesses_count)
      break;
    const auto register_and_indirect_access = &subtree.register_and_indirect_accesses[i];
    const auto [register_tag, register_payload] = register_and_indirect_access->register_access;
    u32 register_index = 0;
    ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM> register_read_timestamp_columns = {};
    ColumnSet<REGISTER_SIZE> register_read_value_columns = {};
    switch (register_tag) {
    case RegisterReadAccess: {
      const auto [index, read_timestamp, read_value] = register_payload.register_access_columns_read_access;
      register_index = index;
      register_read_timestamp_columns = read_timestamp;
      register_read_value_columns = read_value;
      break;
    }
    case RegisterWriteAccess: {
      const auto access = register_payload.register_access_columns_write_access;
      register_index = access.register_index;
      register_read_timestamp_columns = access.read_timestamp;
      register_read_value_columns = access.read_value;
      break;
    }
    }
    const TimestampData register_read_timestamp_value =
        trace.get_witness_from_placeholder<TimestampData>({DelegationRegisterReadTimestamp, register_index}, index);
    write_timestamp_value(register_read_timestamp_columns, register_read_timestamp_value, memory);
    PRINT_TS(M, register_read_timestamp_columns, register_read_timestamp_value);
    const u32 register_read_value = trace.get_witness_from_placeholder<u32>({DelegationRegisterReadValue, register_index}, index);
    write_u32_value(register_read_value_columns, register_read_value, memory);
    PRINT_U32(M, register_read_value_columns, register_read_value);
    if (register_tag == RegisterWriteAccess) {
      const auto register_write_access_columns = register_payload.register_access_columns_write_access.write_value;
      const u32 register_write_value = trace.get_witness_from_placeholder<u32>({DelegationRegisterWriteValue, register_index}, index);
      write_u32_value(register_write_access_columns, register_write_value, memory);
      PRINT_U32(M, register_write_access_columns, register_write_value);
    }
    const auto borrow_set = &aux_vars.aux_borrow_sets[i];
    const auto indirects = borrow_set->indirects;
    if (COMPUTE_WITNESS) {
      const auto borrow_address = borrow_set->borrow;
      const u32 read_timestamp_low = register_read_timestamp_value.get_low();
      const u32 write_timestamp_low = write_timestamp.get_low();
      const bool intermediate_borrow = TimestampData::sub_borrow(read_timestamp_low, write_timestamp_low).y;
      write_bool_value(borrow_address, intermediate_borrow, witness);
      PRINT_U16(W, borrow_address, intermediate_borrow);
    }
    const u32 base_address = register_read_value;
    const auto indirect_accesses_count = register_and_indirect_access->indirect_accesses_count;
    const auto indirect_accesses = register_and_indirect_access->indirect_accesses;
#pragma unroll
    for (u32 access_index = 0; access_index < MAX_INDIRECT_ACCESS_DESCRIPTION_INDIRECT_ACCESSES_COUNT; ++access_index) {
      if (access_index == indirect_accesses_count)
        break;
      const auto [tag, payload] = indirect_accesses[access_index];
      ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM> read_timestamp_columns = {};
      ColumnSet<REGISTER_SIZE> read_value_columns = {};
      ColumnSet<1> address_derivation_carry_bit_column = {};
      switch (tag) {
      case IndirectReadAccess: {
        const auto access = payload.indirect_access_columns_read_access;
        read_timestamp_columns = access.read_timestamp;
        read_value_columns = access.read_value;
        address_derivation_carry_bit_column = access.address_derivation_carry_bit;
        break;
      }
      case IndirectWriteAccess: {
        const auto access = payload.indirect_access_columns_write_access;
        read_timestamp_columns = access.read_timestamp;
        read_value_columns = access.read_value;
        address_derivation_carry_bit_column = access.address_derivation_carry_bit;
        break;
      }
      }
      PlaceholderPayload placeholder_payload{.delegation_payload = DelegationPayload{register_index, access_index}};
      const TimestampData read_timestamp_value =
          trace.get_witness_from_placeholder<TimestampData>({DelegationIndirectReadTimestamp, placeholder_payload}, index);
      write_timestamp_value(read_timestamp_columns, read_timestamp_value, memory);
      PRINT_TS(M, read_timestamp_columns, read_timestamp_value);
      const u32 read_value_value = trace.get_witness_from_placeholder<u32>({DelegationIndirectReadValue, placeholder_payload}, index);
      write_u32_value(read_value_columns, read_value_value, memory);
      PRINT_U32(M, read_value_columns, read_value_value);
      if (tag == IndirectWriteAccess) {
        const u32 write_value_value = trace.get_witness_from_placeholder<u32>({DelegationIndirectWriteValue, placeholder_payload}, index);
        const auto write_value_columns = payload.indirect_access_columns_write_access.write_value;
        write_u32_value(write_value_columns, write_value_value, memory);
        PRINT_U32(M, write_value_columns, write_value_value);
      }
      if (access_index != 0 && address_derivation_carry_bit_column.num_elements != 0) {
        const u32 derived_address = base_address + access_index * sizeof(u32);
        const bool carry_bit = derived_address >> 16 != base_address >> 16;
        write_u16_value(address_derivation_carry_bit_column, carry_bit, memory);
        PRINT_U16(M, address_derivation_carry_bit_column, carry_bit);
      }
      if (!COMPUTE_WITNESS)
        continue;
      const auto borrow_address = indirects[access_index];
      const u32 read_timestamp_low = read_timestamp_value.get_low();
      const u32 write_timestamp_low = write_timestamp.get_low();
      const bool intermediate_borrow = TimestampData::sub_borrow(read_timestamp_low, write_timestamp_low).y;
      write_bool_value(borrow_address, intermediate_borrow, witness);
      PRINT_U16(W, borrow_address, intermediate_borrow);
    }
  }
}

template <bool COMPUTE_WITNESS>
DEVICE_FORCEINLINE void generate(const DelegationMemorySubtree &subtree, const RegisterAndIndirectAccessTimestampComparisonAuxVars &aux_vars,
                                 const DelegationTrace &trace, matrix_setter<bf, st_modifier::cg> memory, matrix_setter<bf, st_modifier::cg> witness,
                                 const unsigned count) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= count)
    return;
  memory.add_row(gid);
  witness.add_row(gid);
  process_delegation_requests_execution(subtree, trace, memory, gid);
  process_indirect_memory_accesses<COMPUTE_WITNESS>(subtree, aux_vars, trace, memory, witness, gid);
}

EXTERN __global__ void generate_memory_values_delegation_kernel(const __grid_constant__ DelegationMemorySubtree subtree,
                                                                const __grid_constant__ DelegationTrace trace, const matrix_setter<bf, st_modifier::cg> memory,
                                                                const unsigned count) {
  generate<false>(subtree, {}, trace, memory, memory, count);
}

EXTERN __global__ void
generate_memory_and_witness_values_delegation_kernel(const __grid_constant__ DelegationMemorySubtree subtree,
                                                     const __grid_constant__ RegisterAndIndirectAccessTimestampComparisonAuxVars aux_vars,
                                                     const __grid_constant__ DelegationTrace trace, const matrix_setter<bf, st_modifier::cg> memory,
                                                     const matrix_setter<bf, st_modifier::cg> witness, const unsigned count) {
  generate<true>(subtree, aux_vars, trace, memory, witness, count);
}
