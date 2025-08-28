#pragma once

#include "column.cuh"

using namespace ::airbender::witness::column;

namespace airbender::witness::ram_access {

struct RegisterOnlyAccessAddress {
  ColumnSet<1> register_index;
};

struct RegisterOrRamAccessAddress {
  ColumnSet<1> is_register;
  ColumnSet<REGISTER_SIZE> address;
};

enum ShuffleRamAddressTag : u32 {
  RegisterOnly,
  RegisterOrRam,
};

union ShuffleRamAddressPayload {
  RegisterOnlyAccessAddress register_only_access_address;
  RegisterOrRamAccessAddress register_or_ram_access_address;
};

struct ShuffleRamAddressEnum {
  ShuffleRamAddressTag tag;
  ShuffleRamAddressPayload payload;
};

struct ShuffleRamQueryReadColumns {
  u32 in_cycle_write_index;
  ShuffleRamAddressEnum address;
  ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM> read_timestamp;
  ColumnSet<REGISTER_SIZE> read_value;
};

struct ShuffleRamQueryWriteColumns {
  u32 in_cycle_write_index;
  ShuffleRamAddressEnum address;
  ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM> read_timestamp;
  ColumnSet<REGISTER_SIZE> read_value;
  ColumnSet<REGISTER_SIZE> write_value;
};

enum ShuffleRamQueryColumnsTag : u32 {
  Readonly,
  Write,
};

union ShuffleRamQueryColumnsPayload {
  ShuffleRamQueryReadColumns shuffle_ram_query_read_columns;
  ShuffleRamQueryWriteColumns shuffle_ram_query_write_columns;
};

struct ShuffleRamQueryColumns {
  ShuffleRamQueryColumnsTag tag;
  ShuffleRamQueryColumnsPayload payload;
};

struct ShuffleRamAuxComparisonSet {
  ColumnAddress aux_low_high[2];
  ColumnAddress intermediate_borrow;
  ColumnAddress final_borrow;
};

struct BatchedRamAccessColumnsReadAccess {
  ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM> read_timestamp;
  ColumnSet<REGISTER_SIZE> read_value;
};

struct BatchedRamAccessColumnsWriteAccess {
  ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM> read_timestamp;
  ColumnSet<REGISTER_SIZE> read_value;
  ColumnSet<REGISTER_SIZE> write_value;
};

enum BatchedRamAccessColumnsTag : u32 {
  BatchedRamReadAccess,
  BatchedRamWriteAccess,
};

union BatchedRamAccessColumnsPayload {
  BatchedRamAccessColumnsReadAccess batched_ram_access_columns_read_access;
  BatchedRamAccessColumnsWriteAccess batched_ram_access_columns_write_access;
};

struct BatchedRamAccessColumns {
  BatchedRamAccessColumnsTag tag;
  BatchedRamAccessColumnsPayload payload;
};

struct RegisterAccessColumnsReadAccess {
  u32 register_index;
  ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM> read_timestamp;
  ColumnSet<REGISTER_SIZE> read_value;
};

struct RegisterAccessColumnsWriteAccess {
  u32 register_index;
  ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM> read_timestamp;
  ColumnSet<REGISTER_SIZE> read_value;
  ColumnSet<REGISTER_SIZE> write_value;
};

enum RegisterAccessColumnsTag : u32 {
  RegisterReadAccess,
  RegisterWriteAccess,
};

union RegisterAccessColumnsPayload {
  RegisterAccessColumnsReadAccess register_access_columns_read_access;
  RegisterAccessColumnsWriteAccess register_access_columns_write_access;
};

struct RegisterAccessColumns {
  RegisterAccessColumnsTag tag;
  RegisterAccessColumnsPayload payload;
};

struct IndirectAccessColumnsReadAccess {
  u32 offset;
  ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM> read_timestamp;
  ColumnSet<REGISTER_SIZE> read_value;
  ColumnSet<1> address_derivation_carry_bit;
};

struct IndirectAccessColumnsWriteAccess {
  u32 offset;
  ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM> read_timestamp;
  ColumnSet<REGISTER_SIZE> read_value;
  ColumnSet<REGISTER_SIZE> write_value;
  ColumnSet<1> address_derivation_carry_bit;
};

enum IndirectAccessColumnsTag : u32 {
  IndirectReadAccess,
  IndirectWriteAccess,
};

union IndirectAccessColumnsPayload {
  IndirectAccessColumnsReadAccess indirect_access_columns_read_access;
  IndirectAccessColumnsWriteAccess indirect_access_columns_write_access;
};

struct IndirectAccessColumns {
  IndirectAccessColumnsTag tag;
  IndirectAccessColumnsPayload payload;
};

#define MAX_INDIRECT_ACCESS_DESCRIPTION_INDIRECT_ACCESSES_COUNT 32

struct RegisterAndIndirectAccessDescription {
  RegisterAccessColumns register_access;
  u32 indirect_accesses_count;
  IndirectAccessColumns indirect_accesses[MAX_INDIRECT_ACCESS_DESCRIPTION_INDIRECT_ACCESSES_COUNT];
};

#define MAX_AUX_BORROW_SET_INDIRECTS_COUNT 24

struct AuxBorrowSet {
  ColumnAddress borrow;
  u32 indirects_count;
  ColumnAddress indirects[MAX_AUX_BORROW_SET_INDIRECTS_COUNT];
};

#define MAX_AUX_BORROW_SETS_COUNT 4

struct RegisterAndIndirectAccessTimestampComparisonAuxVars {
  ColumnAddress predicate;
  ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM> write_timestamp_columns;
  ColumnAddress write_timestamp[2];
  u32 aux_borrow_sets_count;
  AuxBorrowSet aux_borrow_sets[MAX_AUX_BORROW_SETS_COUNT];
};

} // namespace airbender::witness::ram_access