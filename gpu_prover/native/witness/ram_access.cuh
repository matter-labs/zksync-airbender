#pragma once

#include "common.cuh"
#include "option.cuh"

using namespace ::airbender::witness;
using namespace ::airbender::witness::option;

namespace airbender::witness::ram_access {

struct RegisterOnlyAccessAddress {
  u32 register_index;
};

enum IsRegisterAddressTag : u32 {
  Is,
  Not,
};

struct IsRegisterAddress {
  IsRegisterAddressTag tag;
  u32 value;
};

struct RegisterOrRamAccessAddress {
  IsRegisterAddress is_register;
  u32 address[REGISTER_SIZE];
};

enum RamAddressTag : u32 {
  RegisterOnly,
  RegisterOrRam,
};

union RamAddressPayload {
  RegisterOnlyAccessAddress register_only_access_address;
  RegisterOrRamAccessAddress register_or_ram_access_address;
};

struct RamAddress {
  RamAddressTag tag;
  RamAddressPayload payload;
};

struct RamReadQuery {
  u32 in_cycle_write_index;
  RamAddress address;
  u32 read_timestamp[NUM_TIMESTAMP_COLUMNS_FOR_RAM];
  u32 read_value[REGISTER_SIZE];
};

struct RamWriteQuery {
  u32 in_cycle_write_index;
  RamAddress address;
  u32 read_timestamp[NUM_TIMESTAMP_COLUMNS_FOR_RAM];
  u32 read_value[REGISTER_SIZE];
  u32 write_value[REGISTER_SIZE];
};

enum RamQueryTag : u32 {
  Readonly,
  Write,
};

union RamQueryPayload {
  RamReadQuery ram_read_query;
  RamWriteQuery ram_write_query;
};

struct RamQuery {
  RamQueryTag tag;
  RamQueryPayload payload;
};

struct RamAuxComparisonSet {
  Address intermediate_borrow;
};

struct RegisterAccessColumnsReadAccess {
  u32 register_index;
  u32 read_timestamp[NUM_TIMESTAMP_COLUMNS_FOR_RAM];
  u32 read_value[REGISTER_SIZE];
};

struct RegisterAccessColumnsWriteAccess {
  u32 register_index;
  u32 read_timestamp[NUM_TIMESTAMP_COLUMNS_FOR_RAM];
  u32 read_value[REGISTER_SIZE];
  u32 write_value[REGISTER_SIZE];
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

struct IndirectAccessVariableDependency {
  u32 offset;
  u32 variable;
  u32 index;
};

struct IndirectAccessReadAccess {
  u32 read_timestamp[NUM_TIMESTAMP_COLUMNS_FOR_RAM];
  u32 read_value[REGISTER_SIZE];
  u32 address_derivation_carry_bit;
  OptionU32::Option<IndirectAccessVariableDependency> variable_dependent;
  u32 offset_constant;
};

struct IndirectAccessWriteAccess {
  u32 read_timestamp[NUM_TIMESTAMP_COLUMNS_FOR_RAM];
  u32 read_value[REGISTER_SIZE];
  u32 write_value[REGISTER_SIZE];
  u32 address_derivation_carry_bit;
  OptionU32::Option<IndirectAccessVariableDependency> variable_dependent;
  u32 offset_constant;
};

enum IndirectAccessTag : u32 {
  IndirectReadAccess,
  IndirectWriteAccess,
};

union IndirectAccessPayload {
  IndirectAccessReadAccess indirect_access_read_access;
  IndirectAccessWriteAccess indirect_access_write_access;
};

struct IndirectAccess {
  IndirectAccessTag tag;
  IndirectAccessPayload payload;
};

#define MAX_INDIRECT_ACCESSES_COUNT 32

struct RegisterAndIndirectAccessDescription {
  RegisterAccessColumns register_access;
  u32 indirect_accesses_count;
  IndirectAccess indirect_accesses[MAX_INDIRECT_ACCESSES_COUNT];
};

#define MAX_AUX_BORROW_SET_INDIRECTS_COUNT 24

struct AuxBorrowSet {
  Address borrow;
  u32 indirects_count;
  Address indirects[MAX_AUX_BORROW_SET_INDIRECTS_COUNT];
};

#define MAX_AUX_BORROW_SETS_COUNT 4

struct RegisterAndIndirectAccessTimestampComparisonAuxVars {
  Address predicate;
  Address write_timestamp_columns[NUM_TIMESTAMP_COLUMNS_FOR_RAM];
  Address write_timestamp[NUM_TIMESTAMP_COLUMNS_FOR_RAM];
  u32 aux_borrow_sets_count;
  AuxBorrowSet aux_borrow_sets[MAX_AUX_BORROW_SETS_COUNT];
};

} // namespace airbender::witness::ram_access