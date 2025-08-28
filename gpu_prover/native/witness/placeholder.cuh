#pragma once

#include "common.cuh"

using namespace ::airbender::witness;

namespace airbender::witness::placeholder {

enum PlaceholderTag : u32 {
  XregsInit,
  XregsFin,
  XregInit,
  XregFin,
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
  MemoryLoadOp,
  WriteRdReadSetWitness,
  ShuffleRamLazyInitAddressThis,
  ShuffleRamLazyInitAddressNext,
  ShuffleRamAddress,
  ShuffleRamReadTimestamp,
  ShuffleRamReadValue,
  ShuffleRamIsRegisterAccess,
  ShuffleRamWriteValue,
  ExecuteDelegation,
  DelegationType,
  DelegationABIOffset,
  DelegationWriteTimestamp,
  DelegationMemoryReadValue,
  DelegationMemoryReadTimestamp,
  DelegationMemoryWriteValue,
  DelegationRegisterReadValue,
  DelegationRegisterReadTimestamp,
  DelegationRegisterWriteValue,
  DelegationIndirectReadValue,
  DelegationIndirectReadTimestamp,
  DelegationIndirectWriteValue,
  DelegationNondeterminismAccess,
  DelegationNondeterminismAccessNoSplits,
};

struct DelegationPayload {
  u32 register_index;
  u32 word_index;
};

union PlaceholderPayload {
  u32 u32;
  DelegationPayload delegation_payload;
};

struct Placeholder {
  PlaceholderTag tag;
  PlaceholderPayload payload;
};

} // namespace airbender::witness::placeholder