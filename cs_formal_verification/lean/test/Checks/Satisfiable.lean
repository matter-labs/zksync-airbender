-- Each `…SatisfiableClaim` restates the premises of its claim. Applying the claim to the satisfying data
-- type-checks only if they are exactly the claim's premises; the result is the claim's conclusion on that data.
import Human.Trace.Delegation.RVTheorems
import Human.Trace.ZeroTimestamp
import Human.Trace.WritesRangeChecked
import Human.Trace.Workers.Bigint.RVTheorems
import Human.Trace.RVSoundness
import Human.Trace.TeardownBounds
import Human.Trace.Families.AddSub.RVTheorems
import Human.Trace.UnifiedReduced.RVTheorems
import Human.Trace.UnifiedReduced.RVCallerTheorems
import Human.Trace.Workers.Blake2G.RVTheorems
import Human.Trace.Workers.Blake2Round.RVTheorems
import Human.Trace.Workers.Keccak.RVTheorems
import Human.Trace.Workers.KeccakSplit.RVTheorems

open Airbender Trace

namespace Checks.Satisfiable

example (claim : Delegation.RVNativeMemoryExecutionClaim) : Delegation.RVNativeMemoryExecutionSatisfiableClaim →
    ∃ (data : Delegation.MemoryData babyBearModulus) (before : RV.State) (cells : List Cell),
      Delegation.RVMemoryExecution data before cells ∧ data.rows ≠ [] :=
  fun ⟨data, before, cells, hp, accepted, inputs, aligned, rows⟩ =>
    ⟨data, before, cells, claim hp accepted inputs aligned, rows⟩

example (claim : Delegation.RVOperationMemorySoundnessClaim) :
    Delegation.RVOperationMemorySoundnessSatisfiableClaim →
    ∃ data : Delegation.MemoryData babyBearModulus,
      (Delegation.MemorySoundness data ∧ Delegation.WordBounds data) ∧ data.rows ≠ [] :=
  fun ⟨data, _, _, _, accepted, inputs, rows⟩ => ⟨data, claim accepted inputs, rows⟩

example (claim : Delegation.RVMemorySoundnessClaim) : Delegation.RVMemorySoundnessSatisfiableClaim →
    ∃ data : Delegation.MemoryData babyBearModulus, Delegation.MemorySoundness data ∧ data.rows ≠ [] :=
  fun ⟨data, _, _, hp, accepted, inputs, rows⟩ => ⟨data, claim hp accepted inputs, rows⟩

example (claim : Delegation.NoZeroTimestampWritesClaim) : Delegation.NoZeroTimestampWritesSatisfiableClaim →
    ∃ data : Delegation.MemoryData babyBearModulus, ∃ row ∈ data.rows, ∃ port ∈ row.ports,
      2 ≤ (timeOfPair (row.writeToken port).time).value :=
  fun ⟨data, room, high, row, member, port, present⟩ =>
    ⟨data, row, member, port, present, claim room high row member port present⟩

example (claim : Keccak.Split.Native.NoZeroTimestampWritesClaim) :
    Keccak.Split.Native.NoZeroTimestampWritesSatisfiableClaim →
    ∃ data : Keccak.Split.Native.MemoryData babyBearModulus, ∃ row ∈ data.rows, ∃ port ∈ row.ports,
      2 ≤ (timeOfPair (row.writeToken port).time).value :=
  fun ⟨data, room, high, row, member, port, present⟩ =>
    ⟨data, row, member, port, present, claim room high row member port present⟩

example (claim : Delegation.WritesRangeCheckedClaim) : Delegation.WritesRangeCheckedSatisfiableClaim →
    ∃ data : Delegation.MemoryData babyBearModulus, ∃ row ∈ data.rows, row.memorySteps ≠ [] ∧
      ∀ step ∈ row.memorySteps, step.2.word.Bounded :=
  fun ⟨data, _, accepted, tables, rounds, keccak, row, member, steps, reads⟩ =>
    ⟨data, row, member, steps, claim accepted tables rounds keccak row member reads⟩

example (claim : InitsTeardowns.WritesRangeCheckedClaim) : InitsTeardowns.WritesRangeCheckedSatisfiableClaim →
    ∃ w : InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout, ∃ token ∈ w.initTokens,
      token.word.Bounded :=
  fun ⟨w, token, member⟩ => ⟨w, token, member, claim w token member⟩

example (claim : Bigint.Native.RVOperationExecutionClaim) : Bigint.Native.RVOperationExecutionSatisfiableClaim →
    ∃ (data : Delegation.MemoryData babyBearModulus) (before : RV.State) (cells : List Cell),
      Delegation.RVMemoryExecution data before cells ∧ ∃ row ∈ data.rows, row.family = .bigint ∧
        Bigint.Native.ArithmeticEffects row.assignment :=
  fun ⟨data, before, cells, accepted, inputs, aligned, table, row, member, family⟩ =>
    have result := claim accepted inputs aligned table
    ⟨data, before, cells, result.1, row, member, family, result.2.1 row member family⟩

example (claim : RVPooledNativeSoundnessClaim) : RVPooledNativeSoundnessSatisfiableClaim →
    ∃ (trace : PooledTrace babyBearModulus) (initial : RV.State) (cells : List Cell),
      RVRealizes trace initial cells ∧ trace.rows ≠ [] :=
  fun ⟨trace, initial, cells, _, _, inputs, accepted, decoded, rows⟩ =>
    ⟨trace, initial, cells, claim inputs accepted decoded, rows⟩

example (claim : BootRamZeroClaim) : BootRamZeroSatisfiableClaim →
    ∃ (initial : RV.State) (cells : List Cell) (address : BitVec 32),
      Cell.ram address ∈ cells ∧ (Cell.ram address).readRV initial = some 0 :=
  fun ⟨_, initial, cells, _, _, _, inputs, address, member⟩ =>
    ⟨initial, cells, address, member, claim inputs address member⟩

example (claim : NonDeterminism.Pooled.RVNativeSoundnessClaim) :
    NonDeterminism.Pooled.RVNativeSoundnessSatisfiableClaim →
    ∃ (trace : PooledTrace babyBearModulus) (initial : RV.State) (cells : List Cell),
      NonDeterminism.Pooled.RVRealizes trace initial cells ∧ trace.rows ≠ [] :=
  fun ⟨trace, initial, cells, _, _, inputs, accepted, decoded, ports, rows⟩ =>
    ⟨trace, initial, cells, claim inputs accepted decoded ports, rows⟩

example (claim : NoZeroTimestampWritesClaim) : NoZeroTimestampWritesSatisfiableClaim →
    ∃ trace : PooledTrace babyBearModulus, ∃ row ∈ trace.rows, ∃ token ∈ row.writes,
      4 ≤ (timeOfPair token.time).value :=
  fun ⟨trace, accepted, boot, row, member, token, present⟩ =>
    ⟨trace, row, member, token, present, claim accepted boot row member token present⟩

example (claim : WritesRangeCheckedClaim) : WritesRangeCheckedSatisfiableClaim →
    ∃ trace : PooledTrace babyBearModulus, ∃ row ∈ trace.rows, row.memorySteps ≠ [] ∧
      ∀ step ∈ row.memorySteps, step.2.word.Bounded :=
  fun ⟨trace, _, _, _, _, _, table, inputs, accepted, decoded, row, member, steps, reads⟩ =>
    ⟨trace, row, member, steps, claim table inputs accepted decoded row member reads⟩

example (claim : TeardownsBoundedClaim) : TeardownsBoundedSatisfiableClaim →
    ∃ inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout),
      ∃ w ∈ inits, ∃ token ∈ w.teardownTokens, token.word.Bounded :=
  fun ⟨_, _, _, _, inits, _, table, inputs, accepted, decoded, reads, w, present, token, member⟩ =>
    ⟨inits, w, present, token, member, claim table inputs accepted decoded reads w present token member⟩

example (claim : RVAirbenderSoundnessClaim) : RVAirbenderSoundnessSatisfiableClaim →
    ∃ (trace : Data babyBearModulus) (initial : RV.State) (cells : List Cell),
      RVRealizes trace initial cells ∧ trace.rows ≠ [] :=
  fun ⟨trace, initial, cells, _, inputs, accepted, decoded, rows⟩ =>
    ⟨trace, initial, cells, claim inputs accepted decoded, rows⟩

example (claim : RVNativeBootSoundnessClaim) : RVNativeBootSoundnessSatisfiableClaim →
    ∃ (trace : Data babyBearModulus) (initial : RV.State) (cells : List Cell),
      RVRealizes trace initial cells ∧ trace.rows ≠ [] :=
  fun ⟨trace, initial, cells, _, _, inputs, accepted, decoded, rows⟩ =>
    ⟨trace, initial, cells, claim inputs accepted decoded, rows⟩

example (claim : UnifiedReduced.RVExecutionSoundnessClaim) : UnifiedReduced.RVExecutionSoundnessSatisfiableClaim →
    ∃ (trace : UnifiedTrace babyBearModulus) (initial : RV.State) (cells : List Cell),
      RVRealizes trace initial cells ∧ trace.rows ≠ [] :=
  fun ⟨trace, initial, cells, _, _, inputs, accepted, decoded, rows⟩ =>
    ⟨trace, initial, cells, claim inputs accepted decoded, rows⟩

example (claim : UnifiedReduced.BootRamZeroClaim) : UnifiedReduced.BootRamZeroSatisfiableClaim →
    ∃ (initial : RV.State) (cells : List Cell) (address : BitVec 32),
      Cell.ram address ∈ cells ∧ (Cell.ram address).readRV initial = some 0 :=
  fun ⟨_, initial, cells, _, _, inputs, address, member⟩ =>
    ⟨initial, cells, address, member, claim inputs address member⟩

example (claim : UnifiedReduced.NoZeroTimestampWritesClaim) : UnifiedReduced.NoZeroTimestampWritesSatisfiableClaim →
    ∃ trace : UnifiedTrace babyBearModulus, ∃ row ∈ trace.rows, ∃ token ∈ row.writes,
      4 ≤ (timeOfPair token.time).value :=
  fun ⟨trace, accepted, boot, row, member, token, present⟩ =>
    ⟨trace, row, member, token, present, claim accepted boot row member token present⟩

example (claim : UnifiedReduced.WritesRangeCheckedClaim) : UnifiedReduced.WritesRangeCheckedSatisfiableClaim →
    ∃ trace : UnifiedTrace babyBearModulus, ∃ row ∈ trace.rows, row.memorySteps ≠ [] ∧
      ∀ step ∈ row.memorySteps, step.2.word.Bounded :=
  fun ⟨trace, accepted, row, member, steps, reads⟩ => ⟨trace, row, member, steps, claim accepted row member reads⟩

example (claim : UnifiedReduced.TeardownsBoundedClaim) : UnifiedReduced.TeardownsBoundedSatisfiableClaim →
    ∃ inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.unifiedLayout),
      ∃ w ∈ inits, ∃ token ∈ w.teardownTokens, token.word.Bounded :=
  fun ⟨_, _, _, _, inits, inputs, accepted, reads, w, present, token, member⟩ =>
    ⟨inits, w, present, token, member, claim inputs accepted reads w present token member⟩

example (claim : Blake2G.Native.RVOperationExecutionClaim) : Blake2G.Native.RVOperationExecutionSatisfiableClaim →
    ∃ (data : Delegation.MemoryData babyBearModulus) (before : RV.State) (cells : List Cell),
      Delegation.RVMemoryExecution data before cells ∧ ∃ row ∈ data.rows, row.family = .blakeG ∧
        Blake2G.spec (Blake2G.Native.input row.assignment) (Blake2G.Native.output row.assignment) :=
  fun ⟨data, before, cells, _, accepted, inputs, aligned, row, member, family⟩ =>
    have result := claim accepted inputs aligned
    ⟨data, before, cells, result.1, row, member, family, result.2 row member family⟩

example (claim : Keccak.Native.RVOperationExecutionClaim) : Keccak.Native.RVOperationExecutionSatisfiableClaim →
    ∃ (data : Delegation.MemoryData babyBearModulus) (before : RV.State) (cells : List Cell),
      Delegation.RVMemoryExecution data before cells ∧ ∃ row ∈ data.rows, row.family = .keccak ∧
        Keccak.Native.RowEffects row.assignment :=
  fun ⟨data, before, cells, accepted, inputs, aligned, row, member, family⟩ =>
    have result := claim accepted inputs aligned
    ⟨data, before, cells, result.1, row, member, family, result.2 row member family⟩

example (claim : Keccak.Split.Native.RVOperationExecutionClaim) :
    Keccak.Split.Native.RVOperationExecutionSatisfiableClaim →
    ∃ (data : Keccak.Split.Native.MemoryData babyBearModulus) (before : RV.State) (cells : List Cell),
      Keccak.Split.Native.RVMemoryExecution data before cells ∧
        ∃ row ∈ data.rows, Keccak.Split.Native.RowEffects row :=
  fun ⟨data, before, cells, accepted, inputs, aligned, row, member⟩ =>
    have result := claim accepted inputs aligned
    ⟨data, before, cells, result.1, row, member, result.2 row member⟩

example (claim : Keccak.Split.Native.WritesRangeCheckedClaim) :
    Keccak.Split.Native.WritesRangeCheckedSatisfiableClaim →
    ∃ data : Keccak.Split.Native.MemoryData babyBearModulus, ∃ row ∈ data.rows, row.memorySteps ≠ [] ∧
      ∀ step ∈ row.memorySteps, step.2.word.Bounded :=
  fun ⟨data, accepted, active, row, member, steps, reads⟩ =>
    ⟨data, row, member, steps, claim accepted active row member reads⟩

example (claim : Blake2Round.Native.RVOperationExecutionClaim) :
    Blake2Round.Native.RVOperationExecutionSatisfiableClaim →
    ∃ (data : Delegation.MemoryData babyBearModulus) (before : RV.State) (cells : List Cell),
      Delegation.RVMemoryExecution data before cells ∧ ∃ row ∈ data.rows, row.family = .blakeRound ∧
        ∃ round, Blake2Round.Memory.RoundMask row.assignment round ∧
          Blake2Round.Row.spec (Blake2Round.Native.input round row.assignment)
            (Blake2Round.Native.output row.assignment) :=
  fun ⟨data, before, cells, _, accepted, inputs, aligned, row, member, family⟩ =>
    have result := claim accepted inputs aligned
    ⟨data, before, cells, result.1, row, member, family, result.2 row member family⟩

section UnifiedCallers
open UnifiedReduced.Caller

example (claim : RVMixedMemorySoundnessClaim) : RVMixedMemorySoundnessSatisfiableClaim →
    ∃ (data : UnifiedReduced.Caller.RVRequestTrace babyBearModulus) (before : RV.State) (cells : List Cell),
      RVMixedMemoryEffects data before cells ∧ data.callers ≠ [] :=
  fun ⟨data, _, before, _, _, cells, accepted, inputs, callers⟩ =>
    ⟨data, before, cells, claim accepted inputs, callers⟩

example (claim : RVRequestWindowSoundnessClaim) : RVRequestWindowSoundnessSatisfiableClaim →
    ∃ (data : UnifiedReduced.Caller.RVRequestTrace babyBearModulus) (lower upper : Nat),
      Delegation.Caller.RequestWindowBinding data.callers data.workers lower upper ∧ data.callers ≠ [] ∧
        data.workers.windowRows lower upper ≠ [] :=
  fun ⟨data, _, _, lower, upper, checks, inputs, first, last, past, callers, window⟩ =>
    ⟨data, lower, upper, claim checks inputs first last past, callers, window⟩

example (claim : RVMixedWindowSoundnessClaim) : RVMixedWindowSoundnessSatisfiableClaim →
    ∃ (data : UnifiedReduced.Caller.RVRequestTrace babyBearModulus) (before : RV.State) (cells : List Cell) (lower upper : Nat),
      RVMixedWindowExecution data before cells lower upper ∧ data.callers ≠ [] ∧
        data.workers.windowRows lower upper ≠ [] :=
  fun ⟨data, _, before, _, _, cells, lower, upper, accepted, inputs, first, last, past, ordered, callers, window⟩ =>
    ⟨data, before, cells, lower, upper, claim accepted inputs first last past ordered, callers, window⟩

example (claim : RVWindowProjectionSoundnessClaim) : RVWindowProjectionSoundnessSatisfiableClaim →
    ∃ (data : UnifiedReduced.Caller.RVRequestTrace babyBearModulus) (before : RV.State) (cells : List Cell) (lower upper : Nat),
      RVProjectedWindowExecution data before cells lower upper ∧ data.callers ≠ [] ∧
        data.workers.windowRows lower upper ≠ [] :=
  fun ⟨data, before, _, _, cells, lower, upper, accepted, inputs, first, last, past, ordered, callers, window⟩ =>
    ⟨data, before, cells, lower, upper, claim accepted inputs first last past ordered, callers, window⟩

example (claim : RVWindowScheduleSoundnessClaim) : RVWindowScheduleSoundnessSatisfiableClaim →
    ∃ (data : UnifiedReduced.Caller.RVRequestTrace babyBearModulus) (lower upper : Nat),
      RVCallerWindowSchedule data lower upper ∧ data.callers ≠ [] ∧ data.workers.windowRows lower upper ≠ [] :=
  fun ⟨data, _, _, lower, upper, checks, inputs, first, last, past, ordered, after, before, duration, callers,
      window⟩ =>
    ⟨data, lower, upper, claim checks inputs first last past ordered after before duration, callers, window⟩

example (claim : RVMixedWindowProjectionSoundnessClaim) : RVMixedWindowProjectionSoundnessSatisfiableClaim →
    ∃ (data : UnifiedReduced.Caller.RVRequestTrace babyBearModulus) (before : RV.State) (cells : List Cell) (lower upper : Nat),
      RVMixedProjectedWindowExecution data before cells lower upper ∧ data.callers ≠ [] ∧
        data.workers.windowRows lower upper ≠ [] :=
  fun ⟨data, _, before, _, _, cells, lower, upper, accepted, inputs, first, last, past, ordered, after, beforeT,
      duration, callers, window⟩ =>
    ⟨data, before, cells, lower, upper,
      claim accepted inputs first last past ordered after beforeT duration, callers, window⟩

example (claim : RVMixedWindowSequenceSoundnessClaim) : RVMixedWindowSequenceSoundnessSatisfiableClaim →
    ∃ (data : UnifiedReduced.Caller.RVRequestTrace babyBearModulus) (before : RV.State) (cells : List Cell) (cut : Nat) (windows : List (Nat × Nat)),
      RVMixedWindowSequenceExecution data before cells cut windows ∧ data.callers ≠ [] ∧
        ∃ window ∈ windows, data.workers.windowRows window.1 window.2 ≠ [] :=
  fun ⟨data, _, before, _, _, cells, cut, windows, accepted, inputs, first, positive, ordered, callers, window⟩ =>
    ⟨data, before, cells, cut, windows, claim accepted inputs first positive ordered, callers, window⟩

example (claim : RVCallerCyclesSoundnessClaim) : RVCallerCyclesSoundnessSatisfiableClaim →
    ∃ (data : UnifiedReduced.Caller.RVRequestTrace babyBearModulus) (program : List UnifiedReduced.RVProgramEntry) (initial : RV.State) (cells : List Cell),
      RVCallerCycleEffects data program initial cells ∧ data.callers ≠ [] :=
  fun ⟨data, program, initial, _, _, cells, accepted, inputs, started, callers⟩ =>
    ⟨data, program, initial, cells, claim accepted inputs started, callers⟩

end UnifiedCallers

end Checks.Satisfiable
