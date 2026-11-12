import Human.Circuits.Blake2Round.Mask
import Human.Circuits.InitsTeardowns.Native.Standalone
import Human.Circuits.InitsTeardowns.Native.Unified
import Human.Helpers.Context.VerifierBoundary.Theorems
import Human.Circuits.AddSub.RVTheorems
import Human.Circuits.JumpBranchSlt.RVTheorems
import Human.Circuits.MulDiv.RVTheorems
import Human.Circuits.ShiftBinop.RVTheorems
import Human.Circuits.SubwordMemory.RVTheorems
import Human.Circuits.WordMemory.RVTheorems
import Human.Circuits.InitsTeardowns.Theorems
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
import Human.Trace.Families.JumpBranchSlt.RVTheorems
import Human.Trace.Families.MulDiv.RVTheorems
import Human.Trace.Families.ShiftBinop.RVTheorems
import Human.Trace.Families.SubwordMemory.RVTheorems
import Human.Circuits.AddSub.RVCallerTheorems
import Human.Trace.Delegation.RVCallerTheorems

open Airbender Trace

namespace Checks.Satisfiable

example (claim : VerifierBoundary.TerminalStateSoundnessClaim) :
    VerifierBoundary.TerminalStateSatisfiableClaim →
    ∃ (terminal : PCState.State babyBearModulus) (statement : VerifierBoundary.Statement),
      terminal = statement.terminal.encode :=
  fun ⟨_, terminal, _, _, statement, matched, binding, _⟩ =>
    ⟨terminal, statement, claim matched binding⟩

example (claim : VerifierBoundary.TerminalBoundSoundnessClaim) :
    VerifierBoundary.TerminalBoundSatisfiableClaim →
    ∃ terminal : PCState.State babyBearModulus, terminal.word.Bounded :=
  fun ⟨_, terminal, _, _, hp, matched, closure, _⟩ => ⟨terminal, claim hp matched closure⟩


example : InitsTeardowns.StandaloneSatisfiableClaim →
    InitsTeardowns.TopBitsChecked (List.range InitsTeardowns.maxTopBit) :=
  fun ⟨_, rfl, checked⟩ => checked

example : InitsTeardowns.UnifiedSatisfiableClaim →
    InitsTeardowns.TopBitsChecked (List.range InitsTeardowns.maxTopBit) :=
  fun ⟨_, rfl, checked⟩ => checked

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

example (claim : RVControlPreparationSoundnessClaim) : RVControlPreparationSoundnessSatisfiableClaim →
    ∃ (data : UnifiedReduced.Caller.RVRequestTrace babyBearModulus) (before : RV.State) (cells : List Cell) (cut : Nat) (register : BitVec 5)
      (literal : ControlLiteral),
      RVPreparedBoundaryExecution data before cells cut register literal ∧ data.callers ≠ [] :=
  fun ⟨data, _, before, _, _, cells, cut, register, literal, accepted, inputs, scope, nonzero, aligned, callers⟩ =>
    ⟨data, before, cells, cut, register, literal, claim accepted inputs scope nonzero aligned, callers⟩

example (claim : RVControlPreparationWindowSoundnessClaim) : RVControlPreparationWindowSoundnessSatisfiableClaim →
    ∃ (data : UnifiedReduced.Caller.RVRequestTrace babyBearModulus) (before : RV.State) (cells : List Cell) (lower upper : Nat) (r s : BitVec 5)
      (a b : ControlLiteral),
      RVPreparedControlWindow data before cells lower upper r a s b ∧ data.callers ≠ [] ∧
        data.workers.windowRows lower upper ≠ [] :=
  fun ⟨data, _, before, _, _, cells, lower, upper, r, s, a, b, accepted, inputs, firstScope, lastScope, rn, sn,
      first, last, ordered, callers, window⟩ =>
    ⟨data, before, cells, lower, upper, r, s, a, b,
      claim accepted inputs firstScope lastScope rn sn first last ordered, callers, window⟩

example (claim : RVProgramWindowScheduleSoundnessClaim) : RVProgramWindowScheduleSoundnessSatisfiableClaim →
    ∃ (data : UnifiedReduced.Caller.RVRequestTrace babyBearModulus) (family : Delegation.Family) (lower upper : Nat),
      RVProgramCallerWindow data family lower upper ∧ data.callers ≠ [] ∧
        data.workers.windowRows lower upper ≠ [] :=
  fun ⟨data, _, _, _, _, family, lower, upper, accepted, publicProgram, ordinary, registry, region, first, last, positive,
      ordered, after, beforeT, callers, window⟩ =>
    ⟨data, family, lower, upper,
      claim accepted publicProgram ordinary registry region first last positive ordered after beforeT, callers, window⟩

example (claim : RVSharedSpanSoundnessClaim) : RVSharedSpanSoundnessSatisfiableClaim →
    ∃ (data : UnifiedReduced.Caller.RVRequestTrace babyBearModulus) (before : RV.State) (cells : List Cell)
      (span : Delegation.Caller.HashSpan), RVSharedSpanEffects data before cells span ∧ data.callers ≠ [] :=
  fun ⟨data, before, _, cells, span, accepted, inputs, callers⟩ =>
    ⟨data, before, cells, span, claim accepted inputs, callers⟩

example (claim : RVRequestHashWindowSoundnessClaim) : RVRequestHashWindowSoundnessSatisfiableClaim →
    ∃ (data : UnifiedReduced.Caller.RVRequestTrace babyBearModulus) (before : RV.State) (cells : List Cell)
      (span : Delegation.Caller.HashSpan) (lower upper : Nat),
      span.RVRequestWindowResult data.callers data.workers before cells lower upper ∧ data.callers ≠ [] ∧
        data.workers.windowRows lower upper ≠ [] :=
  fun ⟨data, before, _, cells, span, lower, upper, checks, workers, program, inputs, aligned, first, last, past,
      callers, window⟩ =>
    ⟨data, before, cells, span, lower, upper, claim checks workers program inputs aligned first last past, callers,
      window⟩

example (claim : RVJointHashWindowSoundnessClaim) : RVJointHashWindowSoundnessSatisfiableClaim →
    ∃ (data : UnifiedReduced.Caller.RVRequestTrace babyBearModulus) (before : RV.State) (cells : List Cell)
      (span : Delegation.Caller.HashSpan) (lower upper : Nat),
      RVJointHashWindowResult data before cells span lower upper ∧ data.callers ≠ [] ∧
        data.workers.windowRows lower upper ≠ [] :=
  fun ⟨data, before, _, cells, span, lower, upper, accepted, inputs, first, last, positive, ordered, callers,
      window⟩ =>
    ⟨data, before, cells, span, lower, upper, claim accepted inputs first last positive ordered, callers, window⟩

example (claim : RVPreparedHashWindowSoundnessClaim) : RVPreparedHashWindowSoundnessSatisfiableClaim →
    ∃ (data : UnifiedReduced.Caller.RVRequestTrace babyBearModulus) (before : RV.State) (cells : List Cell)
      (span : Delegation.Caller.HashSpan) (lower upper : Nat),
      RVJointHashWindowResult data before cells span lower upper ∧ data.callers ≠ [] ∧
        data.workers.windowRows lower upper ≠ [] :=
  fun ⟨data, before, _, _, cells, _, span, lower, upper, accepted, inputs, first, last, callers, window⟩ =>
    ⟨data, before, cells, span, lower, upper, claim accepted inputs first last, callers, window⟩

example (claim : RVPreparedHashSequenceSoundnessClaim) : RVPreparedHashSequenceSoundnessSatisfiableClaim →
    ∃ (data : UnifiedReduced.Caller.RVRequestTrace babyBearModulus) (before : RV.State) (cells : List Cell)
      (first : HashWindow) (rest : List HashWindow),
      RVPreparedHashSequenceResult data before cells first rest ∧ data.callers ≠ [] ∧
        data.workers.windowRows first.lower first.upper ≠ [] :=
  fun ⟨data, before, _, _, cells, _, first, rest, accepted, firstInputs, restInputs, ordered, callers, window⟩ =>
    ⟨data, before, cells, first, rest, claim accepted firstInputs restInputs ordered, callers, window⟩

example (claim : RVPreparedProtocolSequenceSoundnessClaim) : RVPreparedProtocolSequenceSoundnessSatisfiableClaim →
    ∃ (data : UnifiedReduced.Caller.RVRequestTrace babyBearModulus) (before : RV.State) (cells : List Cell)
      (first : HashWindow) (rest : List HashWindow),
      RVPreparedHashSequenceResult data before cells first rest ∧ data.callers ≠ [] ∧
        data.workers.windowRows first.lower first.upper ≠ [] :=
  fun ⟨data, before, _, _, cells, _, _, first, rest, accepted, inputs, scopes, ordered, callers, window⟩ =>
    ⟨data, before, cells, first, rest, claim accepted inputs scopes ordered, callers, window⟩

example (claim : RVProgramPreparedProtocolSequenceSoundnessClaim) :
    RVProgramPreparedProtocolSequenceSoundnessSatisfiableClaim →
    ∃ (data : UnifiedReduced.Caller.RVRequestTrace babyBearModulus) (before : RV.State) (cells : List Cell)
      (first : HashWindow) (rest : List HashWindow),
      RVPreparedHashSequenceResult data before cells first rest ∧ data.callers ≠ [] ∧
        data.workers.windowRows first.lower first.upper ≠ [] :=
  fun ⟨data, before, _, _, cells, _, _, first, rest, accepted, inputs, registry, scopes, ordered, callers,
      window⟩ =>
    ⟨data, before, cells, first, rest, claim accepted inputs registry scopes ordered, callers, window⟩

example (claim : RVPreparedRoundRegionMasksSoundnessClaim) : RVPreparedRoundRegionMasksSoundnessSatisfiableClaim →
    ∃ (data : UnifiedReduced.Caller.RVRequestTrace babyBearModulus) (region : RoundRegion),
      (∀ row ∈ data.workers.windowRows region.lower region.upper,
        ∃ round, Blake2Round.Memory.RoundMask row.assignment round) ∧ data.callers ≠ [] ∧
        data.workers.windowRows region.lower region.upper ≠ [] :=
  fun ⟨data, _, _, _, _, _, _, region, accepted, inputs, scope, callers, window⟩ =>
    ⟨data, region, claim accepted inputs scope, callers, window⟩

example (claim : RVPreparedRoundMasksSoundnessClaim) : RVPreparedRoundMasksSoundnessSatisfiableClaim →
    ∃ (data : UnifiedReduced.Caller.RVRequestTrace babyBearModulus),
      (∀ row ∈ data.workers.rows, ∃ round, Blake2Round.Memory.RoundMask row.assignment round) ∧
        data.callers ≠ [] ∧ data.workers.rows ≠ [] :=
  fun ⟨data, _, _, _, _, _, _, _, accepted, inputs, first, callers, rows⟩ =>
    ⟨data, claim accepted inputs first, callers, rows⟩

example (claim : RVPreparedRoundWindowSoundnessClaim) : RVPreparedRoundWindowSoundnessSatisfiableClaim →
    ∃ (data : UnifiedReduced.Caller.RVRequestTrace babyBearModulus) (before : RV.State) (cells : List Cell)
      (flags : Fin 8) (lower upper : Nat),
      RVJointHashWindowResult data before cells (.blakeRound flags) lower upper ∧ data.callers ≠ [] ∧
        data.workers.windowRows lower upper ≠ [] :=
  fun ⟨data, before, _, _, cells, _, flags, lower, upper, accepted, inputs, first, last, callers, window⟩ =>
    ⟨data, before, cells, flags, lower, upper, claim accepted inputs first last, callers, window⟩

example (claim : RVPreparedRoundCyclesSoundnessClaim) : RVPreparedRoundCyclesSoundnessSatisfiableClaim →
    ∃ (data : UnifiedReduced.Caller.RVRequestTrace babyBearModulus) (program : List UnifiedReduced.RVProgramEntry)
      (initial : RV.State) (cells : List Cell),
      RVCallerCycleEffects data program initial cells ∧ data.callers ≠ [] ∧ data.workers.rows ≠ [] :=
  fun ⟨data, program, initial, _, _, cells, _, _, accepted, inputs, first, started, callers, rows⟩ =>
    ⟨data, program, initial, cells, claim accepted inputs first started, callers, rows⟩

end UnifiedCallers

example (claim : JumpBranchSlt.RVTraceSoundnessClaim) : JumpBranchSlt.RVTraceSoundnessSatisfiableClaim →
    ∃ (trace : JumpBranchSlt.NativeTrace babyBearModulus) (initial : RV.State) (cells : List Cell),
      RVRealizes trace initial cells ∧ trace.rows ≠ [] :=
  fun ⟨trace, initial, cells, _, inputs, accepted, decoded, rows⟩ =>
    ⟨trace, initial, cells, claim inputs accepted decoded, rows⟩

example (claim : MulDiv.RVTraceSoundnessClaim) : MulDiv.RVTraceSoundnessSatisfiableClaim →
    ∃ (trace : MulDiv.NativeTrace babyBearModulus) (initial : RV.State) (cells : List Cell),
      RVRealizes trace initial cells ∧ trace.rows ≠ [] :=
  fun ⟨trace, initial, cells, _, inputs, accepted, decoded, rows⟩ =>
    ⟨trace, initial, cells, claim inputs accepted decoded, rows⟩

example (claim : ShiftBinop.RVTraceSoundnessClaim) : ShiftBinop.RVTraceSoundnessSatisfiableClaim →
    ∃ (trace : ShiftBinop.NativeTrace babyBearModulus) (initial : RV.State) (cells : List Cell),
      RVRealizes trace initial cells ∧ trace.rows ≠ [] :=
  fun ⟨trace, initial, cells, _, inputs, accepted, decoded, rows⟩ =>
    ⟨trace, initial, cells, claim inputs accepted decoded, rows⟩

example (claim : SubwordMemory.RVRamTraceSoundnessClaim) : SubwordMemory.RVRamTraceSoundnessSatisfiableClaim →
    ∃ (trace : SubwordMemory.NativeTrace babyBearModulus) (initial : RV.State) (cells : List Cell),
      RVRealizes trace initial cells ∧ trace.rows ≠ [] :=
  fun ⟨trace, initial, cells, _, inputs, accepted, decoded, rows⟩ =>
    ⟨trace, initial, cells, claim inputs accepted decoded, rows⟩

section Callers
open Delegation.Caller

example (claim : RVSoundnessClaim) : RVSoundnessSatisfiableClaim →
    ∃ (before : RV.State) (program : List Delegation.Caller.RVProgramEntry) (w : Nat → ZMod babyBearModulus),
      RVBinding w before program ∧ Delegation.Requests.Selected w :=
  fun ⟨before, _, program, w, hp, constraints, image, member, selected⟩ =>
    ⟨before, program, w, claim hp constraints image member, selected⟩

example (claim : RVPcSoundnessClaim) : RVPcSoundnessSatisfiableClaim →
    ∃ (before : RV.State) (program : List Delegation.Caller.RVProgramEntry) (w : Nat → ZMod babyBearModulus),
      RVPCBinding w before program ∧ Delegation.Requests.Selected w :=
  fun ⟨before, _, program, w, constraints, image, member, selected⟩ =>
    ⟨before, program, w, claim constraints image member, selected⟩

example (claim : RVRequestsSoundnessClaim) : RVRequestsSoundnessSatisfiableClaim →
    ∃ (data : RVRequestTrace babyBearModulus) (before : RV.State), RVRequestBinding data before ∧ data.callers ≠ [] :=
  fun ⟨data, before, _, accepted, inputs, callers⟩ => ⟨data, before, claim accepted inputs, callers⟩

example (claim : RVRequestMemorySoundnessClaim) : RVRequestMemorySoundnessSatisfiableClaim →
    ∃ (data : RVRequestTrace babyBearModulus) (before : RV.State) (cells : List Cell),
      RVRequestExecution data before cells ∧ data.callers ≠ [] :=
  fun ⟨data, before, _, cells, accepted, inputs, callers⟩ => ⟨data, before, cells, claim accepted inputs, callers⟩

example (claim : RVOperationSoundnessClaim) : RVOperationSoundnessSatisfiableClaim →
    ∃ (data : RVRequestTrace babyBearModulus) (before : RV.State) (cells : List Cell),
      RVRequestOperationEffects data before cells ∧ data.callers ≠ [] :=
  fun ⟨data, before, _, cells, accepted, inputs, callers⟩ => ⟨data, before, cells, claim accepted inputs, callers⟩

example (claim : RVSharedMemorySoundnessClaim) : RVSharedMemorySoundnessSatisfiableClaim →
    ∃ (data : RVRequestTrace babyBearModulus) (before : RV.State) (cells : List Cell),
      RVSharedMemoryEffects data before cells ∧ data.callers ≠ [] :=
  fun ⟨data, before, _, cells, accepted, inputs, callers⟩ => ⟨data, before, cells, claim accepted inputs, callers⟩

example (claim : RVSharedOperationSoundnessClaim) : RVSharedOperationSoundnessSatisfiableClaim →
    ∃ (data : RVRequestTrace babyBearModulus) (before : RV.State) (cells : List Cell),
      RVSharedOperationEffects data before cells ∧ data.callers ≠ [] :=
  fun ⟨data, before, _, cells, accepted, inputs, callers⟩ => ⟨data, before, cells, claim accepted inputs, callers⟩

example (claim : RVMixedMemorySoundnessClaim) : RVMixedMemorySoundnessSatisfiableClaim →
    ∃ (data : RVRequestTrace babyBearModulus) (before : RV.State) (cells : List Cell),
      RVMixedMemoryEffects data before cells ∧ data.callers ≠ [] :=
  fun ⟨data, _, before, _, _, cells, accepted, inputs, callers⟩ =>
    ⟨data, before, cells, claim accepted inputs, callers⟩

example (claim : RVWorkerScheduleSoundnessClaim) : RVWorkerScheduleSoundnessSatisfiableClaim →
    ∃ data : RVRequestTrace babyBearModulus, RVWorkerSchedule data ∧ data.callers ≠ [] :=
  fun ⟨data, _, _, accepted, inputs, callers⟩ => ⟨data, claim accepted inputs, callers⟩

example (claim : RVRequestWindowSoundnessClaim) : RVRequestWindowSoundnessSatisfiableClaim →
    ∃ (data : RVRequestTrace babyBearModulus) (lower upper : Nat),
      RequestWindowBinding data.callers data.workers lower upper ∧ windowCallers data.callers lower upper ≠ [] :=
  fun ⟨data, _, _, lower, upper, accepted, inputs, first, last, pastZero, window⟩ =>
    ⟨data, lower, upper, claim accepted inputs first last pastZero, window⟩

example (claim : Delegation.Caller.RVSharedSpanSoundnessClaim) :
    Delegation.Caller.RVSharedSpanSoundnessSatisfiableClaim →
    ∃ (data : Delegation.Caller.RVRequestTrace babyBearModulus) (before : RV.State) (cells : List Cell)
      (span : Delegation.Caller.HashSpan),
      Delegation.Caller.RVSharedSpanEffects data before cells span ∧ data.callers ≠ [] :=
  fun ⟨data, before, _, cells, span, accepted, inputs, callers⟩ =>
    ⟨data, before, cells, span, claim accepted inputs, callers⟩

example (claim : Delegation.Caller.RVRequestHashWindowSoundnessClaim) :
    Delegation.Caller.RVRequestHashWindowSoundnessSatisfiableClaim →
    ∃ (data : Delegation.Caller.RVRequestTrace babyBearModulus) (before : RV.State) (cells : List Cell)
      (span : Delegation.Caller.HashSpan) (lower upper : Nat),
      span.RVRequestWindowResult data.callers data.workers before cells lower upper ∧ data.callers ≠ [] ∧
        data.workers.windowRows lower upper ≠ [] :=
  fun ⟨data, before, _, cells, span, lower, upper, accepted, program, inputs, aligned, first, last, past, callers,
      window⟩ =>
    ⟨data, before, cells, span, lower, upper, claim accepted program inputs aligned first last past, callers, window⟩

end Callers

example (claim : Blake2G.Native.RVWorkvectorSoundnessClaim) : Blake2G.Native.RVWorkvectorSoundnessSatisfiableClaim →
    ∃ (data : Delegation.MemoryData babyBearModulus) (initial after : RV.State) (cells : List Cell),
      Delegation.RVTraceMapping data initial after cells ∧ data.rows ≠ [] :=
  fun ⟨data, initial, cells, reduced, accepted, inputs, aligned⟩ =>
    have ⟨after, _, _, _, _, _, _, trace, _⟩ := claim accepted inputs aligned
    ⟨data, initial, after, cells, trace, fun empty => by
      have calls := inputs.calls
      rw [empty] at calls
      cases reduced <;> simp [Blake2G.callCount] at calls⟩

example (claim : Blake2G.Native.RVWorkvectorBoundarySoundnessClaim) :
    Blake2G.Native.RVWorkvectorBoundarySoundnessSatisfiableClaim →
    ∃ (data : Delegation.MemoryData babyBearModulus) (initial after : RV.State) (cells : List Cell),
      Delegation.RVTraceMapping data initial after cells ∧ data.rows ≠ [] :=
  fun ⟨data, initial, cells, reduced, accepted, inputs, aligned⟩ =>
    have ⟨after, _, _, _, _, _, _, trace, _⟩ := claim accepted inputs aligned
    ⟨data, initial, after, cells, trace, fun empty => by
      have calls := inputs.calls
      rw [empty] at calls
      cases reduced <;> simp [Blake2G.callCount] at calls⟩

example (claim : Blake2G.Native.RVWindowSoundnessClaim) : Blake2G.Native.RVWindowSoundnessSatisfiableClaim →
    ∃ (data : Delegation.MemoryData babyBearModulus) (before : RV.State) (cells : List Cell) (reduced : Bool)
      (lower upper : Nat), Delegation.Caller.RVWindowResult (Blake2G.RVSpanResult reduced) data before cells lower upper ∧
        data.windowRows lower upper ≠ [] :=
  fun ⟨data, before, cells, reduced, lower, upper, accepted, inputs, aligned⟩ =>
    ⟨data, before, cells, reduced, lower, upper, claim accepted inputs aligned, fun empty => by
      have calls := inputs.calls
      rw [empty] at calls
      cases reduced <;> simp [Blake2G.callCount] at calls⟩

example (claim : Keccak.Split.Native.RVPermutationSoundnessClaim) :
    Keccak.Split.Native.RVPermutationSoundnessSatisfiableClaim →
    ∃ (data : Keccak.Split.Native.MemoryData babyBearModulus) (initial after : RV.State) (cells : List Cell),
      Keccak.Split.Native.RVTraceMapping data initial after cells ∧ data.rows ≠ [] :=
  fun ⟨data, initial, cells, accepted, inputs, aligned⟩ =>
    have ⟨states, _, _, _, _, _, _, trace, _⟩ := claim accepted inputs aligned
    ⟨data, initial, states 361, cells, trace, fun empty => by
      have calls := inputs.calls
      rw [empty] at calls
      simp at calls⟩

example (claim : Keccak.Native.RVPermutationSoundnessClaim) : Keccak.Native.RVPermutationSoundnessSatisfiableClaim →
    ∃ (data : Delegation.MemoryData babyBearModulus) (initial after : RV.State) (cells : List Cell),
      Delegation.RVTraceMapping data initial after cells ∧ data.rows ≠ [] :=
  fun ⟨data, initial, cells, accepted, inputs, tables, aligned⟩ =>
    have ⟨after, _, _, _, _, trace, _⟩ := claim accepted inputs tables aligned
    ⟨data, initial, after, cells, trace, fun empty => by
      have calls := inputs.calls
      rw [empty] at calls
      simp at calls⟩

example (claim : Keccak.Native.RVPermutationBoundarySoundnessClaim) :
    Keccak.Native.RVPermutationBoundarySoundnessSatisfiableClaim →
    ∃ (data : Delegation.MemoryData babyBearModulus) (initial after : RV.State) (cells : List Cell),
      Delegation.RVTraceMapping data initial after cells ∧ data.rows ≠ [] :=
  fun ⟨data, initial, cells, accepted, inputs, tables, aligned⟩ =>
    have ⟨after, _, _, _, _, trace, _⟩ := claim accepted inputs tables aligned
    ⟨data, initial, after, cells, trace, fun empty => by
      have calls := inputs.calls
      rw [empty] at calls
      simp at calls⟩

example (claim : Keccak.Native.RVWindowSoundnessClaim) : Keccak.Native.RVWindowSoundnessSatisfiableClaim →
    ∃ (data : Delegation.MemoryData babyBearModulus) (before : RV.State) (cells : List Cell) (lower upper : Nat),
      Delegation.Caller.RVWindowResult Keccak.RVSpanResult data before cells lower upper ∧
        data.windowRows lower upper ≠ [] :=
  fun ⟨data, before, cells, lower, upper, accepted, inputs, aligned⟩ =>
    ⟨data, before, cells, lower, upper, claim accepted inputs aligned, fun empty => by
      have calls := inputs.calls
      rw [empty] at calls
      simp at calls⟩

example (claim : Blake2Round.Native.RVCompressionSoundnessClaim) :
    Blake2Round.Native.RVCompressionSoundnessSatisfiableClaim →
    ∃ (data : Delegation.MemoryData babyBearModulus) (initial after : RV.State) (cells : List Cell),
      Delegation.RVTraceMapping data initial after cells ∧ data.rows ≠ [] :=
  fun ⟨data, initial, cells, flags, accepted, inputs, aligned⟩ =>
    have ⟨after, _, _, _, _, _, _, trace, _⟩ := claim accepted inputs aligned
    ⟨data, initial, after, cells, trace, fun empty => by
      have calls := inputs.calls
      rw [empty] at calls
      split at calls <;> simp at calls⟩

example (claim : Blake2Round.Native.RVCompressionBoundarySoundnessClaim) :
    Blake2Round.Native.RVCompressionBoundarySoundnessSatisfiableClaim →
    ∃ (data : Delegation.MemoryData babyBearModulus) (initial after : RV.State) (cells : List Cell),
      Delegation.RVTraceMapping data initial after cells ∧ data.rows ≠ [] :=
  fun ⟨data, initial, cells, flags, accepted, inputs, aligned⟩ =>
    have ⟨after, _, _, _, _, _, _, trace, _⟩ := claim accepted inputs aligned
    ⟨data, initial, after, cells, trace, fun empty => by
      have calls := inputs.calls
      rw [empty] at calls
      split at calls <;> simp at calls⟩

example (claim : Blake2Round.Native.RVWindowSoundnessClaim) : Blake2Round.Native.RVWindowSoundnessSatisfiableClaim →
    ∃ (data : Delegation.MemoryData babyBearModulus) (before : RV.State) (cells : List Cell) (flags : Fin 8)
      (lower upper : Nat),
      Delegation.Caller.RVWindowResult (Blake2Round.RVSpanResult flags) data before cells lower upper ∧
        data.windowRows lower upper ≠ [] :=
  fun ⟨data, before, cells, flags, lower, upper, accepted, inputs, aligned⟩ =>
    ⟨data, before, cells, flags, lower, upper, claim accepted inputs aligned, fun empty => by
      have calls := inputs.calls
      rw [empty] at calls
      split at calls <;> simp at calls⟩

end Checks.Satisfiable

namespace Checks.Satisfiable

example (claim : Airbender.AddSub.RVSoundnessClaim) : Airbender.AddSub.RVSatisfiableClaim →
    ∃ input output, Airbender.AddSub.rvSpec input output :=
  fun ⟨trace, initial, cells, program, input, output, w, assumptions, relation⟩ =>
    ⟨input, output, claim trace initial cells program assumptions input output w relation⟩

example (claim : Airbender.MulDiv.RVSoundnessClaim) : Airbender.MulDiv.RVSatisfiableClaim →
    ∃ input output, Airbender.MulDiv.rvSpec input output :=
  fun ⟨trace, initial, cells, program, input, output, w, assumptions, relation⟩ =>
    ⟨input, output, claim trace initial cells program assumptions input output w relation⟩

example (claim : Airbender.ShiftBinop.RVSoundnessClaim) : Airbender.ShiftBinop.RVSatisfiableClaim →
    ∃ input output, Airbender.ShiftBinop.rvSpec input output :=
  fun ⟨trace, initial, cells, program, input, output, w, assumptions, relation⟩ =>
    ⟨input, output, claim trace initial cells program assumptions input output w relation⟩

example (claim : Airbender.SubwordMemory.RVSoundnessClaim) : Airbender.SubwordMemory.RVSatisfiableClaim →
    ∃ input output, Airbender.SubwordMemory.rvSpec input output :=
  fun ⟨trace, initial, cells, program, input, output, w, assumptions, relation⟩ =>
    ⟨input, output, claim trace initial cells program assumptions input output w relation⟩

example (claim : Airbender.WordMemory.RVSoundnessClaim) : Airbender.WordMemory.RVSatisfiableClaim →
    ∃ input output, Airbender.WordMemory.rvSpec input output :=
  fun ⟨trace, initial, cells, program, input, output, w, assumptions, relation⟩ =>
    ⟨input, output, claim trace initial cells program assumptions input output w relation⟩

example (claim : Airbender.JumpBranchSlt.Comparison.RVSoundnessClaim) : Airbender.JumpBranchSlt.Comparison.RVSatisfiableClaim →
    ∃ input output, Airbender.JumpBranchSlt.Comparison.rvSpec input output :=
  fun ⟨trace, initial, cells, program, input, output, w, assumptions, relation⟩ =>
    ⟨input, output, claim trace initial cells program assumptions input output w relation⟩

example (claim : Airbender.JumpBranchSlt.Branch.RVSoundnessClaim) : Airbender.JumpBranchSlt.Branch.RVSatisfiableClaim →
    ∃ input output, Airbender.JumpBranchSlt.Branch.rvSpec input output :=
  fun ⟨trace, initial, cells, program, input, output, w, assumptions, relation⟩ =>
    ⟨input, output, claim trace initial cells program assumptions input output w relation⟩

example (claim : Airbender.JumpBranchSlt.Jump.RVSoundnessClaim) : Airbender.JumpBranchSlt.Jump.RVSatisfiableClaim →
    ∃ input output, Airbender.JumpBranchSlt.Jump.rvSpec input output :=
  fun ⟨trace, initial, cells, program, input, output, w, assumptions, relation⟩ =>
    ⟨input, output, claim trace initial cells program assumptions input output w relation⟩

end Checks.Satisfiable

example (claim : Airbender.InitsTeardowns.Native.StandaloneSoundnessClaim)
    (satisfiable : Airbender.InitsTeardowns.Native.StandaloneSatisfiableClaim) :
    ∃ (parameters : Airbender.InitsTeardowns.Native.Parameters Airbender.babyBearModulus
      (ZMod Airbender.babyBearModulus)) (raw : Airbender.InitsTeardowns.Native.Raw Airbender.babyBearModulus)
      (wires : Airbender.InitsTeardowns.Native.Wires (ZMod Airbender.babyBearModulus)),
      Airbender.InitsTeardowns.Native.Accepted Airbender.InitsTeardowns.Native.standaloneArtifact parameters raw wires ∧
      Airbender.InitsTeardowns.Native.rootProduct Airbender.InitsTeardowns.Native.standaloneArtifact
        Airbender.InitsTeardowns.Native.standaloneArtifact.terminal wires =
        ((Airbender.InitsTeardowns.Native.ramTokens Airbender.InitsTeardowns.Native.standaloneArtifact.layout
          parameters raw .terminal).map parameters.encode).prod := by
  obtain ⟨parameters, raw, wires, accepted⟩ := satisfiable
  exact ⟨parameters, raw, wires, accepted, (claim parameters raw wires accepted).1⟩

example (claim : Airbender.InitsTeardowns.Native.UnifiedSoundnessClaim)
    (satisfiable : Airbender.InitsTeardowns.Native.UnifiedSatisfiableClaim) :
    ∃ (parameters : Airbender.InitsTeardowns.Native.Parameters Airbender.babyBearModulus
      (ZMod Airbender.babyBearModulus)) (raw : Airbender.InitsTeardowns.Native.Raw Airbender.babyBearModulus)
      (wires : Airbender.InitsTeardowns.Native.Wires (ZMod Airbender.babyBearModulus)),
      Airbender.InitsTeardowns.Native.Accepted Airbender.InitsTeardowns.Native.unifiedArtifact parameters raw wires ∧
      Airbender.InitsTeardowns.Native.rootProduct Airbender.InitsTeardowns.Native.unifiedArtifact
        Airbender.InitsTeardowns.Native.unifiedArtifact.terminal wires =
        ((Airbender.InitsTeardowns.Native.ramTokens Airbender.InitsTeardowns.Native.unifiedArtifact.layout
          parameters raw .terminal).map parameters.encode).prod := by
  obtain ⟨parameters, raw, wires, accepted⟩ := satisfiable
  exact ⟨parameters, raw, wires, accepted, (claim parameters raw wires accepted).1⟩

example (claim : Airbender.Blake2Round.Mask.SoundnessClaim)
    (witness : Airbender.Blake2Round.Mask.SatisfiableClaim) :
    ∃ (input : Airbender.Blake2Round.Mask.Input) (output : Airbender.Blake2Round.Mask.Output)
      (w : Nat → ZMod Airbender.babyBearModulus),
      Airbender.Blake2Round.Mask.Assumptions input ∧ Airbender.Blake2Round.Mask.Mapping input output w ∧
      Airbender.Blake2Round.Mask.spec input output := by
  obtain ⟨input, output, w, assumptions, constraints, mapping⟩ := witness
  exact ⟨input, output, w, assumptions, mapping, claim input output w assumptions constraints mapping⟩
