import Proven.Final.Import.Theorems
import Proven.Final.Compiler.WorkerCertificates
import Proven.Final.Compiler.WorkerArithmetic
import Proven.Final.Compiler.WorkerSelectors
import Proven.Final.Trace.Machine.Witnesses
import Proven.Final.ISA.NativeTargets
import Proven.Final.Helpers.Context.PaddingBoundary
import Proven.Final.ISA.ValidUse
import Proven.Final.Compiler.NativeMachine
import Proven.Final.ISA.DelegationRuns
import Proven.Final.Helpers.Context.PCState.Theorems
import Proven.Final.Circuits.Blake2G.Theorems
import Proven.Final.Circuits.Bigint.RVTheorems
import Proven.Final.Compiler.Arithmetic
import Proven.Final.ISA.WholeRun
import Proven.Final.ISA.Interpreter
import Proven.Final.ISA.MachineTargets
import Proven.Final.ISA.Theorems
import Proven.Final.Compiler.LookupSelectors
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
import Proven.Final.Compiler.MemoryPorts
import Proven.Final.Compiler.PaddedNativeMachine
import Proven.Final.Compiler.WorkerMemoryPorts
import Proven.Final.Compiler.MemoryComposition
import Proven.Final.Compiler.CertificateMemory
import Proven.Final.Compiler.PermutationMachine

import Proven.Final.Circuits.InitsTeardowns.SharedArtifact

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


example (claim : InitsTeardowns.StandaloneClaim) : InitsTeardowns.StandaloneSatisfiableClaim →
    ∃ instances : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout),
      (InitsTeardowns.windowCells InitsTeardowns.importedLayout
        (instances.flatMap fun witness => witness.topBits.toList)).Nodup ∧
      instances.flatMap InitsTeardowns.Witness.initTokens = ROMView.nativeBootImage
        (InitsTeardowns.windowCells InitsTeardowns.importedLayout
          (instances.flatMap fun witness => witness.topBits.toList)) :=
  fun ⟨instances, _, checked⟩ => ⟨instances, claim.1.bootImage instances checked⟩

example (claim : InitsTeardowns.UnifiedClaim) : InitsTeardowns.UnifiedSatisfiableClaim →
    ∃ instances : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.unifiedLayout),
      (InitsTeardowns.windowCells InitsTeardowns.unifiedLayout
        (instances.flatMap fun witness => witness.topBits.toList)).Nodup ∧
      instances.flatMap InitsTeardowns.Witness.initTokens = ROMView.nativeBootImage
        (InitsTeardowns.windowCells InitsTeardowns.unifiedLayout
          (instances.flatMap fun witness => witness.topBits.toList)) :=
  fun ⟨instances, _, checked⟩ => ⟨instances, claim.1.bootImage instances checked⟩

example (claim : Delegation.RVNativeMemoryExecutionClaim) : Delegation.RVNativeMemoryExecutionSatisfiableClaim →
    ∃ (data : Delegation.MemoryData babyBearModulus) (before : RV.State) (cells : List Cell),
      Delegation.RVMemoryExecution data before cells ∧ data.rows ≠ [] :=
  fun ⟨data, before, cells, hp, accepted, «inputs», aligned, rows⟩ =>
    ⟨data, before, cells, claim hp accepted «inputs» aligned, rows⟩

example (claim : Delegation.RVOperationMemorySoundnessClaim) :
    Delegation.RVOperationMemorySoundnessSatisfiableClaim →
    ∃ data : Delegation.MemoryData babyBearModulus,
      (Delegation.MemorySoundness data ∧ Delegation.WordBounds data) ∧ data.rows ≠ [] :=
  fun ⟨data, _, _, _, accepted, «inputs», rows⟩ => ⟨data, claim accepted «inputs», rows⟩

example (claim : Delegation.RVMemorySoundnessClaim) : Delegation.RVMemorySoundnessSatisfiableClaim →
    ∃ data : Delegation.MemoryData babyBearModulus, Delegation.MemorySoundness data ∧ data.rows ≠ [] :=
  fun ⟨data, _, _, hp, accepted, «inputs», rows⟩ => ⟨data, claim hp accepted «inputs», rows⟩

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
  fun ⟨data, before, cells, accepted, «inputs», aligned, table, row, member, family⟩ =>
    have result := claim accepted «inputs» aligned table
    ⟨data, before, cells, result.1, row, member, family, result.2.1 row member family⟩

example (claim : RVPooledNativeSoundnessClaim) : RVPooledNativeSoundnessSatisfiableClaim →
    ∃ (trace : PooledTrace babyBearModulus) (initial : RV.State) (cells : List Cell),
      RVRealizes trace initial cells ∧ trace.rows ≠ [] :=
  fun ⟨trace, initial, cells, _, _, «inputs», accepted, decoded, rows⟩ =>
    ⟨trace, initial, cells, claim «inputs» accepted decoded, rows⟩

example (claim : BootRamZeroClaim) : BootRamZeroSatisfiableClaim →
    ∃ (initial : RV.State) (cells : List Cell) (address : BitVec 32),
      Cell.ram address ∈ cells ∧ (Cell.ram address).readRV initial = some 0 :=
  fun ⟨_, initial, cells, _, _, _, «inputs», address, member⟩ =>
    ⟨initial, cells, address, member, claim «inputs» address member⟩

example (claim : NonDeterminism.Pooled.RVNativeSoundnessClaim) :
    NonDeterminism.Pooled.RVNativeSoundnessSatisfiableClaim →
    ∃ (trace : PooledTrace babyBearModulus) (initial : RV.State) (cells : List Cell),
      NonDeterminism.Pooled.RVRealizes trace initial cells ∧ trace.rows ≠ [] :=
  fun ⟨trace, initial, cells, _, _, «inputs», accepted, decoded, ports, rows⟩ =>
    ⟨trace, initial, cells, claim «inputs» accepted decoded ports, rows⟩

example (claim : NoZeroTimestampWritesClaim) : NoZeroTimestampWritesSatisfiableClaim →
    ∃ trace : PooledTrace babyBearModulus, ∃ row ∈ trace.rows, ∃ token ∈ row.writes,
      4 ≤ (timeOfPair token.time).value :=
  fun ⟨trace, accepted, boot, row, member, token, present⟩ =>
    ⟨trace, row, member, token, present, claim accepted boot row member token present⟩

example (claim : WritesRangeCheckedClaim) : WritesRangeCheckedSatisfiableClaim →
    ∃ trace : PooledTrace babyBearModulus, ∃ row ∈ trace.rows, row.memorySteps ≠ [] ∧
      ∀ step ∈ row.memorySteps, step.2.word.Bounded :=
  fun ⟨trace, _, _, _, _, _, table, «inputs», accepted, decoded, row, member, steps, reads⟩ =>
    ⟨trace, row, member, steps, claim table «inputs» accepted decoded row member reads⟩

example (claim : TeardownsBoundedClaim) : TeardownsBoundedSatisfiableClaim →
    ∃ inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout),
      ∃ w ∈ inits, ∃ token ∈ w.teardownTokens, token.word.Bounded :=
  fun ⟨_, _, _, _, inits, _, table, «inputs», accepted, decoded, reads, w, present, token, member⟩ =>
    ⟨inits, w, present, token, member, claim table «inputs» accepted decoded reads w present token member⟩

example (claim : RVAirbenderSoundnessClaim) : RVAirbenderSoundnessSatisfiableClaim →
    ∃ (trace : Data babyBearModulus) (initial : RV.State) (cells : List Cell),
      RVRealizes trace initial cells ∧ trace.rows ≠ [] :=
  fun ⟨trace, initial, cells, _, «inputs», accepted, decoded, rows⟩ =>
    ⟨trace, initial, cells, claim «inputs» accepted decoded, rows⟩

example (claim : RVNativeBootSoundnessClaim) : RVNativeBootSoundnessSatisfiableClaim →
    ∃ (trace : Data babyBearModulus) (initial : RV.State) (cells : List Cell),
      RVRealizes trace initial cells ∧ trace.rows ≠ [] :=
  fun ⟨trace, initial, cells, _, _, «inputs», accepted, decoded, rows⟩ =>
    ⟨trace, initial, cells, claim «inputs» accepted decoded, rows⟩

example (claim : UnifiedReduced.RVExecutionSoundnessClaim) : UnifiedReduced.RVExecutionSoundnessSatisfiableClaim →
    ∃ (trace : UnifiedTrace babyBearModulus) (initial : RV.State) (cells : List Cell),
      RVRealizes trace initial cells ∧ trace.rows ≠ [] :=
  fun ⟨trace, initial, cells, _, _, «inputs», accepted, decoded, rows⟩ =>
    ⟨trace, initial, cells, claim «inputs» accepted decoded, rows⟩

example (claim : UnifiedReduced.BootRamZeroClaim) : UnifiedReduced.BootRamZeroSatisfiableClaim →
    ∃ (initial : RV.State) (cells : List Cell) (address : BitVec 32),
      Cell.ram address ∈ cells ∧ (Cell.ram address).readRV initial = some 0 :=
  fun ⟨_, initial, cells, _, _, «inputs», address, member⟩ =>
    ⟨initial, cells, address, member, claim «inputs» address member⟩

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
  fun ⟨_, _, _, _, inits, «inputs», accepted, reads, w, present, token, member⟩ =>
    ⟨inits, w, present, token, member, claim «inputs» accepted reads w present token member⟩

example (claim : Blake2G.Native.RVOperationExecutionClaim) : Blake2G.Native.RVOperationExecutionSatisfiableClaim →
    ∃ (data : Delegation.MemoryData babyBearModulus) (before : RV.State) (cells : List Cell),
      Delegation.RVMemoryExecution data before cells ∧ ∃ row ∈ data.rows, row.family = .blakeG ∧
        Blake2G.spec (Blake2G.Native.input row.assignment) (Blake2G.Native.output row.assignment) :=
  fun ⟨data, before, cells, _, accepted, «inputs», aligned, row, member, family⟩ =>
    have result := claim accepted «inputs» aligned
    ⟨data, before, cells, result.1, row, member, family, result.2 row member family⟩

example (claim : Keccak.Native.RVOperationExecutionClaim) : Keccak.Native.RVOperationExecutionSatisfiableClaim →
    ∃ (data : Delegation.MemoryData babyBearModulus) (before : RV.State) (cells : List Cell),
      Delegation.RVMemoryExecution data before cells ∧ ∃ row ∈ data.rows, row.family = .keccak ∧
        Keccak.Native.RowEffects row.assignment :=
  fun ⟨data, before, cells, accepted, «inputs», aligned, row, member, family⟩ =>
    have result := claim accepted «inputs» aligned
    ⟨data, before, cells, result.1, row, member, family, result.2 row member family⟩

example (claim : Keccak.Split.Native.RVOperationExecutionClaim) :
    Keccak.Split.Native.RVOperationExecutionSatisfiableClaim →
    ∃ (data : Keccak.Split.Native.MemoryData babyBearModulus) (before : RV.State) (cells : List Cell),
      Keccak.Split.Native.RVMemoryExecution data before cells ∧
        ∃ row ∈ data.rows, Keccak.Split.Native.RowEffects row :=
  fun ⟨data, before, cells, accepted, «inputs», aligned, row, member⟩ =>
    have result := claim accepted «inputs» aligned
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
  fun ⟨data, before, cells, _, accepted, «inputs», aligned, row, member, family⟩ =>
    have result := claim accepted «inputs» aligned
    ⟨data, before, cells, result.1, row, member, family, result.2 row member family⟩

section UnifiedCallers
open UnifiedReduced.Caller

example (claim : RVMixedMemorySoundnessClaim) : RVMixedMemorySoundnessSatisfiableClaim →
    ∃ (data : UnifiedReduced.Caller.RVRequestTrace babyBearModulus) (before : RV.State) (cells : List Cell),
      RVMixedMemoryEffects data before cells ∧ data.callers ≠ [] :=
  fun ⟨data, _, before, _, _, cells, accepted, «inputs», callers⟩ =>
    ⟨data, before, cells, claim accepted «inputs», callers⟩

example (claim : RVRequestWindowSoundnessClaim) : RVRequestWindowSoundnessSatisfiableClaim →
    ∃ (data : UnifiedReduced.Caller.RVRequestTrace babyBearModulus) (lower upper : Nat),
      Delegation.Caller.RequestWindowBinding data.callers data.workers lower upper ∧ data.callers ≠ [] ∧
        data.workers.windowRows lower upper ≠ [] :=
  fun ⟨data, _, _, lower, upper, checks, «inputs», first, last, past, callers, window⟩ =>
    ⟨data, lower, upper, claim checks «inputs» first last past, callers, window⟩

example (claim : RVMixedWindowSoundnessClaim) : RVMixedWindowSoundnessSatisfiableClaim →
    ∃ (data : UnifiedReduced.Caller.RVRequestTrace babyBearModulus) (before : RV.State) (cells : List Cell) (lower upper : Nat),
      RVMixedWindowExecution data before cells lower upper ∧ data.callers ≠ [] ∧
        data.workers.windowRows lower upper ≠ [] :=
  fun ⟨data, _, before, _, _, cells, lower, upper, accepted, «inputs», first, last, past, ordered, callers, window⟩ =>
    ⟨data, before, cells, lower, upper, claim accepted «inputs» first last past ordered, callers, window⟩

example (claim : RVWindowProjectionSoundnessClaim) : RVWindowProjectionSoundnessSatisfiableClaim →
    ∃ (data : UnifiedReduced.Caller.RVRequestTrace babyBearModulus) (before : RV.State) (cells : List Cell) (lower upper : Nat),
      RVProjectedWindowExecution data before cells lower upper ∧ data.callers ≠ [] ∧
        data.workers.windowRows lower upper ≠ [] :=
  fun ⟨data, before, _, _, cells, lower, upper, accepted, «inputs», first, last, past, ordered, callers, window⟩ =>
    ⟨data, before, cells, lower, upper, claim accepted «inputs» first last past ordered, callers, window⟩

example (claim : RVWindowScheduleSoundnessClaim) : RVWindowScheduleSoundnessSatisfiableClaim →
    ∃ (data : UnifiedReduced.Caller.RVRequestTrace babyBearModulus) (lower upper : Nat),
      RVCallerWindowSchedule data lower upper ∧ data.callers ≠ [] ∧ data.workers.windowRows lower upper ≠ [] :=
  fun ⟨data, _, _, lower, upper, checks, «inputs», first, last, past, ordered, after, before, duration, callers,
      window⟩ =>
    ⟨data, lower, upper, claim checks «inputs» first last past ordered after before duration, callers, window⟩

example (claim : RVMixedWindowProjectionSoundnessClaim) : RVMixedWindowProjectionSoundnessSatisfiableClaim →
    ∃ (data : UnifiedReduced.Caller.RVRequestTrace babyBearModulus) (before : RV.State) (cells : List Cell) (lower upper : Nat),
      RVMixedProjectedWindowExecution data before cells lower upper ∧ data.callers ≠ [] ∧
        data.workers.windowRows lower upper ≠ [] :=
  fun ⟨data, _, before, _, _, cells, lower, upper, accepted, «inputs», first, last, past, ordered, after, beforeT,
      duration, callers, window⟩ =>
    ⟨data, before, cells, lower, upper,
      claim accepted «inputs» first last past ordered after beforeT duration, callers, window⟩

example (claim : RVMixedWindowSequenceSoundnessClaim) : RVMixedWindowSequenceSoundnessSatisfiableClaim →
    ∃ (data : UnifiedReduced.Caller.RVRequestTrace babyBearModulus) (before : RV.State) (cells : List Cell) (cut : Nat) (windows : List (Nat × Nat)),
      RVMixedWindowSequenceExecution data before cells cut windows ∧ data.callers ≠ [] ∧
        ∃ window ∈ windows, data.workers.windowRows window.1 window.2 ≠ [] :=
  fun ⟨data, _, before, _, _, cells, cut, windows, accepted, «inputs», first, positive, ordered, callers, window⟩ =>
    ⟨data, before, cells, cut, windows, claim accepted «inputs» first positive ordered, callers, window⟩

example (claim : RVCallerCyclesSoundnessClaim) : RVCallerCyclesSoundnessSatisfiableClaim →
    ∃ (data : UnifiedReduced.Caller.RVRequestTrace babyBearModulus) (program : List UnifiedReduced.RVProgramEntry) (initial : RV.State) (cells : List Cell),
      RVCallerCycleEffects data program initial cells ∧ data.callers ≠ [] :=
  fun ⟨data, program, initial, _, _, cells, accepted, «inputs», started, callers⟩ =>
    ⟨data, program, initial, cells, claim accepted «inputs» started, callers⟩

example (claim : RVControlPreparationSoundnessClaim) : RVControlPreparationSoundnessSatisfiableClaim →
    ∃ (data : UnifiedReduced.Caller.RVRequestTrace babyBearModulus) (before : RV.State) (cells : List Cell) (cut : Nat) (register : BitVec 5)
      (literal : ControlLiteral),
      RVPreparedBoundaryExecution data before cells cut register literal ∧ data.callers ≠ [] :=
  fun ⟨data, _, before, _, _, cells, cut, register, literal, accepted, «inputs», scope, nonzero, aligned, callers⟩ =>
    ⟨data, before, cells, cut, register, literal, claim accepted «inputs» scope nonzero aligned, callers⟩

example (claim : RVControlPreparationWindowSoundnessClaim) : RVControlPreparationWindowSoundnessSatisfiableClaim →
    ∃ (data : UnifiedReduced.Caller.RVRequestTrace babyBearModulus) (before : RV.State) (cells : List Cell) (lower upper : Nat) (r s : BitVec 5)
      (a b : ControlLiteral),
      RVPreparedControlWindow data before cells lower upper r a s b ∧ data.callers ≠ [] ∧
        data.workers.windowRows lower upper ≠ [] :=
  fun ⟨data, _, before, _, _, cells, lower, upper, r, s, a, b, accepted, «inputs», firstScope, lastScope, rn, sn,
      first, last, ordered, callers, window⟩ =>
    ⟨data, before, cells, lower, upper, r, s, a, b,
      claim accepted «inputs» firstScope lastScope rn sn first last ordered, callers, window⟩

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
  fun ⟨data, before, _, cells, span, accepted, «inputs», callers⟩ =>
    ⟨data, before, cells, span, claim accepted «inputs», callers⟩

example (claim : RVRequestHashWindowSoundnessClaim) : RVRequestHashWindowSoundnessSatisfiableClaim →
    ∃ (data : UnifiedReduced.Caller.RVRequestTrace babyBearModulus) (before : RV.State) (cells : List Cell)
      (span : Delegation.Caller.HashSpan) (lower upper : Nat),
      span.RVRequestWindowResult data.callers data.workers before cells lower upper ∧ data.callers ≠ [] ∧
        data.workers.windowRows lower upper ≠ [] :=
  fun ⟨data, before, _, cells, span, lower, upper, checks, workers, program, «inputs», aligned, first, last, past,
      callers, window⟩ =>
    ⟨data, before, cells, span, lower, upper, claim checks workers program «inputs» aligned first last past, callers,
      window⟩

example (claim : RVJointHashWindowSoundnessClaim) : RVJointHashWindowSoundnessSatisfiableClaim →
    ∃ (data : UnifiedReduced.Caller.RVRequestTrace babyBearModulus) (before : RV.State) (cells : List Cell)
      (span : Delegation.Caller.HashSpan) (lower upper : Nat),
      RVJointHashWindowResult data before cells span lower upper ∧ data.callers ≠ [] ∧
        data.workers.windowRows lower upper ≠ [] :=
  fun ⟨data, before, _, cells, span, lower, upper, accepted, «inputs», first, last, positive, ordered, callers,
      window⟩ =>
    ⟨data, before, cells, span, lower, upper, claim accepted «inputs» first last positive ordered, callers, window⟩

example (claim : RVPreparedHashWindowSoundnessClaim) : RVPreparedHashWindowSoundnessSatisfiableClaim →
    ∃ (data : UnifiedReduced.Caller.RVRequestTrace babyBearModulus) (before : RV.State) (cells : List Cell)
      (span : Delegation.Caller.HashSpan) (lower upper : Nat),
      RVJointHashWindowResult data before cells span lower upper ∧ data.callers ≠ [] ∧
        data.workers.windowRows lower upper ≠ [] :=
  fun ⟨data, before, _, _, cells, _, span, lower, upper, accepted, «inputs», first, last, callers, window⟩ =>
    ⟨data, before, cells, span, lower, upper, claim accepted «inputs» first last, callers, window⟩

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
  fun ⟨data, before, _, _, cells, _, _, first, rest, accepted, «inputs», scopes, ordered, callers, window⟩ =>
    ⟨data, before, cells, first, rest, claim accepted «inputs» scopes ordered, callers, window⟩

example (claim : RVProgramPreparedProtocolSequenceSoundnessClaim) :
    RVProgramPreparedProtocolSequenceSoundnessSatisfiableClaim →
    ∃ (data : UnifiedReduced.Caller.RVRequestTrace babyBearModulus) (before : RV.State) (cells : List Cell)
      (first : HashWindow) (rest : List HashWindow),
      RVPreparedHashSequenceResult data before cells first rest ∧ data.callers ≠ [] ∧
        data.workers.windowRows first.lower first.upper ≠ [] :=
  fun ⟨data, before, _, _, cells, _, _, first, rest, accepted, «inputs», registry, scopes, ordered, callers,
      window⟩ =>
    ⟨data, before, cells, first, rest, claim accepted «inputs» registry scopes ordered, callers, window⟩

example (claim : RVPreparedRoundRegionMasksSoundnessClaim) : RVPreparedRoundRegionMasksSoundnessSatisfiableClaim →
    ∃ (data : UnifiedReduced.Caller.RVRequestTrace babyBearModulus) (region : RoundRegion),
      (∀ row ∈ data.workers.windowRows region.lower region.upper,
        ∃ round, Blake2Round.Memory.RoundMask row.assignment round) ∧ data.callers ≠ [] ∧
        data.workers.windowRows region.lower region.upper ≠ [] :=
  fun ⟨data, _, _, _, _, _, _, region, accepted, «inputs», scope, _, member, callers⟩ =>
    ⟨data, region, claim accepted «inputs» scope, callers, List.ne_nil_of_mem member⟩

example (claim : RVPreparedRoundMasksSoundnessClaim) : RVPreparedRoundMasksSoundnessSatisfiableClaim →
    ∃ (data : UnifiedReduced.Caller.RVRequestTrace babyBearModulus),
      (∀ row ∈ data.workers.rows, ∃ round, Blake2Round.Memory.RoundMask row.assignment round) ∧
        data.callers ≠ [] ∧ data.workers.rows ≠ [] :=
  fun ⟨data, _, _, _, _, _, _, _, accepted, «inputs», first, _, member, callers⟩ =>
    ⟨data, claim accepted «inputs» first, callers, List.ne_nil_of_mem member⟩

example (claim : RVPreparedRoundWindowSoundnessClaim) : RVPreparedRoundWindowSoundnessSatisfiableClaim →
    ∃ (data : UnifiedReduced.Caller.RVRequestTrace babyBearModulus) (before : RV.State) (cells : List Cell)
      (flags : Fin 8) (lower upper : Nat),
      RVJointHashWindowResult data before cells (.blakeRound flags) lower upper ∧ data.callers ≠ [] ∧
        data.workers.windowRows lower upper ≠ [] :=
  fun ⟨data, before, _, _, cells, _, flags, lower, upper, accepted, «inputs», first, last, callers, window⟩ =>
    ⟨data, before, cells, flags, lower, upper, claim accepted «inputs» first last, callers, window⟩

example (claim : RVPreparedRoundCyclesSoundnessClaim) : RVPreparedRoundCyclesSoundnessSatisfiableClaim →
    ∃ (data : UnifiedReduced.Caller.RVRequestTrace babyBearModulus) (program : List UnifiedReduced.RVProgramEntry)
      (initial : RV.State) (cells : List Cell),
      RVCallerCycleEffects data program initial cells ∧ data.callers ≠ [] ∧ data.workers.rows ≠ [] :=
  fun ⟨data, program, initial, _, _, cells, _, _, accepted, «inputs», first, started, callers, rows⟩ =>
    ⟨data, program, initial, cells, claim accepted «inputs» first started, callers, rows⟩

end UnifiedCallers

example (claim : JumpBranchSlt.RVTraceSoundnessClaim) : JumpBranchSlt.RVTraceSoundnessSatisfiableClaim →
    ∃ (trace : JumpBranchSlt.NativeTrace babyBearModulus) (initial : RV.State) (cells : List Cell),
      RVRealizes trace initial cells ∧ trace.rows ≠ [] :=
  fun ⟨trace, initial, cells, _, «inputs», accepted, decoded, rows⟩ =>
    ⟨trace, initial, cells, claim «inputs» accepted decoded, rows⟩

example (claim : MulDiv.RVTraceSoundnessClaim) : MulDiv.RVTraceSoundnessSatisfiableClaim →
    ∃ (trace : MulDiv.NativeTrace babyBearModulus) (initial : RV.State) (cells : List Cell),
      RVRealizes trace initial cells ∧ trace.rows ≠ [] :=
  fun ⟨trace, initial, cells, _, «inputs», accepted, decoded, rows⟩ =>
    ⟨trace, initial, cells, claim «inputs» accepted decoded, rows⟩

example (claim : ShiftBinop.RVTraceSoundnessClaim) : ShiftBinop.RVTraceSoundnessSatisfiableClaim →
    ∃ (trace : ShiftBinop.NativeTrace babyBearModulus) (initial : RV.State) (cells : List Cell),
      RVRealizes trace initial cells ∧ trace.rows ≠ [] :=
  fun ⟨trace, initial, cells, _, «inputs», accepted, decoded, rows⟩ =>
    ⟨trace, initial, cells, claim «inputs» accepted decoded, rows⟩

example (claim : SubwordMemory.RVRamTraceSoundnessClaim) : SubwordMemory.RVRamTraceSoundnessSatisfiableClaim →
    ∃ (trace : SubwordMemory.NativeTrace babyBearModulus) (initial : RV.State) (cells : List Cell),
      RVRealizes trace initial cells ∧ trace.rows ≠ [] :=
  fun ⟨trace, initial, cells, _, «inputs», accepted, decoded, rows⟩ =>
    ⟨trace, initial, cells, claim «inputs» accepted decoded, rows⟩

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
  fun ⟨data, before, _, accepted, «inputs», callers⟩ => ⟨data, before, claim accepted «inputs», callers⟩

example (claim : RVRequestMemorySoundnessClaim) : RVRequestMemorySoundnessSatisfiableClaim →
    ∃ (data : RVRequestTrace babyBearModulus) (before : RV.State) (cells : List Cell),
      RVRequestExecution data before cells ∧ data.callers ≠ [] :=
  fun ⟨data, before, _, cells, accepted, «inputs», callers⟩ => ⟨data, before, cells, claim accepted «inputs», callers⟩

example (claim : RVOperationSoundnessClaim) : RVOperationSoundnessSatisfiableClaim →
    ∃ (data : RVRequestTrace babyBearModulus) (before : RV.State) (cells : List Cell),
      RVRequestOperationEffects data before cells ∧ data.callers ≠ [] :=
  fun ⟨data, before, _, cells, accepted, «inputs», callers⟩ => ⟨data, before, cells, claim accepted «inputs», callers⟩

example (claim : RVSharedMemorySoundnessClaim) : RVSharedMemorySoundnessSatisfiableClaim →
    ∃ (data : RVRequestTrace babyBearModulus) (before : RV.State) (cells : List Cell),
      RVSharedMemoryEffects data before cells ∧ data.callers ≠ [] :=
  fun ⟨data, before, _, cells, accepted, «inputs», callers⟩ => ⟨data, before, cells, claim accepted «inputs», callers⟩

example (claim : RVSharedOperationSoundnessClaim) : RVSharedOperationSoundnessSatisfiableClaim →
    ∃ (data : RVRequestTrace babyBearModulus) (before : RV.State) (cells : List Cell),
      RVSharedOperationEffects data before cells ∧ data.callers ≠ [] :=
  fun ⟨data, before, _, cells, accepted, «inputs», callers⟩ => ⟨data, before, cells, claim accepted «inputs», callers⟩

example (claim : RVMixedMemorySoundnessClaim) : RVMixedMemorySoundnessSatisfiableClaim →
    ∃ (data : RVRequestTrace babyBearModulus) (before : RV.State) (cells : List Cell),
      RVMixedMemoryEffects data before cells ∧ data.callers ≠ [] :=
  fun ⟨data, _, before, _, _, cells, accepted, «inputs», callers⟩ =>
    ⟨data, before, cells, claim accepted «inputs», callers⟩

example (claim : RVWorkerScheduleSoundnessClaim) : RVWorkerScheduleSoundnessSatisfiableClaim →
    ∃ data : RVRequestTrace babyBearModulus, RVWorkerSchedule data ∧ data.callers ≠ [] :=
  fun ⟨data, _, _, accepted, «inputs», callers⟩ => ⟨data, claim accepted «inputs», callers⟩

example (claim : RVRequestWindowSoundnessClaim) : RVRequestWindowSoundnessSatisfiableClaim →
    ∃ (data : RVRequestTrace babyBearModulus) (lower upper : Nat),
      RequestWindowBinding data.callers data.workers lower upper ∧ windowCallers data.callers lower upper ≠ [] :=
  fun ⟨data, _, _, lower, upper, accepted, «inputs», first, last, pastZero, window⟩ =>
    ⟨data, lower, upper, claim accepted «inputs» first last pastZero, window⟩

example (claim : Delegation.Caller.RVSharedSpanSoundnessClaim) :
    Delegation.Caller.RVSharedSpanSoundnessSatisfiableClaim →
    ∃ (data : Delegation.Caller.RVRequestTrace babyBearModulus) (before : RV.State) (cells : List Cell)
      (span : Delegation.Caller.HashSpan),
      Delegation.Caller.RVSharedSpanEffects data before cells span ∧ data.callers ≠ [] :=
  fun ⟨data, before, _, cells, span, accepted, «inputs», callers⟩ =>
    ⟨data, before, cells, span, claim accepted «inputs», callers⟩

example (claim : Delegation.Caller.RVRequestHashWindowSoundnessClaim) :
    Delegation.Caller.RVRequestHashWindowSoundnessSatisfiableClaim →
    ∃ (data : Delegation.Caller.RVRequestTrace babyBearModulus) (before : RV.State) (cells : List Cell)
      (span : Delegation.Caller.HashSpan) (lower upper : Nat),
      span.RVRequestWindowResult data.callers data.workers before cells lower upper ∧ data.callers ≠ [] ∧
        data.workers.windowRows lower upper ≠ [] :=
  fun ⟨data, before, _, cells, span, lower, upper, accepted, program, «inputs», aligned, first, last, past, callers,
      window⟩ =>
    ⟨data, before, cells, span, lower, upper, claim accepted program «inputs» aligned first last past, callers, window⟩

end Callers

example (claim : Blake2G.Native.RVWorkvectorSoundnessClaim) : Blake2G.Native.RVWorkvectorSoundnessSatisfiableClaim →
    ∃ (data : Delegation.MemoryData babyBearModulus) (initial after : RV.State) (cells : List Cell),
      Delegation.RVTraceMapping data initial after cells ∧ data.rows ≠ [] :=
  fun ⟨data, initial, cells, reduced, accepted, «inputs», aligned⟩ =>
    have ⟨after, _, _, _, _, _, _, trace, _⟩ := claim accepted «inputs» aligned
    ⟨data, initial, after, cells, trace, fun empty => by
      have calls := «inputs».calls
      rw [empty] at calls
      cases reduced <;> simp [Blake2G.callCount] at calls⟩

example (claim : Blake2G.Native.RVWorkvectorBoundarySoundnessClaim) :
    Blake2G.Native.RVWorkvectorBoundarySoundnessSatisfiableClaim →
    ∃ (data : Delegation.MemoryData babyBearModulus) (initial after : RV.State) (cells : List Cell),
      Delegation.RVTraceMapping data initial after cells ∧ data.rows ≠ [] :=
  fun ⟨data, initial, cells, reduced, accepted, «inputs», aligned⟩ =>
    have ⟨after, _, _, _, _, _, _, trace, _⟩ := claim accepted «inputs» aligned
    ⟨data, initial, after, cells, trace, fun empty => by
      have calls := «inputs».calls
      rw [empty] at calls
      cases reduced <;> simp [Blake2G.callCount] at calls⟩

example (claim : Blake2G.Native.RVWindowSoundnessClaim) : Blake2G.Native.RVWindowSoundnessSatisfiableClaim →
    ∃ (data : Delegation.MemoryData babyBearModulus) (before : RV.State) (cells : List Cell) (reduced : Bool)
      (lower upper : Nat), Delegation.Caller.RVWindowResult (Blake2G.RVSpanResult reduced) data before cells lower upper ∧
        data.windowRows lower upper ≠ [] :=
  fun ⟨data, before, cells, reduced, lower, upper, accepted, «inputs», aligned⟩ =>
    ⟨data, before, cells, reduced, lower, upper, claim accepted «inputs» aligned, fun empty => by
      have calls := «inputs».calls
      rw [empty] at calls
      cases reduced <;> simp [Blake2G.callCount] at calls⟩

example (claim : Keccak.Split.Native.RVPermutationSoundnessClaim) :
    Keccak.Split.Native.RVPermutationSoundnessSatisfiableClaim →
    ∃ (data : Keccak.Split.Native.MemoryData babyBearModulus) (initial after : RV.State) (cells : List Cell),
      Keccak.Split.Native.RVTraceMapping data initial after cells ∧ data.rows ≠ [] :=
  fun ⟨data, initial, cells, accepted, «inputs», aligned⟩ =>
    have ⟨states, _, _, _, _, _, _, trace, _⟩ := claim accepted «inputs» aligned
    ⟨data, initial, states 361, cells, trace, fun empty => by
      have calls := «inputs».calls
      rw [empty] at calls
      simp at calls⟩

example (claim : Keccak.Native.RVPermutationSoundnessClaim) : Keccak.Native.RVPermutationSoundnessSatisfiableClaim →
    ∃ (data : Delegation.MemoryData babyBearModulus) (initial after : RV.State) (cells : List Cell),
      Delegation.RVTraceMapping data initial after cells ∧ data.rows ≠ [] :=
  fun ⟨data, initial, cells, accepted, «inputs», tables, aligned⟩ =>
    have ⟨after, _, _, _, _, trace, _⟩ := claim accepted «inputs» tables aligned
    ⟨data, initial, after, cells, trace, fun empty => by
      have calls := «inputs».calls
      rw [empty] at calls
      simp at calls⟩

example (claim : Keccak.Native.RVPermutationBoundarySoundnessClaim) :
    Keccak.Native.RVPermutationBoundarySoundnessSatisfiableClaim →
    ∃ (data : Delegation.MemoryData babyBearModulus) (initial after : RV.State) (cells : List Cell),
      Delegation.RVTraceMapping data initial after cells ∧ data.rows ≠ [] :=
  fun ⟨data, initial, cells, accepted, «inputs», tables, aligned⟩ =>
    have ⟨after, _, _, _, _, trace, _⟩ := claim accepted «inputs» tables aligned
    ⟨data, initial, after, cells, trace, fun empty => by
      have calls := «inputs».calls
      rw [empty] at calls
      simp at calls⟩

example (claim : Keccak.Native.RVWindowSoundnessClaim) : Keccak.Native.RVWindowSoundnessSatisfiableClaim →
    ∃ (data : Delegation.MemoryData babyBearModulus) (before : RV.State) (cells : List Cell) (lower upper : Nat),
      Delegation.Caller.RVWindowResult Keccak.RVSpanResult data before cells lower upper ∧
        data.windowRows lower upper ≠ [] :=
  fun ⟨data, before, cells, lower, upper, accepted, «inputs», aligned⟩ =>
    ⟨data, before, cells, lower, upper, claim accepted «inputs» aligned, fun empty => by
      have calls := «inputs».calls
      rw [empty] at calls
      simp at calls⟩

example (claim : Blake2Round.Native.RVCompressionSoundnessClaim) :
    Blake2Round.Native.RVCompressionSoundnessSatisfiableClaim →
    ∃ (data : Delegation.MemoryData babyBearModulus) (initial after : RV.State) (cells : List Cell),
      Delegation.RVTraceMapping data initial after cells ∧ data.rows ≠ [] :=
  fun ⟨data, initial, cells, flags, accepted, «inputs», aligned⟩ =>
    have ⟨after, _, _, _, _, _, _, trace, _⟩ := claim accepted «inputs» aligned
    ⟨data, initial, after, cells, trace, fun empty => by
      have calls := «inputs».calls
      rw [empty] at calls
      split at calls <;> simp at calls⟩

example (claim : Blake2Round.Native.RVCompressionBoundarySoundnessClaim) :
    Blake2Round.Native.RVCompressionBoundarySoundnessSatisfiableClaim →
    ∃ (data : Delegation.MemoryData babyBearModulus) (initial after : RV.State) (cells : List Cell),
      Delegation.RVTraceMapping data initial after cells ∧ data.rows ≠ [] :=
  fun ⟨data, initial, cells, flags, accepted, «inputs», aligned⟩ =>
    have ⟨after, _, _, _, _, _, _, trace, _⟩ := claim accepted «inputs» aligned
    ⟨data, initial, after, cells, trace, fun empty => by
      have calls := «inputs».calls
      rw [empty] at calls
      split at calls <;> simp at calls⟩

example (claim : Blake2Round.Native.RVWindowSoundnessClaim) : Blake2Round.Native.RVWindowSoundnessSatisfiableClaim →
    ∃ (data : Delegation.MemoryData babyBearModulus) (before : RV.State) (cells : List Cell) (flags : Fin 8)
      (lower upper : Nat),
      Delegation.Caller.RVWindowResult (Blake2Round.RVSpanResult flags) data before cells lower upper ∧
        data.windowRows lower upper ≠ [] :=
  fun ⟨data, before, cells, flags, lower, upper, accepted, «inputs», aligned⟩ =>
    ⟨data, before, cells, flags, lower, upper, claim accepted «inputs» aligned, fun empty => by
      have calls := «inputs».calls
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
      (ZMod Airbender.babyBearModulus))
      (witness : Airbender.InitsTeardowns.Witness Airbender.babyBearModulus Airbender.InitsTeardowns.importedLayout)
      (wires : Airbender.InitsTeardowns.Native.Wires (ZMod Airbender.babyBearModulus)),
      Airbender.InitsTeardowns.Native.Accepted Airbender.InitsTeardowns.Native.standaloneArtifact parameters (Airbender.InitsTeardowns.Native.memoryBank 0 witness) wires ∧
      Airbender.InitsTeardowns.Native.rootProduct Airbender.InitsTeardowns.Native.standaloneArtifact
        Airbender.InitsTeardowns.Native.standaloneArtifact.terminal wires = (witness.teardownTokens.map parameters.encode).prod := by
  obtain ⟨parameters, witness, wires, windows, checked, accepted⟩ := satisfiable
  exact ⟨parameters, witness, wires, accepted, (claim parameters witness wires windows checked accepted).1⟩

example (claim : Airbender.InitsTeardowns.Native.UnifiedSoundnessClaim)
    (satisfiable : Airbender.InitsTeardowns.Native.UnifiedSatisfiableClaim) :
    ∃ (parameters : Airbender.InitsTeardowns.Native.Parameters Airbender.babyBearModulus
      (ZMod Airbender.babyBearModulus))
      (witness : Airbender.InitsTeardowns.Witness Airbender.babyBearModulus Airbender.InitsTeardowns.unifiedLayout)
      (wires : Airbender.InitsTeardowns.Native.Wires (ZMod Airbender.babyBearModulus)),
      Airbender.InitsTeardowns.Native.Accepted Airbender.InitsTeardowns.Native.unifiedArtifact parameters (Airbender.InitsTeardowns.Native.memoryBank 96 witness) wires ∧
      Airbender.InitsTeardowns.Native.rootProduct Airbender.InitsTeardowns.Native.unifiedArtifact
        Airbender.InitsTeardowns.Native.unifiedArtifact.terminal wires = (witness.teardownTokens.map parameters.encode).prod := by
  obtain ⟨parameters, witness, wires, windows, checked, accepted⟩ := satisfiable
  exact ⟨parameters, witness, wires, accepted, (claim parameters witness wires windows checked accepted).1⟩

example (claim : Airbender.Blake2Round.Mask.SoundnessClaim)
    (witness : Airbender.Blake2Round.Mask.SatisfiableClaim) :
    ∃ (input : Airbender.Blake2Round.Mask.Input) (output : Airbender.Blake2Round.Mask.Output)
      (w : Nat → ZMod Airbender.babyBearModulus),
      Airbender.Blake2Round.Mask.Assumptions input ∧ Airbender.Blake2Round.Mask.Mapping input output w ∧
      Airbender.Blake2Round.Mask.spec input output := by
  obtain ⟨input, output, w, assumptions, constraints, mapping, _⟩ := witness
  exact ⟨input, output, w, assumptions, mapping, claim input output w assumptions constraints mapping⟩

example : Airbender.Compiler.NativeLookups.CachedLookupSelectorsSatisfiableClaim := Airbender.Compiler.NativeLookups.cached_lookup_selectors_satisfiable

example : Airbender.DecodeIsSailSatisfiableClaim := Airbender.decode_is_sail_satisfiable
example : Airbender.StepIsAirbenderSatisfiableClaim := Airbender.step_is_airbender_satisfiable

example : Airbender.RunIsAirbenderSatisfiableClaim := Airbender.run_is_airbender_satisfiable

example : Airbender.AgreeExistsSatisfiableClaim := Airbender.agree_exists_satisfiable

example : Airbender.FetchKeepsConfiguredSatisfiableClaim := Airbender.fetch_keeps_configured_satisfiable

example : Airbender.Bigint.Memory.RVAddressesSoundnessSatisfiableClaim := Airbender.Bigint.Memory.rv_addresses_soundness_satisfiable

example : Airbender.Blake2G.SoundnessSatisfiableClaim := Airbender.Blake2G.soundness_satisfiable

example : Airbender.PCState.OutgoingBoundsSatisfiableClaim := Airbender.PCState.outgoing_bounds_satisfiable

example : Airbender.Compiler.AddSubCachedArithmeticSatisfiableClaim := Airbender.Compiler.addSub_cached_arithmetic_satisfiable

example : Airbender.Compiler.BigintCachedArithmeticSatisfiableClaim := Airbender.Compiler.bigint_cached_arithmetic_satisfiable

example : Airbender.Compiler.BlakeGCachedArithmeticSatisfiableClaim := Airbender.Compiler.blakeG_cached_arithmetic_satisfiable

example : Airbender.Compiler.BlakeRoundCachedArithmeticSatisfiableClaim := Airbender.Compiler.blakeRound_cached_arithmetic_satisfiable

example : Airbender.Compiler.JumpBranchCachedArithmeticSatisfiableClaim := Airbender.Compiler.jumpBranch_cached_arithmetic_satisfiable

example : Airbender.Compiler.KeccakCachedArithmeticSatisfiableClaim := Airbender.Compiler.keccak_cached_arithmetic_satisfiable

example : Airbender.Compiler.MulDivCachedArithmeticSatisfiableClaim := Airbender.Compiler.mulDiv_cached_arithmetic_satisfiable

example : Airbender.Compiler.ShiftBinopCachedArithmeticSatisfiableClaim := Airbender.Compiler.shiftBinop_cached_arithmetic_satisfiable

example : Airbender.Compiler.SubwordMemoryCachedArithmeticSatisfiableClaim := Airbender.Compiler.subwordMemory_cached_arithmetic_satisfiable

example : Airbender.Compiler.UnifiedCachedArithmeticSatisfiableClaim := Airbender.Compiler.unified_cached_arithmetic_satisfiable

example : Airbender.Compiler.WordMemoryCachedArithmeticSatisfiableClaim := Airbender.Compiler.wordMemory_cached_arithmetic_satisfiable

example : RV.CallsRunSatisfiableClaim := RV.calls_run_satisfiable

example : RV.BlakeCompressRunSatisfiableClaim := RV.blake_compress_run_satisfiable

example : RV.BlakeHashRunSatisfiableClaim := RV.blake_hash_run_satisfiable

example : RV.BlakeCompressRun10SatisfiableClaim := RV.blake_compress_run10_satisfiable

example : RV.BlakeHashRun10SatisfiableClaim := RV.blake_hash_run10_satisfiable

example : RV.BlakeGRunSatisfiableClaim := RV.blake_g_run_satisfiable

example : RV.BlakeGRun10SatisfiableClaim := RV.blake_g_run10_satisfiable

example : RV.KeccakSpecial5RunSatisfiableClaim := RV.keccak_special5_run_satisfiable

example : RV.KeccakF1600RunSatisfiableClaim := RV.keccak_f1600_run_satisfiable

example : Airbender.Trace.Machine.Native.UnrolledFullFromNativeSatisfiableClaim := Airbender.Trace.Machine.Native.unrolled_full_from_native_satisfiable

example : Airbender.Trace.Machine.Native.UnrolledReducedFromNativeSatisfiableClaim := Airbender.Trace.Machine.Native.unrolled_reduced_from_native_satisfiable

example : Airbender.Trace.Machine.Native.UnifiedFromNativeSatisfiableClaim := Airbender.Trace.Machine.Native.unified_from_native_satisfiable

example : Airbender.PaddingBoundary.ContributionSatisfiableClaim := Airbender.PaddingBoundary.contribution_satisfiable

example : RV.ValidUse.BigintReferenceSatisfiableClaim := RV.ValidUse.bigint_reference_satisfiable

example : RV.ValidUse.GReferenceSatisfiableClaim := RV.ValidUse.g_reference_satisfiable

example : RV.ValidUse.RoundReferenceSatisfiableClaim := RV.ValidUse.round_reference_satisfiable

example : RV.ValidUse.HashReferenceSatisfiableClaim := RV.ValidUse.hash_reference_satisfiable

example : RV.ValidUse.SplitKeccakReferenceSatisfiableClaim := RV.ValidUse.split_keccak_reference_satisfiable

example : RV.ValidUse.Special5ReferenceSatisfiableClaim := RV.ValidUse.special5_reference_satisfiable

namespace Airbender.Trace.Machine
open Airbender.Compiler

example (claim : Airbender.Trace.Machine.UnrolledFullUnsigned) : Airbender.Trace.Machine.UnrolledFullUnsignedSatisfiableClaim →
  ∃ (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)),
    trace.rows ≠ [] ∧ trace.rows.length = 1 ∧
    BootInputs .unrolledFullUnsigned trace initial cells program InitsTeardowns.importedLayout inits ∧
    trace.rom.wordMemory = ROM.table cells (romImageRV initial cells) ∧
    trace.rom.subwordMemory = Verification.subwordTable (ROM.wordsRV initial) ∧
    workers.standard.setup = Delegation.modeledSetup Keccak.Controller.rows ∧
    NoSpecial5 program ∧
    NonDeterminism.Pooled.StreamPorts trace initial.input ∧
    UnrolledAcceptance trace workers program ∧
    (RVRealizes trace initial cells (NonDeterminism.Pooled.readCount trace)) :=
  fun ⟨trace, workers, initial, cells, program, inits, premise0, premise1, premise2, premise3, premise4, premise5, premise6, rows_nonempty, row_count⟩ =>
    ⟨trace, workers, initial, cells, program, inits, rows_nonempty, row_count, premise0, premise1, premise2, premise3, premise4, premise5, premise6, claim trace workers initial cells program inits premise0 premise1 premise2 premise3 premise4 premise5 premise6⟩

example (claim : Airbender.Trace.Machine.UnrolledReduced) : Airbender.Trace.Machine.UnrolledReducedSatisfiableClaim →
  ∃ (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)),
    trace.rows ≠ [] ∧ trace.rows.length = 1 ∧
    BootInputs .unrolledReduced trace initial cells program InitsTeardowns.importedLayout inits ∧
    trace.rom.wordMemory = ROM.table cells (romImageRV initial cells) ∧
    trace.rom.subwordMemory = Verification.subwordTable (ROM.wordsRV initial) ∧
    workers.standard.setup = Delegation.modeledSetup Keccak.Controller.rows ∧
    NonDeterminism.Pooled.StreamPorts trace initial.input ∧
    UnrolledAcceptance trace workers program ∧
    (RVRealizes trace initial cells (NonDeterminism.Pooled.readCount trace)) :=
  fun ⟨trace, workers, initial, cells, program, inits, premise0, premise1, premise2, premise3, premise4, premise5, rows_nonempty, row_count⟩ =>
    ⟨trace, workers, initial, cells, program, inits, rows_nonempty, row_count, premise0, premise1, premise2, premise3, premise4, premise5, claim trace workers initial cells program inits premise0 premise1 premise2 premise3 premise4 premise5⟩

example (claim : Airbender.Trace.Machine.Unified) : Airbender.Trace.Machine.UnifiedSatisfiableClaim →
  ∃ (trace : UnifiedTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.unifiedLayout)),
    BootInputs .unified trace initial cells program InitsTeardowns.unifiedLayout inits ∧
    trace.rom = UnifiedReduced.Setup.tableRV initial ∧
    workers.standard.setup = Delegation.modeledSetup Keccak.Controller.rows ∧
    NoSpecial5 program ∧ UnifiedStreamPorts trace initial.input ∧
    UnifiedAcceptance trace workers program ∧
    (RVRealizes trace initial cells (unifiedReadCount trace)) :=
  fun ⟨trace, workers, initial, cells, program, inits, premise0, premise1, premise2, premise3, premise4, premise5⟩ =>
    ⟨trace, workers, initial, cells, program, inits, premise0, premise1, premise2, premise3, premise4, premise5, claim trace workers initial cells program inits premise0 premise1 premise2 premise3 premise4 premise5⟩

end Airbender.Trace.Machine


namespace Airbender.Trace.Machine
open Airbender.Compiler

example (claim : Airbender.Trace.Machine.PaddedUnrolledFullUnsigned) : Airbender.Trace.Machine.PaddedUnrolledFullUnsignedSatisfiableClaim →
  ∃ (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)),
    trace.rows ≠ [] ∧ trace.rows.length = 2 ∧
    (PaddingBoundary.active trace).rows.length = 1 ∧ (PaddingBoundary.inactive trace).rows.length = 1 ∧
    BootInputs .unrolledFullUnsigned (PaddingBoundary.active trace) initial cells program InitsTeardowns.importedLayout inits ∧
    trace.rom.wordMemory = ROM.table cells (romImageRV initial cells) ∧
    trace.rom.subwordMemory = Verification.subwordTable (ROM.wordsRV initial) ∧
    workers.standard.setup = Delegation.modeledSetup Keccak.Controller.rows ∧
    NoSpecial5 program ∧
    NonDeterminism.Pooled.StreamPorts (PaddingBoundary.active trace) initial.input ∧
    MaskedUnrolledAcceptance trace workers program ∧
    (RVRealizes trace initial cells (NonDeterminism.Pooled.readCount (PaddingBoundary.active trace))) :=
  fun ⟨trace, workers, initial, cells, program, inits, premise0, premise1, premise2, premise3, premise4, premise5, premise6, rows_nonempty, row_count, active_count, padding_count⟩ =>
    ⟨trace, workers, initial, cells, program, inits, rows_nonempty, row_count, active_count, padding_count, premise0, premise1, premise2, premise3, premise4, premise5, premise6, claim trace workers initial cells program inits premise0 premise1 premise2 premise3 premise4 premise5 premise6⟩

example (claim : Airbender.Trace.Machine.PaddedUnrolledReduced) : Airbender.Trace.Machine.PaddedUnrolledReducedSatisfiableClaim →
  ∃ (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)),
    trace.rows ≠ [] ∧ trace.rows.length = 2 ∧
    (PaddingBoundary.active trace).rows.length = 1 ∧ (PaddingBoundary.inactive trace).rows.length = 1 ∧
    BootInputs .unrolledReduced (PaddingBoundary.active trace) initial cells program InitsTeardowns.importedLayout inits ∧
    trace.rom.wordMemory = ROM.table cells (romImageRV initial cells) ∧
    trace.rom.subwordMemory = Verification.subwordTable (ROM.wordsRV initial) ∧
    workers.standard.setup = Delegation.modeledSetup Keccak.Controller.rows ∧
    NonDeterminism.Pooled.StreamPorts (PaddingBoundary.active trace) initial.input ∧
    MaskedUnrolledAcceptance trace workers program ∧
    (RVRealizes trace initial cells (NonDeterminism.Pooled.readCount (PaddingBoundary.active trace))) :=
  fun ⟨trace, workers, initial, cells, program, inits, premise0, premise1, premise2, premise3, premise4, premise5, rows_nonempty, row_count, active_count, padding_count⟩ =>
    ⟨trace, workers, initial, cells, program, inits, rows_nonempty, row_count, active_count, padding_count, premise0, premise1, premise2, premise3, premise4, premise5, claim trace workers initial cells program inits premise0 premise1 premise2 premise3 premise4 premise5⟩

example (claim : Airbender.Trace.Machine.PaddedUnified) : Airbender.Trace.Machine.PaddedUnifiedSatisfiableClaim →
  ∃ (trace : UnifiedTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.unifiedLayout)),
    trace.rows ≠ [] ∧ trace.rows.length = 2 ∧
    (PaddingBoundary.active trace).rows.length = 1 ∧ (PaddingBoundary.inactive trace).rows.length = 1 ∧
    BootInputs .unified (PaddingBoundary.active trace) initial cells program InitsTeardowns.unifiedLayout inits ∧
    trace.rom = UnifiedReduced.Setup.tableRV initial ∧
    workers.standard.setup = Delegation.modeledSetup Keccak.Controller.rows ∧
    NoSpecial5 program ∧ UnifiedStreamPorts (PaddingBoundary.active trace) initial.input ∧
    MaskedUnifiedAcceptance trace workers program ∧
    (RVRealizes trace initial cells (unifiedReadCount (PaddingBoundary.active trace))) :=
  fun ⟨trace, workers, initial, cells, program, inits, premise0, premise1, premise2, premise3, premise4, premise5, rows_nonempty, row_count, active_count, padding_count⟩ =>
    ⟨trace, workers, initial, cells, program, inits, rows_nonempty, row_count, active_count, padding_count, premise0, premise1, premise2, premise3, premise4, premise5, claim trace workers initial cells program inits premise0 premise1 premise2 premise3 premise4 premise5⟩

end Airbender.Trace.Machine


namespace Airbender.Trace.Machine
open Airbender.Compiler

example (claim : Airbender.Trace.Machine.UnrolledHashSegmentationClaim) : Airbender.Trace.Machine.UnrolledHashSegmentationSatisfiableClaim →
  ∃ (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (program : List RVMachineProgramEntry) (windows : List HashWindow),
    trace.rows ≠ [] ∧ trace.rows.length = 10 ∧ workers.standard.rows.length = 10 ∧
    workers.split.rows = [] ∧ windows ≠ [] ∧ windows.length = 1 ∧
    UnrolledAcceptance trace workers program ∧
    (timeOfPair trace.initial.timestamp).Bounded ∧ (timeOfPair trace.initial.timestamp).value % 4 = 0 ∧
    HashWindowProfile ((unrolledCallers trace).map fun row => Delegation.Requests.caller row.assignment) windows ∧
    (IssuedHashSegmentation workers.fulfillments windows) :=
  fun ⟨trace, workers, program, windows, premise0, premise1, premise2, premise3, rows_nonempty, row_count, worker_count, split_rows, windows_nonempty, window_count⟩ =>
    ⟨trace, workers, program, windows, rows_nonempty, row_count, worker_count, split_rows, windows_nonempty, window_count, premise0, premise1, premise2, premise3, claim trace workers program windows premise0 premise1 premise2 premise3⟩

example (claim : Airbender.Trace.Machine.UnifiedHashSegmentationClaim) : Airbender.Trace.Machine.UnifiedHashSegmentationSatisfiableClaim →
  ∃ (trace : UnifiedTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (program : List RVMachineProgramEntry) (windows : List HashWindow),
    trace.rows ≠ [] ∧ trace.rows.length = 10 ∧ workers.standard.rows.length = 10 ∧
    workers.split.rows = [] ∧ windows ≠ [] ∧ windows.length = 1 ∧
    UnifiedAcceptance trace workers program ∧
    (timeOfPair trace.initial.timestamp).Bounded ∧ (timeOfPair trace.initial.timestamp).value % 4 = 0 ∧
    HashWindowProfile ((trace.rows.filter fun row => decide (UnifiedReduced.Caller.Selected row.assignment)).map
      fun row => UnifiedReduced.Caller.request row.assignment) windows ∧
    (IssuedHashSegmentation workers.fulfillments windows) :=
  fun ⟨trace, workers, program, windows, premise0, premise1, premise2, premise3, rows_nonempty, row_count, worker_count, split_rows, windows_nonempty, window_count⟩ =>
    ⟨trace, workers, program, windows, rows_nonempty, row_count, worker_count, split_rows, windows_nonempty, window_count, premise0, premise1, premise2, premise3, claim trace workers program windows premise0 premise1 premise2 premise3⟩

end Airbender.Trace.Machine


namespace Airbender.Trace.Machine
open Airbender.Compiler

example (claim : Airbender.Trace.Machine.UnrolledCodeHashSegmentationClaim) : Airbender.Trace.Machine.UnrolledCodeHashSegmentationSatisfiableClaim →
  ∃ (config : RVMachineConfig) (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (addresses : List (BitVec 32))
    (program : List RVMachineProgramEntry) (windows : List HashWindow),
    trace.rows ≠ [] ∧ trace.rows.length = 10 ∧ workers.standard.rows.length = 10 ∧
    workers.split.rows = [] ∧ windows ≠ [] ∧ windows.length = 1 ∧
    config ≠ .unified ∧ rvMachineProgramImage config initial addresses = some program ∧
    UnrolledAcceptance trace workers program ∧
    (timeOfPair trace.initial.timestamp).Bounded ∧ (timeOfPair trace.initial.timestamp).value % 4 = 0 ∧
    windows.Pairwise (fun first second => first.upper ≤ second.lower) ∧
    (∀ request ∈ (unrolledCallers trace).map (fun row => Delegation.Requests.caller row.assignment),
      request.csr ≠ Delegation.Requests.csr .bigint ↔ ∃ window ∈ windows, window.select request = true) ∧
    (∀ window ∈ windows, CodeWindowScope trace program window) ∧
    (IssuedHashSegmentation workers.fulfillments windows) :=
  fun ⟨config, trace, workers, initial, addresses, program, windows, premise0, premise1, premise2, premise3, premise4, premise5, premise6, premise7, rows_nonempty, row_count, worker_count, split_rows, windows_nonempty, window_count⟩ =>
    ⟨config, trace, workers, initial, addresses, program, windows, rows_nonempty, row_count, worker_count, split_rows, windows_nonempty, window_count, premise0, premise1, premise2, premise3, premise4, premise5, premise6, premise7, claim config trace workers initial addresses program windows premise0 premise1 premise2 premise3 premise4 premise5 premise6 premise7⟩

example (claim : Airbender.Trace.Machine.UnifiedCodeHashSegmentationClaim) : Airbender.Trace.Machine.UnifiedCodeHashSegmentationSatisfiableClaim →
  ∃ (trace : UnifiedTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (addresses : List (BitVec 32))
    (program : List RVMachineProgramEntry) (windows : List HashWindow),
    trace.rows ≠ [] ∧ trace.rows.length = 10 ∧ workers.standard.rows.length = 10 ∧
    workers.split.rows = [] ∧ windows ≠ [] ∧ windows.length = 1 ∧
    rvMachineProgramImage .unified initial addresses = some program ∧ UnifiedAcceptance trace workers program ∧
    (timeOfPair trace.initial.timestamp).Bounded ∧ (timeOfPair trace.initial.timestamp).value % 4 = 0 ∧
    windows.Pairwise (fun first second => first.upper ≤ second.lower) ∧
    (∀ request ∈ (trace.rows.filter (fun row => decide (UnifiedReduced.Caller.Selected row.assignment))).map
      (fun row => UnifiedReduced.Caller.request row.assignment),
      request.csr ≠ Delegation.Requests.csr .bigint ↔ ∃ window ∈ windows, window.select request = true) ∧
    (∀ window ∈ windows, CodeWindowScope trace program window) ∧
    (IssuedHashSegmentation workers.fulfillments windows) :=
  fun ⟨trace, workers, initial, addresses, program, windows, premise0, premise1, premise2, premise3, premise4, premise5, premise6, rows_nonempty, row_count, worker_count, split_rows, windows_nonempty, window_count⟩ =>
    ⟨trace, workers, initial, addresses, program, windows, rows_nonempty, row_count, worker_count, split_rows, windows_nonempty, window_count, premise0, premise1, premise2, premise3, premise4, premise5, premise6, claim trace workers initial addresses program windows premise0 premise1 premise2 premise3 premise4 premise5 premise6⟩

end Airbender.Trace.Machine


namespace Airbender.Trace.Machine
open Airbender.Compiler

example (claim : Airbender.Trace.Machine.UnrolledFullUnsignedSailClaim) : Airbender.Trace.Machine.UnrolledFullUnsignedSailSatisfiableClaim →
  ∃ (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)),
    trace.rows ≠ [] ∧ trace.rows.length = 1 ∧
    BootInputs .unrolledFullUnsigned trace initial cells program InitsTeardowns.importedLayout inits ∧
    trace.rom.wordMemory = ROM.table cells (romImageRV initial cells) ∧
    trace.rom.subwordMemory = Verification.subwordTable (ROM.wordsRV initial) ∧
    workers.standard.setup = Delegation.modeledSetup Keccak.Controller.rows ∧
    NoSpecial5 program ∧
    NonDeterminism.Pooled.StreamPorts trace initial.input ∧
    UnrolledAcceptance trace workers program ∧
    (SailRealizes trace initial cells (NonDeterminism.Pooled.readCount trace)) :=
  fun ⟨trace, workers, initial, cells, program, inits, premise0, premise1, premise2, premise3, premise4, premise5, premise6, rows_nonempty, row_count⟩ =>
    ⟨trace, workers, initial, cells, program, inits, rows_nonempty, row_count, premise0, premise1, premise2, premise3, premise4, premise5, premise6, claim trace workers initial cells program inits premise0 premise1 premise2 premise3 premise4 premise5 premise6⟩

example (claim : Airbender.Trace.Machine.UnrolledReducedSailClaim) : Airbender.Trace.Machine.UnrolledReducedSailSatisfiableClaim →
  ∃ (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)),
    trace.rows ≠ [] ∧ trace.rows.length = 1 ∧
    BootInputs .unrolledReduced trace initial cells program InitsTeardowns.importedLayout inits ∧
    trace.rom.wordMemory = ROM.table cells (romImageRV initial cells) ∧
    trace.rom.subwordMemory = Verification.subwordTable (ROM.wordsRV initial) ∧
    workers.standard.setup = Delegation.modeledSetup Keccak.Controller.rows ∧
    NonDeterminism.Pooled.StreamPorts trace initial.input ∧
    UnrolledAcceptance trace workers program ∧
    (SailRealizes trace initial cells (NonDeterminism.Pooled.readCount trace)) :=
  fun ⟨trace, workers, initial, cells, program, inits, premise0, premise1, premise2, premise3, premise4, premise5, rows_nonempty, row_count⟩ =>
    ⟨trace, workers, initial, cells, program, inits, rows_nonempty, row_count, premise0, premise1, premise2, premise3, premise4, premise5, claim trace workers initial cells program inits premise0 premise1 premise2 premise3 premise4 premise5⟩

example (claim : Airbender.Trace.Machine.UnifiedSailClaim) : Airbender.Trace.Machine.UnifiedSailSatisfiableClaim →
  ∃ (trace : UnifiedTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.unifiedLayout)),
    BootInputs .unified trace initial cells program InitsTeardowns.unifiedLayout inits ∧
    trace.rom = UnifiedReduced.Setup.tableRV initial ∧
    workers.standard.setup = Delegation.modeledSetup Keccak.Controller.rows ∧
    NoSpecial5 program ∧ UnifiedStreamPorts trace initial.input ∧
    UnifiedAcceptance trace workers program ∧
    (SailRealizes trace initial cells (unifiedReadCount trace)) :=
  fun ⟨trace, workers, initial, cells, program, inits, premise0, premise1, premise2, premise3, premise4, premise5⟩ =>
    ⟨trace, workers, initial, cells, program, inits, premise0, premise1, premise2, premise3, premise4, premise5, claim trace workers initial cells program inits premise0 premise1 premise2 premise3 premise4 premise5⟩

end Airbender.Trace.Machine


namespace Airbender.Trace.Machine.Native
open Airbender.Compiler

example (claim : Airbender.Trace.Machine.Native.UnrolledFullFromNativeSailClaim) : Airbender.Trace.Machine.Native.UnrolledFullFromNativeSailSatisfiableClaim →
  ∃ (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)) (tables : ProgramLookupRows),
    BootInputs .unrolledFullUnsigned trace initial cells program InitsTeardowns.importedLayout inits ∧
    NoSpecial5 program ∧
    NonDeterminism.Pooled.StreamPorts trace initial.input ∧
    NativePublicSetup.Bound initial program tables ∧ NativePublicSetup.CoversROM cells ∧
    ∃ certificates : List (ProgramLogicalRowCertificate tables),
      UnrolledNativeArguments tables certificates trace workers ∧
    (SailRealizes trace initial cells (NonDeterminism.Pooled.readCount trace)) :=
  fun ⟨trace, workers, initial, cells, program, inits, tables, premise0, premise1, premise2, premise3, premise4, certificates, premise5⟩ =>
    ⟨trace, workers, initial, cells, program, inits, tables, premise0, premise1, premise2, premise3, premise4, certificates, premise5, claim trace workers initial cells program inits tables premise0 premise1 premise2 premise3 premise4 certificates premise5⟩

example (claim : Airbender.Trace.Machine.Native.UnrolledReducedFromNativeSailClaim) : Airbender.Trace.Machine.Native.UnrolledReducedFromNativeSailSatisfiableClaim →
  ∃ (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)) (tables : ProgramLookupRows),
    BootInputs .unrolledReduced trace initial cells program InitsTeardowns.importedLayout inits ∧
    NonDeterminism.Pooled.StreamPorts trace initial.input ∧
    NativePublicSetup.Bound initial program tables ∧ NativePublicSetup.CoversROM cells ∧
    ∃ certificates : List (ProgramLogicalRowCertificate tables),
      UnrolledNativeArguments tables certificates trace workers ∧
    (SailRealizes trace initial cells (NonDeterminism.Pooled.readCount trace)) :=
  fun ⟨trace, workers, initial, cells, program, inits, tables, premise0, premise1, premise2, premise3, certificates, premise4⟩ =>
    ⟨trace, workers, initial, cells, program, inits, tables, premise0, premise1, premise2, premise3, certificates, premise4, claim trace workers initial cells program inits tables premise0 premise1 premise2 premise3 certificates premise4⟩

example (claim : Airbender.Trace.Machine.Native.UnifiedFromNativeSailClaim) : Airbender.Trace.Machine.Native.UnifiedFromNativeSailSatisfiableClaim →
  ∃ (trace : UnifiedTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.unifiedLayout)) (tables : ProgramLookupRows),
    BootInputs .unified trace initial cells program InitsTeardowns.unifiedLayout inits ∧
    NoSpecial5 program ∧ UnifiedStreamPorts trace initial.input ∧
    NativePublicSetup.Bound initial program tables ∧
    ∃ certificates : List (UnifiedLogicalRowCertificate tables),
      UnifiedNativeArguments tables certificates trace workers ∧
    (SailRealizes trace initial cells (unifiedReadCount trace)) :=
  fun ⟨trace, workers, initial, cells, program, inits, tables, premise0, premise1, premise2, premise3, certificates, premise4⟩ =>
    ⟨trace, workers, initial, cells, program, inits, tables, premise0, premise1, premise2, premise3, certificates, premise4, claim trace workers initial cells program inits tables premise0 premise1 premise2 premise3 certificates premise4⟩

end Airbender.Trace.Machine.Native

example (claim : Airbender.Bigint.Memory.RVAddressesSoundnessClaim) :
    Airbender.Bigint.Memory.RVAddressesSoundnessSatisfiableClaim →
    ∃ (input : Airbender.Bigint.Addresses.Input) (output : Airbender.Bigint.Addresses.Output),
      Airbender.Bigint.Addresses.spec input output :=
  fun ⟨data, before, cells, input, output, assignment, assumptions, accepted⟩ =>
    ⟨input, output, claim data before cells input output assignment ⟨assumptions, accepted⟩⟩

example (claim : Airbender.Blake2G.SoundnessClaim) : Airbender.Blake2G.SoundnessSatisfiableClaim →
    ∃ (input : Airbender.Blake2G.Input) (output : Airbender.Blake2G.Words),
      Airbender.Blake2G.spec input output :=
  fun ⟨control, input, output, assignment, assumptions, accepted⟩ =>
    ⟨input, output, claim control input output assignment ⟨assumptions, accepted⟩⟩

example (claim : Airbender.Blake2Round.Mask.SoundnessClaim) : Airbender.Blake2Round.Mask.SatisfiableClaim →
    ∃ (input : Airbender.Blake2Round.Mask.Input) (output : Airbender.Blake2Round.Mask.Output),
      Airbender.Blake2Round.Mask.spec input output :=
  fun ⟨input, output, assignment, assumptions, accepted, mapping, _⟩ =>
    ⟨input, output, claim input output assignment assumptions accepted mapping⟩

example (claim : Airbender.PCState.OutgoingBoundsClaim) : Airbender.PCState.OutgoingBoundsSatisfiableClaim →
    ∃ pc : ZMod babyBearModulus × ZMod babyBearModulus,
      pc ≠ PCState.encode 0 ∧ pc.1.val < Arithmetic.limbBase ∧ pc.2.val < Arithmetic.limbBase :=
  fun ⟨_, _, pc, room, interface, outgoing, low, nonzero⟩ =>
    ⟨pc, nonzero, claim room interface outgoing low⟩

example (claim : Airbender.PaddingBoundary.ContributionSoundnessClaim) :
    Airbender.PaddingBoundary.ContributionSatisfiableClaim →
    ∃ (execute : ZMod babyBearModulus) (encode : Nat → ZMod babyBearModulus) (value : Nat),
      PaddingBoundary.evaluate encode (PaddingBoundary.contribution execute value) =
        PaddingBoundary.mask execute (encode value) :=
  fun ⟨execute, boolean, _, encode, value, _⟩ => ⟨execute, encode, value, claim execute boolean encode value⟩

example (claim : Airbender.PaddingBoundary.ProductSoundnessClaim) :
    Airbender.PaddingBoundary.ProductSatisfiableClaim →
    ∃ (execute : ZMod babyBearModulus) (encode : Nat → ZMod babyBearModulus) (values : List Nat),
      ((values.map (PaddingBoundary.contribution execute)).map (PaddingBoundary.evaluate encode)).prod =
        PaddingBoundary.mask execute (values.map encode).prod :=
  fun ⟨execute, boolean, _, encode, values, _, _⟩ => ⟨execute, encode, values, claim execute boolean encode values⟩

example (claim : Airbender.PaddingBoundary.ProjectionClaim) :
    Airbender.PaddingBoundary.ProjectionSatisfiableClaim →
    ∃ trace : Trace.PooledTrace babyBearModulus,
      trace.rows ≠ [] ∧ trace.rows.length = 2 ∧
      (PaddingBoundary.active trace).rows.length = 1 ∧ (PaddingBoundary.inactive trace).rows.length = 1 ∧
      Trace.Accepted (PaddingBoundary.active trace) :=
  fun ⟨trace, accepted, rows_nonempty, row_count, active_count, padding_count⟩ =>
    ⟨trace, rows_nonempty, row_count, active_count, padding_count, claim trace accepted⟩

example (claim : Airbender.Json.ParseSoundClaim) : Airbender.Json.ParseSoundSatisfiableClaim →
    ∃ (bytes : ByteArray) (value : Airbender.Json.Value),
      Airbender.Json.Text bytes.toList value ∧ Airbender.Json.NoDuplicateKeys value :=
  fun ⟨bytes, value, accepted, _, _, _⟩ => ⟨bytes, value, claim bytes value accepted⟩

example (claim : Airbender.Json.TextUniqueClaim) : Airbender.Json.TextUniqueSatisfiableClaim →
    ∃ (bytes : List UInt8) (left right : Airbender.Json.Value),
      Airbender.Json.Text bytes left ∧ Airbender.Json.Text bytes right ∧ left = right :=
  fun ⟨bytes, left, right, first, second, _, _⟩ => ⟨bytes, left, right, first, second, claim bytes left right first second⟩

example (claim : Airbender.DecodeClaim) : Airbender.DecodeSatisfiableClaim →
    ∃ (value : Airbender.Json.Value) (circuit : Airbender.Circuit), Airbender.Serde.encode circuit = value :=
  fun ⟨value, circuit, accepted⟩ => ⟨value, circuit, (claim value circuit).mp accepted⟩

example (claim : Airbender.PlacementsClaim) : Airbender.PlacementsSatisfiableClaim →
    ∃ (circuit : Airbender.Circuit) (address : Airbender.GKRAddress),
      circuit.placements.getD address.key [] =
        ((circuit.placement_data.entries.toList.filter (fun entry => decide (entry.2 = address))).map (·.1)).reverse :=
  fun ⟨circuit, address, _, _⟩ => ⟨circuit, address, claim circuit address⟩

example (claim : Airbender.Compiler.NativeLookups.CachedLookupSelectorsClaim) :
    Airbender.Compiler.NativeLookups.CachedLookupSelectorsSatisfiableClaim →
    ∃ family : Trace.RVMachineDecoderFamily,
      Airbender.Compiler.NativeLookups.selectorsFor family ≠ [] ∧
      Airbender.Compiler.NativeLookups.queryLocators (Airbender.Compiler.NativeLookups.circuitFor family) =
        .ok ((Airbender.Compiler.NativeLookups.selectorsFor family).map (fun selector => (selector.gate, selector.operand))) :=
  fun ⟨family, nonempty, _⟩ => ⟨family, nonempty, (claim family).1⟩

example (claim : Airbender.Compiler.AddSubCachedArithmeticClaim) :
    Airbender.Compiler.AddSubCachedArithmeticSatisfiableClaim →
    ∃ (physical : Airbender.GKRAddress → Airbender.Compiler.NativeArithmetic.F)
      (logical : Nat → Airbender.Compiler.NativeArithmetic.F),
      Airbender.Compiler.NativeArithmetic.Holds Airbender.Compiler.Captures.AddSub.imported.circuit physical ∧
      Airbender.FlatOperation.ConstraintsHoldFlat (Airbender.Verification.environment logical)
        (Airbender.Circuit.equations Airbender.Compiler.Captures.AddSub.imported.circuit) :=
  fun ⟨physical, logical, nativeHolds, placement⟩ => ⟨physical, logical, nativeHolds, claim physical logical nativeHolds placement⟩

example (claim : Airbender.Compiler.BigintCachedArithmeticClaim) :
    Airbender.Compiler.BigintCachedArithmeticSatisfiableClaim →
    ∃ (physical : Airbender.GKRAddress → Airbender.Compiler.NativeArithmetic.F)
      (logical : Nat → Airbender.Compiler.NativeArithmetic.F),
      Airbender.Compiler.NativeArithmetic.Holds Airbender.Compiler.Captures.Bigint.imported.circuit physical ∧
      Airbender.FlatOperation.ConstraintsHoldFlat (Airbender.Verification.environment logical)
        (Airbender.Circuit.equations Airbender.Compiler.Captures.Bigint.imported.circuit) :=
  fun ⟨physical, logical, nativeHolds, placement⟩ => ⟨physical, logical, nativeHolds, claim physical logical nativeHolds placement⟩

example (claim : Airbender.Compiler.BlakeGCachedArithmeticClaim) :
    Airbender.Compiler.BlakeGCachedArithmeticSatisfiableClaim →
    ∃ (physical : Airbender.GKRAddress → Airbender.Compiler.NativeArithmetic.F)
      (logical : Nat → Airbender.Compiler.NativeArithmetic.F),
      Airbender.Compiler.NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeG.imported.circuit physical ∧
      Airbender.FlatOperation.ConstraintsHoldFlat (Airbender.Verification.environment logical)
        (Airbender.Circuit.equations Airbender.Compiler.Captures.BlakeG.imported.circuit) :=
  fun ⟨physical, logical, nativeHolds, placement⟩ => ⟨physical, logical, nativeHolds, claim physical logical nativeHolds placement⟩

example (claim : Airbender.Compiler.BlakeRoundCachedArithmeticClaim) :
    Airbender.Compiler.BlakeRoundCachedArithmeticSatisfiableClaim →
    ∃ (physical : Airbender.GKRAddress → Airbender.Compiler.NativeArithmetic.F)
      (logical : Nat → Airbender.Compiler.NativeArithmetic.F),
      Airbender.Compiler.NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical ∧
      Airbender.FlatOperation.ConstraintsHoldFlat (Airbender.Verification.environment logical)
        (Airbender.Circuit.equations Airbender.Compiler.Captures.BlakeRound.imported.circuit) :=
  fun ⟨physical, logical, nativeHolds, placement⟩ => ⟨physical, logical, nativeHolds, claim physical logical nativeHolds placement⟩

example (claim : Airbender.Compiler.JumpBranchCachedArithmeticClaim) :
    Airbender.Compiler.JumpBranchCachedArithmeticSatisfiableClaim →
    ∃ (physical : Airbender.GKRAddress → Airbender.Compiler.NativeArithmetic.F)
      (logical : Nat → Airbender.Compiler.NativeArithmetic.F),
      Airbender.Compiler.NativeArithmetic.Holds Airbender.Compiler.Captures.JumpBranch.imported.circuit physical ∧
      Airbender.FlatOperation.ConstraintsHoldFlat (Airbender.Verification.environment logical)
        (Airbender.Circuit.equations Airbender.Compiler.Captures.JumpBranch.imported.circuit) :=
  fun ⟨physical, logical, nativeHolds, placement⟩ => ⟨physical, logical, nativeHolds, claim physical logical nativeHolds placement⟩

example (claim : Airbender.Compiler.KeccakCachedArithmeticClaim) :
    Airbender.Compiler.KeccakCachedArithmeticSatisfiableClaim →
    ∃ (physical : Airbender.GKRAddress → Airbender.Compiler.NativeArithmetic.F)
      (logical : Nat → Airbender.Compiler.NativeArithmetic.F),
      Airbender.Compiler.NativeArithmetic.Holds Airbender.Compiler.Captures.Keccak.imported.circuit physical ∧
      Airbender.FlatOperation.ConstraintsHoldFlat (Airbender.Verification.environment logical)
        (Airbender.Circuit.equations Airbender.Compiler.Captures.Keccak.imported.circuit) :=
  fun ⟨physical, logical, nativeHolds, placement⟩ => ⟨physical, logical, nativeHolds, claim physical logical nativeHolds placement⟩

example (claim : Airbender.Compiler.MulDivCachedArithmeticClaim) :
    Airbender.Compiler.MulDivCachedArithmeticSatisfiableClaim →
    ∃ (physical : Airbender.GKRAddress → Airbender.Compiler.NativeArithmetic.F)
      (logical : Nat → Airbender.Compiler.NativeArithmetic.F),
      Airbender.Compiler.NativeArithmetic.Holds Airbender.Compiler.Captures.MulDiv.imported.circuit physical ∧
      Airbender.FlatOperation.ConstraintsHoldFlat (Airbender.Verification.environment logical)
        (Airbender.Circuit.equations Airbender.Compiler.Captures.MulDiv.imported.circuit) :=
  fun ⟨physical, logical, nativeHolds, placement⟩ => ⟨physical, logical, nativeHolds, claim physical logical nativeHolds placement⟩

example (claim : Airbender.Compiler.ShiftBinopCachedArithmeticClaim) :
    Airbender.Compiler.ShiftBinopCachedArithmeticSatisfiableClaim →
    ∃ (physical : Airbender.GKRAddress → Airbender.Compiler.NativeArithmetic.F)
      (logical : Nat → Airbender.Compiler.NativeArithmetic.F),
      Airbender.Compiler.NativeArithmetic.Holds Airbender.Compiler.Captures.ShiftBinop.imported.circuit physical ∧
      Airbender.FlatOperation.ConstraintsHoldFlat (Airbender.Verification.environment logical)
        (Airbender.Circuit.equations Airbender.Compiler.Captures.ShiftBinop.imported.circuit) :=
  fun ⟨physical, logical, nativeHolds, placement⟩ => ⟨physical, logical, nativeHolds, claim physical logical nativeHolds placement⟩

example (claim : Airbender.Compiler.SubwordMemoryCachedArithmeticClaim) :
    Airbender.Compiler.SubwordMemoryCachedArithmeticSatisfiableClaim →
    ∃ (physical : Airbender.GKRAddress → Airbender.Compiler.NativeArithmetic.F)
      (logical : Nat → Airbender.Compiler.NativeArithmetic.F),
      Airbender.Compiler.NativeArithmetic.Holds Airbender.Compiler.Captures.SubwordMemory.imported.circuit physical ∧
      Airbender.FlatOperation.ConstraintsHoldFlat (Airbender.Verification.environment logical)
        (Airbender.Circuit.equations Airbender.Compiler.Captures.SubwordMemory.imported.circuit) :=
  fun ⟨physical, logical, nativeHolds, placement⟩ => ⟨physical, logical, nativeHolds, claim physical logical nativeHolds placement⟩

example (claim : Airbender.Compiler.UnifiedCachedArithmeticClaim) :
    Airbender.Compiler.UnifiedCachedArithmeticSatisfiableClaim →
    ∃ (physical : Airbender.GKRAddress → Airbender.Compiler.NativeArithmetic.F)
      (logical : Nat → Airbender.Compiler.NativeArithmetic.F),
      Airbender.Compiler.NativeArithmetic.Holds Airbender.Compiler.Captures.Unified.imported.circuit physical ∧
      Airbender.FlatOperation.ConstraintsHoldFlat (Airbender.Verification.environment logical)
        (Airbender.Circuit.equations Airbender.Compiler.Captures.Unified.imported.circuit) :=
  fun ⟨physical, logical, nativeHolds, placement⟩ => ⟨physical, logical, nativeHolds, claim physical logical nativeHolds placement⟩

example (claim : Airbender.Compiler.WordMemoryCachedArithmeticClaim) :
    Airbender.Compiler.WordMemoryCachedArithmeticSatisfiableClaim →
    ∃ (physical : Airbender.GKRAddress → Airbender.Compiler.NativeArithmetic.F)
      (logical : Nat → Airbender.Compiler.NativeArithmetic.F),
      Airbender.Compiler.NativeArithmetic.Holds Airbender.Compiler.Captures.WordMemory.imported.circuit physical ∧
      Airbender.FlatOperation.ConstraintsHoldFlat (Airbender.Verification.environment logical)
        (Airbender.Circuit.equations Airbender.Compiler.Captures.WordMemory.imported.circuit) :=
  fun ⟨physical, logical, nativeHolds, placement⟩ => ⟨physical, logical, nativeHolds, claim physical logical nativeHolds placement⟩

example (claim : Airbender.InitsTeardowns.Native.StandaloneSoundnessClaim) :
    Airbender.InitsTeardowns.Native.StandaloneSatisfiableClaim →
    ∃ (parameters : Airbender.InitsTeardowns.Native.Parameters babyBearModulus (ZMod babyBearModulus))
      (witness : Airbender.InitsTeardowns.Witness babyBearModulus Airbender.InitsTeardowns.importedLayout)
      (wires : Airbender.InitsTeardowns.Native.Wires (ZMod babyBearModulus)),
      Airbender.InitsTeardowns.Native.rootProduct Airbender.InitsTeardowns.Native.standaloneArtifact
        Airbender.InitsTeardowns.Native.standaloneArtifact.terminal wires = (witness.teardownTokens.map parameters.encode).prod ∧
      Airbender.InitsTeardowns.Native.rootProduct Airbender.InitsTeardowns.Native.standaloneArtifact
        Airbender.InitsTeardowns.Native.standaloneArtifact.initial wires = (witness.initTokens.map parameters.encode).prod :=
  fun ⟨parameters, witness, wires, windows, checked, accepted⟩ =>
    ⟨parameters, witness, wires, claim parameters witness wires windows checked accepted⟩

example (claim : Airbender.InitsTeardowns.Native.UnifiedSoundnessClaim) :
    Airbender.InitsTeardowns.Native.UnifiedSatisfiableClaim →
    ∃ (parameters : Airbender.InitsTeardowns.Native.Parameters babyBearModulus (ZMod babyBearModulus))
      (witness : Airbender.InitsTeardowns.Witness babyBearModulus Airbender.InitsTeardowns.unifiedLayout)
      (wires : Airbender.InitsTeardowns.Native.Wires (ZMod babyBearModulus)),
      Airbender.InitsTeardowns.Native.rootProduct Airbender.InitsTeardowns.Native.unifiedArtifact
        Airbender.InitsTeardowns.Native.unifiedArtifact.terminal wires = (witness.teardownTokens.map parameters.encode).prod ∧
      Airbender.InitsTeardowns.Native.rootProduct Airbender.InitsTeardowns.Native.unifiedArtifact
        Airbender.InitsTeardowns.Native.unifiedArtifact.initial wires = (witness.initTokens.map parameters.encode).prod :=
  fun ⟨parameters, witness, wires, windows, checked, accepted⟩ =>
    ⟨parameters, witness, wires, claim parameters witness wires windows checked accepted⟩

namespace RV.ValidUse
open Spec

example (claim : RV.ValidUse.BigintReferenceClaim) : RV.ValidUse.BigintReferenceSatisfiableClaim →
    ∃ state, Delegation.effect .bigint (state.getReg 10) (state.getReg 11) (state.getReg 12)
    state.delegationRAM = bigintReference state :=
  fun ⟨state, assumptions⟩ => ⟨state, claim state assumptions⟩

example (claim : RV.ValidUse.GReferenceClaim) : RV.ValidUse.GReferenceSatisfiableClaim →
    ∃ (reduced : Bool) (state : RV.State) (left right : RV.Word), ∃ finish, calls (.replicate (if reduced then 56 else 80) .blakeG) state = some finish ∧
      ChangesOnly state finish left 64 12 ∧ finish.getReg 12 = (if reduced then 0x80#32 else 0#32) ∧
      readWords finish.mem left 16 = gReference reduced (readWords state.mem left 16) (readWords state.mem right 16) :=
  fun ⟨reduced, state, left, right, assumptions⟩ => ⟨reduced, state, left, right, claim reduced state left right assumptions⟩

example (claim : RV.ValidUse.RoundReferenceClaim) : RV.ValidUse.RoundReferenceSatisfiableClaim →
    ∃ (reduced : Bool) (state : RV.State) (left right counter : RV.Word) (last : Bool), ∃ finish, calls (.replicate (if reduced then 7 else 10) .blakeRound) state = some finish ∧
      ChangesOnly state finish left 96 12 ∧
      readWords finish.mem left 8 = compressRounds (if reduced then 7 else 10)
        (readWords state.mem left 8) (readWords state.mem right 16) counter last :=
  fun ⟨reduced, state, left, right, counter, last, assumptions⟩ => ⟨reduced, state, left, right, counter, last, claim reduced state left right counter last assumptions⟩

example (claim : RV.ValidUse.HashReferenceClaim) : RV.ValidUse.HashReferenceSatisfiableClaim →
    ∃ (reduced right : Bool) (state : RV.State) (left sibling : RV.Word), ∃ finish, calls (.replicate (if reduced then 7 else 10) .blakeRound) state = some finish ∧
      ChangesOnly state finish left 96 12 ∧
      readWords finish.mem left 8 = compressRounds (if reduced then 7 else 10) (Vector.ofFn configuredIV)
        (if right then readWords state.mem sibling 8 ++ readWords state.mem left 8
          else readWords state.mem left 8 ++ readWords state.mem sibling 8) 64#32 true :=
  fun ⟨reduced, right, state, left, sibling, assumptions⟩ => ⟨reduced, right, state, left, sibling, claim reduced right state left sibling assumptions⟩

example (claim : RV.ValidUse.SplitKeccakReferenceClaim) : RV.ValidUse.SplitKeccakReferenceSatisfiableClaim →
    ∃ state pointer, ∃ finish, calls f1600Calls state = some finish ∧ ChangesOnly state finish pointer 248 10 ∧
      readLanes finish.mem pointer 25 = keccakF (readLanes state.mem pointer 25) :=
  fun ⟨state, pointer, assumptions⟩ => ⟨state, pointer, claim state pointer assumptions⟩

example (claim : RV.ValidUse.Special5ReferenceClaim) : RV.ValidUse.Special5ReferenceSatisfiableClaim →
    ∃ state pointer, ∃ finish, calls (.replicate 649 .keccak) state = some finish ∧ ChangesOnly state finish pointer 248 10 ∧
      readLanes finish.mem pointer 25 = keccakF (readLanes state.mem pointer 25) :=
  fun ⟨state, pointer, assumptions⟩ => ⟨state, pointer, claim state pointer assumptions⟩

end RV.ValidUse


namespace RV
open Spec

example (claim : RV.BlakeCompressRun) : RV.BlakeCompressRunSatisfiableClaim →
    ∃ (s : State) (p q t : Word) (last : Bool), ∃ s', calls (.replicate 7 .blakeRound) s = some s' ∧ ChangesOnly s s' p 96 12 ∧
      readWords s'.mem p 8 = compress (readWords s.mem p 8) (readWords s.mem q 16) t last :=
  fun ⟨s, p, q, t, last, assumptions⟩ => ⟨s, p, q, t, last, claim s p q t last assumptions⟩

example (claim : RV.BlakeCompressRun10) : RV.BlakeCompressRun10SatisfiableClaim →
    ∃ (s : State) (p q t : Word) (last : Bool), ∃ s', calls (.replicate 10 .blakeRound) s = some s' ∧ ChangesOnly s s' p 96 12 ∧
      readWords s'.mem p 8 = compressRounds 10 (readWords s.mem p 8) (readWords s.mem q 16) t last :=
  fun ⟨s, p, q, t, last, assumptions⟩ => ⟨s, p, q, t, last, claim s p q t last assumptions⟩

example (claim : RV.BlakeHashRun) : RV.BlakeHashRunSatisfiableClaim →
    ∃ (s : State) (p q : Word) (right : Bool), ∃ s', calls (.replicate 7 .blakeRound) s = some s' ∧ ChangesOnly s s' p 96 12 ∧
      readWords s'.mem p 8 =
        if right then hash2 (readWords s.mem q 8) (readWords s.mem p 8) else hash2 (readWords s.mem p 8) (readWords s.mem q 8) :=
  fun ⟨s, p, q, right, assumptions⟩ => ⟨s, p, q, right, claim s p q right assumptions⟩

example (claim : RV.BlakeHashRun10) : RV.BlakeHashRun10SatisfiableClaim →
    ∃ (s : State) (p q : Word) (right : Bool), ∃ s', calls (.replicate 10 .blakeRound) s = some s' ∧ ChangesOnly s s' p 96 12 ∧
      readWords s'.mem p 8 = compressRounds 10 (Vector.ofFn configuredIV)
        (if right then readWords s.mem q 8 ++ readWords s.mem p 8 else readWords s.mem p 8 ++ readWords s.mem q 8)
        64#32 true :=
  fun ⟨s, p, q, right, assumptions⟩ => ⟨s, p, q, right, claim s p q right assumptions⟩

example (claim : RV.BlakeGRun) : RV.BlakeGRunSatisfiableClaim →
    ∃ (s : State) (p q : Word), ∃ s', calls (.replicate 56 .blakeG) s = some s' ∧ ChangesOnly s s' p 64 12 ∧ s'.getReg 12 = 0x80#32 ∧
      readWords s'.mem p 16 = (List.finRange 7).foldl
        (fun v r => round (readWords s.mem q 16) (SIGMA (r.castLE (by decide))) v) (readWords s.mem p 16) :=
  fun ⟨s, p, q, assumptions⟩ => ⟨s, p, q, claim s p q assumptions⟩

example (claim : RV.BlakeGRun10) : RV.BlakeGRun10SatisfiableClaim →
    ∃ (s : State) (p q : Word), ∃ s', calls (.replicate 80 .blakeG) s = some s' ∧ ChangesOnly s s' p 64 12 ∧ s'.getReg 12 = 0#32 ∧
      readWords s'.mem p 16 = (List.finRange 10).foldl
        (fun v r => round (readWords s.mem q 16) (SIGMA r) v) (readWords s.mem p 16) :=
  fun ⟨s, p, q, assumptions⟩ => ⟨s, p, q, claim s p q assumptions⟩

example (claim : RV.KeccakF1600Run) : RV.KeccakF1600RunSatisfiableClaim →
    ∃ (s : State) (p : Word), ∃ s', calls f1600Calls s = some s' ∧ ChangesOnly s s' p 248 10 ∧
      readLanes s'.mem p 25 = keccakF (readLanes s.mem p 25) :=
  fun ⟨s, p, assumptions⟩ => ⟨s, p, claim s p assumptions⟩

example (claim : RV.KeccakSpecial5Run) : RV.KeccakSpecial5RunSatisfiableClaim →
    ∃ (s : State) (p : Word), ∃ s', calls (.replicate 649 .keccak) s = some s' ∧ ChangesOnly s s' p 248 10 ∧
      readLanes s'.mem p 25 = keccakF (readLanes s.mem p 25) :=
  fun ⟨s, p, assumptions⟩ => ⟨s, p, claim s p assumptions⟩

end RV

example (claim : Airbender.AgreeExistsClaim) : Airbender.AgreeExistsSatisfiableClaim →
    ∃ state machine, Airbender.Agree state machine :=
  fun ⟨state, _, _⟩ => ⟨state, claim state⟩

example (claim : Airbender.DecodeIsSailClaim) : Airbender.DecodeIsSailSatisfiableClaim →
    ∃ word instruction state,
      Human.runSail (SailRV32.Functions.ext_decode word) state = .ok (Airbender.toSail instruction) state :=
  fun ⟨word, instruction, state, decoded, configured⟩ => ⟨word, instruction, state, claim word instruction state decoded configured⟩

example (claim : Airbender.StepIsAirbenderClaim) : Airbender.StepIsAirbenderSatisfiableClaim →
    ∃ (state next : RV.State) (machine machine' : Airbender.Machine),
      RV.step state = some next ∧ Airbender.step machine = some machine' ∧ Airbender.Agree next machine' :=
  fun ⟨state, next, machine, agree, step⟩ => by
    obtain ⟨finish, stepped, agrees⟩ := claim state next machine agree step
    exact ⟨state, next, machine, finish, step, stepped, agrees⟩

example (claim : Airbender.RunIsAirbenderClaim) : Airbender.RunIsAirbenderSatisfiableClaim →
    ∃ (n : Nat) (state next : RV.State) (machine : Airbender.Machine), Airbender.Agree state machine ∧ 1 ≤ n ∧
      ∃ finish, Airbender.Machine.run n machine = some finish ∧ Airbender.Agree next finish :=
  fun ⟨n, state, next, machine, agree, run, positive⟩ =>
    ⟨n, state, next, machine, agree, positive, claim n state next machine agree run⟩

example (claim : Airbender.FetchKeepsConfiguredClaim) : Airbender.FetchKeepsConfiguredSatisfiableClaim →
    ∃ (state : Human.SailState) (word : RV.Word) (instruction : RV.Instr)
      (result : _) (state' : Human.SailState),
      RV.decode word = some instruction ∧ Airbender.Configured state ∧
      Human.runSail (SailRV32.Functions.fetch ()) state = .ok result state' ∧ Airbender.Configured state' :=
  fun ⟨state, word, instruction, result, state', configured, aligned, room, read, decoded, fetched⟩ =>
    ⟨state, word, instruction, result, state', decoded, configured, fetched,
      claim state word instruction result state' configured aligned room read decoded fetched⟩

example (claim : RV.CallsRun) : RV.CallsRunSatisfiableClaim →
    ∃ (kinds : List RV.DelegationKind) (state next : RV.State), kinds ≠ [] ∧ RV.run kinds.length state = some next :=
  fun ⟨kinds, state, next, assumptions, nonempty⟩ => ⟨kinds, state, next, nonempty, claim kinds state next assumptions⟩

namespace RV.Delegation
open Spec

example (claim : RV.Delegation.BlakeRoundOneHotClaim) : RV.Delegation.BlakeRoundOneHotSatisfiableClaim →
    ∃ (state message control : Word) (mem : Word → BitVec 8) (roundIndex : Nat),
      blakeRoundMasked state message control mem =
        blakeRoundBody state message control mem (decide (roundIndex = 0))
          (decide (roundIndex + 1 = (if control.getLsbD 16 then 7 else 10)))
          (fun message state => round message (SIGMA ⟨roundIndex % 10, Nat.mod_lt _ (by decide)⟩) state) :=
  fun ⟨state, message, control, mem, roundIndex, bound, mask⟩ =>
    ⟨state, message, control, mem, roundIndex, claim state message control mem roundIndex bound mask⟩

end RV.Delegation

namespace Airbender.Trace.Machine.Native
open Airbender.Compiler

example (claim : Airbender.Trace.Machine.Native.UnrolledFullFromNative) :
    Airbender.Trace.Machine.Native.UnrolledFullFromNativeSatisfiableClaim →
  ∃ (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)) (tables : ProgramLookupRows),
    trace.rows.length = 1 ∧ workers.standard.rows = [] ∧ workers.split.rows = [] ∧
    BootInputs .unrolledFullUnsigned trace initial cells program InitsTeardowns.importedLayout inits ∧
    NoSpecial5 program ∧
    NonDeterminism.Pooled.StreamPorts trace initial.input ∧
    NativePublicSetup.Bound initial program tables ∧ NativePublicSetup.CoversROM cells ∧
    ∃ certificates : List (ProgramLogicalRowCertificate tables),
      UnrolledNativeArguments tables certificates trace workers ∧
    RVRealizes trace initial cells (NonDeterminism.Pooled.readCount trace) :=
  fun ⟨trace, workers, initial, cells, program, inits, tables, boot, noSpecial, stream, bound, covers, certificates, arguments, row_count, worker_count, split_rows⟩ =>
    ⟨trace, workers, initial, cells, program, inits, tables, row_count, worker_count, split_rows, boot, noSpecial, stream, bound, covers, certificates, arguments, claim trace workers initial cells program inits tables boot noSpecial stream bound covers certificates arguments⟩

example (claim : Airbender.Trace.Machine.Native.UnrolledReducedFromNative) :
    Airbender.Trace.Machine.Native.UnrolledReducedFromNativeSatisfiableClaim →
  ∃ (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)) (tables : ProgramLookupRows),
    trace.rows.length = 1 ∧ workers.standard.rows = [] ∧ workers.split.rows = [] ∧
    BootInputs .unrolledReduced trace initial cells program InitsTeardowns.importedLayout inits ∧
    NonDeterminism.Pooled.StreamPorts trace initial.input ∧
    NativePublicSetup.Bound initial program tables ∧ NativePublicSetup.CoversROM cells ∧
    ∃ certificates : List (ProgramLogicalRowCertificate tables),
      UnrolledNativeArguments tables certificates trace workers ∧
    RVRealizes trace initial cells (NonDeterminism.Pooled.readCount trace) :=
  fun ⟨trace, workers, initial, cells, program, inits, tables, boot, stream, bound, covers, certificates, arguments, row_count, worker_count, split_rows⟩ =>
    ⟨trace, workers, initial, cells, program, inits, tables, row_count, worker_count, split_rows, boot, stream, bound, covers, certificates, arguments, claim trace workers initial cells program inits tables boot stream bound covers certificates arguments⟩

example (claim : Airbender.Trace.Machine.Native.UnifiedFromNative) :
    Airbender.Trace.Machine.Native.UnifiedFromNativeSatisfiableClaim →
  ∃ (trace : UnifiedTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.unifiedLayout)) (tables : ProgramLookupRows),
    trace.rows.length = 16 ∧ workers.standard.rows.length = 2 ∧ workers.split.rows = [] ∧
    BootInputs .unified trace initial cells program InitsTeardowns.unifiedLayout inits ∧
    NoSpecial5 program ∧ UnifiedStreamPorts trace initial.input ∧
    NativePublicSetup.Bound initial program tables ∧
    ∃ certificates : List (UnifiedLogicalRowCertificate tables),
      UnifiedNativeArguments tables certificates trace workers ∧
    RVRealizes trace initial cells (unifiedReadCount trace) :=
  fun ⟨trace, workers, initial, cells, program, inits, tables, boot, noSpecial, stream, bound, certificates, arguments, row_count, worker_count, split_rows⟩ =>
    ⟨trace, workers, initial, cells, program, inits, tables, row_count, worker_count, split_rows, boot, noSpecial, stream, bound, certificates, arguments, claim trace workers initial cells program inits tables boot noSpecial stream bound certificates arguments⟩

end Airbender.Trace.Machine.Native

example (claim : Airbender.Compiler.KeccakColumnParityCachedArithmeticClaim) :
    Airbender.Compiler.KeccakColumnParityCachedArithmeticSatisfiableClaim →
    ∃ (physical : Airbender.GKRAddress → Airbender.Compiler.NativeArithmetic.F)
      (logical : Nat → Airbender.Compiler.NativeArithmetic.F),
      Airbender.Compiler.NativeArithmetic.Holds Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical ∧
      Airbender.FlatOperation.ConstraintsHoldFlat (Airbender.Verification.environment logical)
        (Airbender.Circuit.equations Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit) :=
  fun ⟨physical, logical, nativeHolds, placement⟩ => ⟨physical, logical, nativeHolds, claim physical logical nativeHolds placement⟩

example (claim : Airbender.Compiler.KeccakThetaRhoCachedArithmeticClaim) :
    Airbender.Compiler.KeccakThetaRhoCachedArithmeticSatisfiableClaim →
    ∃ (physical : Airbender.GKRAddress → Airbender.Compiler.NativeArithmetic.F)
      (logical : Nat → Airbender.Compiler.NativeArithmetic.F),
      Airbender.Compiler.NativeArithmetic.Holds Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical ∧
      Airbender.FlatOperation.ConstraintsHoldFlat (Airbender.Verification.environment logical)
        (Airbender.Circuit.equations Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit) :=
  fun ⟨physical, logical, nativeHolds, placement⟩ => ⟨physical, logical, nativeHolds, claim physical logical nativeHolds placement⟩

example (claim : Airbender.Compiler.KeccakChi5CachedArithmeticClaim) :
    Airbender.Compiler.KeccakChi5CachedArithmeticSatisfiableClaim →
    ∃ (physical : Airbender.GKRAddress → Airbender.Compiler.NativeArithmetic.F)
      (logical : Nat → Airbender.Compiler.NativeArithmetic.F),
      Airbender.Compiler.NativeArithmetic.Holds Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical ∧
      Airbender.FlatOperation.ConstraintsHoldFlat (Airbender.Verification.environment logical)
        (Airbender.Circuit.equations Airbender.Compiler.Captures.KeccakChi5.imported.circuit) :=
  fun ⟨physical, logical, nativeHolds, placement⟩ => ⟨physical, logical, nativeHolds, claim physical logical nativeHolds placement⟩

example (claim : Airbender.Compiler.NativeWorkerLookups.CachedWorkerLookupSelectorsClaim) :
    Airbender.Compiler.NativeWorkerLookups.CachedWorkerLookupSelectorsSatisfiableClaim →
    ∃ family : Airbender.Compiler.NativeWorkerLookups.Family,
      Airbender.Compiler.NativeWorkerLookups.selectorsFor family ≠ [] ∧
      Airbender.Compiler.NativeLookups.queryLocators (Airbender.Compiler.NativeWorkerLookups.circuitFor family) =
        .ok ((Airbender.Compiler.NativeWorkerLookups.selectorsFor family).map (fun selector => (selector.gate, selector.operand))) :=
  fun ⟨family, nonempty, _⟩ => ⟨family, nonempty, (claim family).1⟩

/-- Every target worker has a certificate with native gates, placement, lookups and execute one. -/
example (family : Airbender.Compiler.NativeWorkerLookups.Family) :
    ∃ entry : Airbender.Compiler.WorkerCertificate, entry.family = family :=
  Airbender.Compiler.cached_worker_certificates_satisfiable family

example (claim : Airbender.RunSailSimulationClaim) : Airbender.RunSailSimulationSatisfiableClaim →
    ∃ (program : SailRV32.SailM (SailRV32.RegisterType .PC)) (sequential sequential' : Airbender.SequentialSailState)
      (value : SailRV32.RegisterType .PC),
      (Sail.ArchSem.interpretSailEffects program).run sequential = .ok value sequential' :=
  fun ⟨program, state, state', sequential, value, agrees, run⟩ =>
    let ⟨sequential', theirs, _⟩ := claim program state state' sequential value agrees run
    ⟨program, sequential, sequential', value, theirs⟩

example (claim : Airbender.MachineRunIsSequentialClaim) : Airbender.MachineRunIsSequentialSatisfiableClaim →
    ∃ (n : Nat) (machine : Airbender.SequentialMachine) (machine' : Airbender.SequentialMachine),
      1 ≤ n ∧ Airbender.SequentialMachine.run n machine = some machine' :=
  fun ⟨n, machine, machine', sequential, agrees, run, positive⟩ =>
    let ⟨_, theirs, _⟩ := claim n machine machine' sequential agrees run
    ⟨n, _, _, positive, theirs⟩

-- Native RAM outputs and padded native targets.

example : Airbender.Compiler.NativeMemory.StateTokenMatchingSatisfiableClaim := Airbender.Compiler.NativeMemory.state_token_matching_satisfiable

example (claim : Airbender.Compiler.NativeMemory.StateTokenMatchingClaim) :
    Airbender.Compiler.NativeMemory.StateTokenMatchingSatisfiableClaim →
    ∃ before after : List (Airbender.PCState.State Airbender.babyBearModulus), before ≠ [] ∧ before.Perm after :=
  fun ⟨before, after, matching, nonempty⟩ => ⟨before, after, nonempty, claim before after matching⟩

example : Airbender.Compiler.AddSubCachedMemorySatisfiableClaim := Airbender.Compiler.addSub_cached_memory_satisfiable

example (claim : Airbender.Compiler.AddSubCachedMemoryClaim) :
    Airbender.Compiler.AddSubCachedMemorySatisfiableClaim →
    ∃ (challenges : Airbender.Compiler.NativeMemory.Challenges Airbender.Compiler.NativeArithmetic.F)
      (values : Airbender.GKRAddress → Airbender.Compiler.NativeArithmetic.F)
      (row : Airbender.Trace.Row Airbender.babyBearModulus Airbender.Trace.PooledFamily),
      Airbender.Compiler.NativeMemory.RamProducts Airbender.Compiler.Captures.AddSub.imported.circuit challenges values
        (row.assignment row.columns.execute) (Airbender.Compiler.NativeMemory.cpuReads row)
        (Airbender.Compiler.NativeMemory.cpuWrites row) :=
  fun ⟨challenges, physical, values, row, family, nativeHolds, placement, extension⟩ =>
    ⟨challenges, values, row, claim challenges physical values row family nativeHolds placement extension⟩

example : Airbender.Compiler.JumpBranchCachedMemorySatisfiableClaim := Airbender.Compiler.jumpBranch_cached_memory_satisfiable

example (claim : Airbender.Compiler.JumpBranchCachedMemoryClaim) :
    Airbender.Compiler.JumpBranchCachedMemorySatisfiableClaim →
    ∃ (challenges : Airbender.Compiler.NativeMemory.Challenges Airbender.Compiler.NativeArithmetic.F)
      (values : Airbender.GKRAddress → Airbender.Compiler.NativeArithmetic.F)
      (row : Airbender.Trace.Row Airbender.babyBearModulus Airbender.Trace.PooledFamily),
      Airbender.Compiler.NativeMemory.RamProducts Airbender.Compiler.Captures.JumpBranch.imported.circuit challenges values
        (row.assignment row.columns.execute) (Airbender.Compiler.NativeMemory.cpuReads row)
        (Airbender.Compiler.NativeMemory.cpuWrites row) :=
  fun ⟨challenges, physical, values, row, family, nativeHolds, placement, extension⟩ =>
    ⟨challenges, values, row, claim challenges physical values row family nativeHolds placement extension⟩

example : Airbender.Compiler.MulDivCachedMemorySatisfiableClaim := Airbender.Compiler.mulDiv_cached_memory_satisfiable

example (claim : Airbender.Compiler.MulDivCachedMemoryClaim) :
    Airbender.Compiler.MulDivCachedMemorySatisfiableClaim →
    ∃ (challenges : Airbender.Compiler.NativeMemory.Challenges Airbender.Compiler.NativeArithmetic.F)
      (values : Airbender.GKRAddress → Airbender.Compiler.NativeArithmetic.F)
      (row : Airbender.Trace.Row Airbender.babyBearModulus Airbender.Trace.PooledFamily),
      Airbender.Compiler.NativeMemory.RamProducts Airbender.Compiler.Captures.MulDiv.imported.circuit challenges values
        (row.assignment row.columns.execute) (Airbender.Compiler.NativeMemory.cpuReads row)
        (Airbender.Compiler.NativeMemory.cpuWrites row) :=
  fun ⟨challenges, physical, values, row, family, nativeHolds, placement, extension⟩ =>
    ⟨challenges, values, row, claim challenges physical values row family nativeHolds placement extension⟩

example : Airbender.Compiler.ShiftBinopCachedMemorySatisfiableClaim := Airbender.Compiler.shiftBinop_cached_memory_satisfiable

example (claim : Airbender.Compiler.ShiftBinopCachedMemoryClaim) :
    Airbender.Compiler.ShiftBinopCachedMemorySatisfiableClaim →
    ∃ (challenges : Airbender.Compiler.NativeMemory.Challenges Airbender.Compiler.NativeArithmetic.F)
      (values : Airbender.GKRAddress → Airbender.Compiler.NativeArithmetic.F)
      (row : Airbender.Trace.Row Airbender.babyBearModulus Airbender.Trace.PooledFamily),
      Airbender.Compiler.NativeMemory.RamProducts Airbender.Compiler.Captures.ShiftBinop.imported.circuit challenges values
        (row.assignment row.columns.execute) (Airbender.Compiler.NativeMemory.cpuReads row)
        (Airbender.Compiler.NativeMemory.cpuWrites row) :=
  fun ⟨challenges, physical, values, row, family, nativeHolds, placement, extension⟩ =>
    ⟨challenges, values, row, claim challenges physical values row family nativeHolds placement extension⟩

example : Airbender.Compiler.SubwordMemoryCachedMemorySatisfiableClaim := Airbender.Compiler.subwordMemory_cached_memory_satisfiable

example (claim : Airbender.Compiler.SubwordMemoryCachedMemoryClaim) :
    Airbender.Compiler.SubwordMemoryCachedMemorySatisfiableClaim →
    ∃ (challenges : Airbender.Compiler.NativeMemory.Challenges Airbender.Compiler.NativeArithmetic.F)
      (values : Airbender.GKRAddress → Airbender.Compiler.NativeArithmetic.F)
      (row : Airbender.Trace.Row Airbender.babyBearModulus Airbender.Trace.PooledFamily),
      Airbender.Compiler.NativeMemory.RamProducts Airbender.Compiler.Captures.SubwordMemory.imported.circuit challenges values
        (row.assignment row.columns.execute) (Airbender.Compiler.NativeMemory.cpuReads row)
        (Airbender.Compiler.NativeMemory.cpuWrites row) :=
  fun ⟨challenges, physical, values, row, family, nativeHolds, placement, extension⟩ =>
    ⟨challenges, values, row, claim challenges physical values row family nativeHolds placement extension⟩

example : Airbender.Compiler.WordMemoryCachedMemorySatisfiableClaim := Airbender.Compiler.wordMemory_cached_memory_satisfiable

example (claim : Airbender.Compiler.WordMemoryCachedMemoryClaim) :
    Airbender.Compiler.WordMemoryCachedMemorySatisfiableClaim →
    ∃ (challenges : Airbender.Compiler.NativeMemory.Challenges Airbender.Compiler.NativeArithmetic.F)
      (values : Airbender.GKRAddress → Airbender.Compiler.NativeArithmetic.F)
      (row : Airbender.Trace.Row Airbender.babyBearModulus Airbender.Trace.PooledFamily),
      Airbender.Compiler.NativeMemory.RamProducts Airbender.Compiler.Captures.WordMemory.imported.circuit challenges values
        (row.assignment row.columns.execute) (Airbender.Compiler.NativeMemory.cpuReads row)
        (Airbender.Compiler.NativeMemory.cpuWrites row) :=
  fun ⟨challenges, physical, values, row, family, nativeHolds, placement, extension⟩ =>
    ⟨challenges, values, row, claim challenges physical values row family nativeHolds placement extension⟩

example : Airbender.Compiler.UnifiedCachedMemorySatisfiableClaim := Airbender.Compiler.unified_cached_memory_satisfiable

example (claim : Airbender.Compiler.UnifiedCachedMemoryClaim) :
    Airbender.Compiler.UnifiedCachedMemorySatisfiableClaim →
    ∃ (challenges : Airbender.Compiler.NativeMemory.Challenges Airbender.Compiler.NativeArithmetic.F)
      (values : Airbender.GKRAddress → Airbender.Compiler.NativeArithmetic.F)
      (row : Airbender.Trace.Row Airbender.babyBearModulus Airbender.Trace.UnifiedFamily),
      Airbender.Compiler.NativeMemory.RamProducts Airbender.Compiler.Captures.Unified.imported.circuit challenges values
        (row.assignment row.columns.execute) (Airbender.Compiler.NativeMemory.cpuReads row)
        (Airbender.Compiler.NativeMemory.cpuWrites row) :=
  fun ⟨challenges, physical, values, row, nativeHolds, placement, extension⟩ =>
    ⟨challenges, values, row, claim challenges physical values row nativeHolds placement extension⟩

namespace Airbender.Trace.Machine.Native
open Airbender.Compiler

example : PaddedUnrolledFullFromNativeSatisfiableClaim := padded_unrolled_full_from_native_satisfiable

example : PaddedUnrolledReducedFromNativeSatisfiableClaim := padded_unrolled_reduced_from_native_satisfiable

example : PaddedUnifiedFromNativeSatisfiableClaim := padded_unified_from_native_satisfiable

example (claim : Airbender.Trace.Machine.Native.PaddedUnrolledFullFromNative) :
    Airbender.Trace.Machine.Native.PaddedUnrolledFullFromNativeSatisfiableClaim →
  ∃ (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)) (tables : ProgramLookupRows),
    (PaddingBoundary.active trace).rows.length = 1 ∧ (PaddingBoundary.inactive trace).rows.length = 1 ∧
    BootInputs .unrolledFullUnsigned (PaddingBoundary.active trace) initial cells program InitsTeardowns.importedLayout inits ∧
    ∃ certificates : List (ProgramRowCertificate tables),
      PaddedUnrolledNativeArguments tables certificates trace workers ∧
    RVRealizes trace initial cells (NonDeterminism.Pooled.readCount (PaddingBoundary.active trace)) :=
  fun ⟨trace, workers, initial, cells, program, inits, tables, boot, noSpecial, stream, bound, covers,
      certificates, arguments, active, padding⟩ =>
    ⟨trace, workers, initial, cells, program, inits, tables, active, padding, boot, certificates, arguments,
      claim trace workers initial cells program inits tables boot noSpecial stream bound covers certificates
        arguments⟩

example (claim : Airbender.Trace.Machine.Native.PaddedUnrolledReducedFromNative) :
    Airbender.Trace.Machine.Native.PaddedUnrolledReducedFromNativeSatisfiableClaim →
  ∃ (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)) (tables : ProgramLookupRows),
    (PaddingBoundary.active trace).rows.length = 1 ∧ (PaddingBoundary.inactive trace).rows.length = 1 ∧
    BootInputs .unrolledReduced (PaddingBoundary.active trace) initial cells program InitsTeardowns.importedLayout inits ∧
    ∃ certificates : List (ProgramRowCertificate tables),
      PaddedUnrolledNativeArguments tables certificates trace workers ∧
    RVRealizes trace initial cells (NonDeterminism.Pooled.readCount (PaddingBoundary.active trace)) :=
  fun ⟨trace, workers, initial, cells, program, inits, tables, boot, stream, bound, covers, certificates,
      arguments, active, padding⟩ =>
    ⟨trace, workers, initial, cells, program, inits, tables, active, padding, boot, certificates, arguments,
      claim trace workers initial cells program inits tables boot stream bound covers certificates arguments⟩

example (claim : Airbender.Trace.Machine.Native.PaddedUnifiedFromNative) :
    Airbender.Trace.Machine.Native.PaddedUnifiedFromNativeSatisfiableClaim →
  ∃ (trace : UnifiedTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.unifiedLayout)) (tables : ProgramLookupRows),
    (PaddingBoundary.active trace).rows.length = 1 ∧ (PaddingBoundary.inactive trace).rows.length = 1 ∧
    BootInputs .unified (PaddingBoundary.active trace) initial cells program InitsTeardowns.unifiedLayout inits ∧
    ∃ certificates : List (UnifiedRowCertificate tables),
      PaddedUnifiedNativeArguments tables certificates trace workers ∧
    RVRealizes trace initial cells (unifiedReadCount (PaddingBoundary.active trace)) :=
  fun ⟨trace, workers, initial, cells, program, inits, tables, boot, noSpecial, stream, bound, certificates,
      arguments, active, padding⟩ =>
    ⟨trace, workers, initial, cells, program, inits, tables, active, padding, boot, certificates, arguments,
      claim trace workers initial cells program inits tables boot noSpecial stream bound certificates arguments⟩

end Airbender.Trace.Machine.Native

-- Worker RAM outputs.

example : Airbender.Compiler.BigintCachedMemorySatisfiableClaim := Airbender.Compiler.bigint_cached_memory_satisfiable

example (claim : Airbender.Compiler.BigintCachedMemoryClaim) :
    Airbender.Compiler.BigintCachedMemorySatisfiableClaim →
    ∃ (challenges : Airbender.Compiler.NativeMemory.Challenges Airbender.Compiler.NativeArithmetic.F)
      (values : Airbender.GKRAddress → Airbender.Compiler.NativeArithmetic.F)
      (row : Airbender.Delegation.Row Airbender.babyBearModulus),
      Airbender.Compiler.NativeMemory.RamProducts Airbender.Compiler.Captures.Bigint.imported.circuit challenges values
        (row.assignment row.columns.execute) (Airbender.Compiler.NativeMemory.standardReads row)
        (Airbender.Compiler.NativeMemory.standardWrites row) :=
  fun ⟨challenges, physical, values, row, selected, nativeHolds, placement, extension⟩ =>
    ⟨challenges, values, row, claim challenges physical values row selected nativeHolds placement extension⟩

example : Airbender.Compiler.BlakeGCachedMemorySatisfiableClaim := Airbender.Compiler.blakeG_cached_memory_satisfiable

example (claim : Airbender.Compiler.BlakeGCachedMemoryClaim) :
    Airbender.Compiler.BlakeGCachedMemorySatisfiableClaim →
    ∃ (challenges : Airbender.Compiler.NativeMemory.Challenges Airbender.Compiler.NativeArithmetic.F)
      (values : Airbender.GKRAddress → Airbender.Compiler.NativeArithmetic.F)
      (row : Airbender.Delegation.Row Airbender.babyBearModulus),
      Airbender.Compiler.NativeMemory.RamProducts Airbender.Compiler.Captures.BlakeG.imported.circuit challenges values
        (row.assignment row.columns.execute) (Airbender.Compiler.NativeMemory.standardReads row)
        (Airbender.Compiler.NativeMemory.standardWrites row) :=
  fun ⟨challenges, physical, values, row, selected, nativeHolds, placement, extension⟩ =>
    ⟨challenges, values, row, claim challenges physical values row selected nativeHolds placement extension⟩

example : Airbender.Compiler.BlakeRoundCachedMemorySatisfiableClaim := Airbender.Compiler.blakeRound_cached_memory_satisfiable

example (claim : Airbender.Compiler.BlakeRoundCachedMemoryClaim) :
    Airbender.Compiler.BlakeRoundCachedMemorySatisfiableClaim →
    ∃ (challenges : Airbender.Compiler.NativeMemory.Challenges Airbender.Compiler.NativeArithmetic.F)
      (values : Airbender.GKRAddress → Airbender.Compiler.NativeArithmetic.F)
      (row : Airbender.Delegation.Row Airbender.babyBearModulus),
      Airbender.Compiler.NativeMemory.RamProducts Airbender.Compiler.Captures.BlakeRound.imported.circuit challenges values
        (row.assignment row.columns.execute) (Airbender.Compiler.NativeMemory.standardReads row)
        (Airbender.Compiler.NativeMemory.standardWrites row) :=
  fun ⟨challenges, physical, values, row, selected, nativeHolds, placement, extension⟩ =>
    ⟨challenges, values, row, claim challenges physical values row selected nativeHolds placement extension⟩

example : Airbender.Compiler.KeccakColumnParityCachedMemorySatisfiableClaim := Airbender.Compiler.keccakColumnParity_cached_memory_satisfiable

example (claim : Airbender.Compiler.KeccakColumnParityCachedMemoryClaim) :
    Airbender.Compiler.KeccakColumnParityCachedMemorySatisfiableClaim →
    ∃ (challenges : Airbender.Compiler.NativeMemory.Challenges Airbender.Compiler.NativeArithmetic.F)
      (values : Airbender.GKRAddress → Airbender.Compiler.NativeArithmetic.F)
      (row : Airbender.Keccak.Split.Native.Row Airbender.babyBearModulus),
      Airbender.Compiler.NativeMemory.RamProducts Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit challenges values
        (row.assignment row.columns.execute) (Airbender.Compiler.NativeMemory.splitReads row)
        (Airbender.Compiler.NativeMemory.splitWrites row) :=
  fun ⟨challenges, physical, values, row, selected, nativeHolds, placement, extension⟩ =>
    ⟨challenges, values, row, claim challenges physical values row selected nativeHolds placement extension⟩

example : Airbender.Compiler.KeccakThetaRhoCachedMemorySatisfiableClaim := Airbender.Compiler.keccakThetaRho_cached_memory_satisfiable

example (claim : Airbender.Compiler.KeccakThetaRhoCachedMemoryClaim) :
    Airbender.Compiler.KeccakThetaRhoCachedMemorySatisfiableClaim →
    ∃ (challenges : Airbender.Compiler.NativeMemory.Challenges Airbender.Compiler.NativeArithmetic.F)
      (values : Airbender.GKRAddress → Airbender.Compiler.NativeArithmetic.F)
      (row : Airbender.Keccak.Split.Native.Row Airbender.babyBearModulus),
      Airbender.Compiler.NativeMemory.RamProducts Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit challenges values
        (row.assignment row.columns.execute) (Airbender.Compiler.NativeMemory.splitReads row)
        (Airbender.Compiler.NativeMemory.splitWrites row) :=
  fun ⟨challenges, physical, values, row, selected, nativeHolds, placement, extension⟩ =>
    ⟨challenges, values, row, claim challenges physical values row selected nativeHolds placement extension⟩

example : Airbender.Compiler.KeccakChi5CachedMemorySatisfiableClaim := Airbender.Compiler.keccakChi5_cached_memory_satisfiable

example (claim : Airbender.Compiler.KeccakChi5CachedMemoryClaim) :
    Airbender.Compiler.KeccakChi5CachedMemorySatisfiableClaim →
    ∃ (challenges : Airbender.Compiler.NativeMemory.Challenges Airbender.Compiler.NativeArithmetic.F)
      (values : Airbender.GKRAddress → Airbender.Compiler.NativeArithmetic.F)
      (row : Airbender.Keccak.Split.Native.Row Airbender.babyBearModulus),
      Airbender.Compiler.NativeMemory.RamProducts Airbender.Compiler.Captures.KeccakChi5.imported.circuit challenges values
        (row.assignment row.columns.execute) (Airbender.Compiler.NativeMemory.splitReads row)
        (Airbender.Compiler.NativeMemory.splitWrites row) :=
  fun ⟨challenges, physical, values, row, selected, nativeHolds, placement, extension⟩ =>
    ⟨challenges, values, row, claim challenges physical values row selected nativeHolds placement extension⟩

-- RAM permutation composition.

example : Airbender.Compiler.UnrolledMemoryCompositionSatisfiableClaim :=
  Airbender.Compiler.unrolled_memory_composition_satisfiable

example : Airbender.Compiler.UnifiedMemoryCompositionSatisfiableClaim :=
  Airbender.Compiler.unified_memory_composition_satisfiable

-- Certificate RAM outputs.

example : Airbender.Compiler.ProgramCertificateRamProductsSatisfiableClaim := Airbender.Compiler.program_certificate_ram_products_satisfiable

example : Airbender.Compiler.UnifiedCertificateRamProductsSatisfiableClaim := Airbender.Compiler.unified_certificate_ram_products_satisfiable

example : Airbender.Compiler.WorkerCertificateRamProductsSatisfiableClaim := Airbender.Compiler.worker_certificate_ram_products_satisfiable

-- Native targets with the single RAM permutation.

example : Airbender.Trace.Machine.Native.UnrolledFullFromNativePermutationSatisfiableClaim := Airbender.Trace.Machine.Native.unrolled_full_from_native_permutation_satisfiable

example : Airbender.Trace.Machine.Native.UnrolledReducedFromNativePermutationSatisfiableClaim := Airbender.Trace.Machine.Native.unrolled_reduced_from_native_permutation_satisfiable

example : Airbender.Trace.Machine.Native.UnifiedFromNativePermutationSatisfiableClaim := Airbender.Trace.Machine.Native.unified_from_native_permutation_satisfiable

example : Airbender.Trace.Machine.Native.PaddedUnrolledFullFromNativePermutationSatisfiableClaim := Airbender.Trace.Machine.Native.padded_unrolled_full_from_native_permutation_satisfiable

example : Airbender.Trace.Machine.Native.PaddedUnrolledReducedFromNativePermutationSatisfiableClaim := Airbender.Trace.Machine.Native.padded_unrolled_reduced_from_native_permutation_satisfiable

example : Airbender.Trace.Machine.Native.PaddedUnifiedFromNativePermutationSatisfiableClaim := Airbender.Trace.Machine.Native.padded_unified_from_native_permutation_satisfiable

example (claim : Airbender.Compiler.UnifiedMemoryCompositionClaim) :
    Airbender.Compiler.UnifiedMemoryCompositionSatisfiableClaim →
    ∃ (trace : Airbender.Trace.UnifiedTrace Airbender.babyBearModulus)
      (workers : Airbender.Trace.Machine.WorkerPools Airbender.babyBearModulus),
      trace.rows ≠ [] ∧
      (trace.initial :: trace.rows.map Airbender.Trace.Row.finish).Perm
        (trace.terminal :: trace.rows.map Airbender.Trace.Row.start) ∧
      Airbender.Delegation.Requests.Matching
        ((trace.rows.filter fun row => decide (Airbender.UnifiedReduced.Caller.Selected row.assignment)).map
          fun row => Airbender.UnifiedReduced.Caller.request row.assignment) workers.fulfillments ∧
      (trace.initialMemory ++ (Airbender.Trace.Machine.unifiedSteps trace ++ workers.steps).map Prod.snd).Perm
        (trace.terminalMemory ++ (Airbender.Trace.Machine.unifiedSteps trace ++ workers.steps).map Prod.fst) :=
  fun ⟨config, trace, workers, initial, cells, program, layout, inits, boot, callers, machine, production, nonempty⟩ =>
    ⟨trace, workers, nonempty, claim config trace workers initial cells program layout inits boot callers machine production⟩

example : Airbender.InitsTeardowns.SharedBytesSatisfiableClaim := Airbender.InitsTeardowns.shared_bytes_satisfiable

example (claim : Airbender.InitsTeardowns.SharedBytesClaim) : Airbender.InitsTeardowns.SharedBytesSatisfiableClaim →
    Airbender.InitsTeardowns.sharedLayoutCircuit.placement_data.entries.size = 32 :=
  fun ⟨_, decoded, entries⟩ => Except.ok.inj (decoded.symm.trans claim) ▸ entries
