-- Each `…SatisfiableClaim` restates the premises of its claim. Applying the claim to the satisfying data
-- type-checks only if they are exactly the claim's premises; the result is the claim's conclusion on that data.
import Human.Trace.Delegation.RVTheorems
import Human.Trace.ZeroTimestamp
import Human.Trace.WritesRangeChecked
import Human.Trace.Workers.Bigint.RVTheorems
import Human.Trace.RVSoundness
import Human.Trace.TeardownBounds

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

end Checks.Satisfiable
