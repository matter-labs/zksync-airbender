-- Each `…SatisfiableClaim` restates the premises of its claim. Applying the claim to the satisfying data
-- type-checks only if they are exactly the claim's premises; the result is the claim's conclusion on that data.
import Human.Trace.Delegation.RVTheorems
import Human.Trace.ZeroTimestamp
import Human.Trace.WritesRangeChecked
import Human.Trace.Workers.Bigint.RVTheorems

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

end Checks.Satisfiable
