import Airbender.Proofs.UnifiedReduced.History

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

theorem register_effects [Fact p.Prime] {setup : Table (ZMod p) (fields 10)}
    {w : Nat → ZMod p} {cells : List Cell} {rd : BitVec 5}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (noStore : w 29 = 0) (destinationIndex : (w 7).val = rd.toNat)
    (epoch : Nat) (output : Output)
    (result : output.destination = Word.mk (w 50).val (w 51).val)
    {before after : State}
    (history : SailHistory cells (rowEvents epoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse before after) :
    run (projectedStep (.Regidx rd) output)
      (retiredState before (Word.mk (w 0).val (w 1).val).toBitVec) =
      .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after output.pc.toBitVec) := by
  have low := Verification.assertion_of_holds holds ⟨31, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds holds ⟨32, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, noStore] at low high
  have location : w 44 = w 7 := by linear_combination low
  have upper : w 45 = 0 := by linear_combination high
  have normalized := retired_state_history history (Word.mk (w 0).val (w 1).val).toBitVec
  have projection := register_history_projection_at (rd := rd) epoch
    (first := importedConstraintsMemoryPorts[0]) (second := importedConstraintsMemoryPorts[1])
    (destination := importedConstraintsMemoryPorts[2]) rfl rfl
    (by simp [importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode,
      noStore, location, upper, pairCode, destinationIndex]) output
    (by simp [result, importedConstraintsMemoryPorts, MemoryPort.writeCode,
      pairCode, memoryWord, Nat.unpair_pair, Word.toBitVec, Word.value]) normalized
  simpa only [retired_state_overwrite] using projection

end Airbender.UnifiedReduced.Proofs
