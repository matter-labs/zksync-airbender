import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Circuits.UnifiedReduced.Control
import Airbender.Proofs.UnifiedReduced.History
import Airbender.Proofs.UnifiedReduced.CustomDecoder

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
  have low := Verification.assertion_of_holds holds ⟨28, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds holds ⟨29, by rw [constraint_count]; decide⟩
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

theorem custom_register_retirement [Fact p.Prime] (hp : FieldCapacity.NoWrap p 524288)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p} {cells : List Cell}
    {entry : ProgramEntry} {rd : SailRV32.regidx}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (fields : customDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query)
    (destination : (.Regidx entry.data.rd : SailRV32.regidx) = rd)
    (epoch : Nat) {before after : State}
    (history : SailHistory cells (rowEvents epoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse before after)
    {clause : SailRV32.SailM SailRV32.ExecutionResult}
    (spec : stepSpec (retiredState before (Control.initialPC w).toBitVec) clause rd
      ⟨Control.destination w, Control.finalPC w⟩) :
    run (normalStep clause) (retiredState before (Control.initialPC w).toBitVec) =
      .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (Control.finalPC w).toBitVec) := by
  have noStore : w 29 = 0 := by
    have flag := decoder_selectors hp core (custom_field_bounds fields).2.1 query 18
    rcases custom_field_mask fields with mask | mask
    all_goals simpa [mask, importedConstraintsDecoderColumns, Nat.testBit, Nat.shiftRight_eq_div_pow] using flag
  have indices := native_query_indices (by dsimp [limbBase]; omega) query
  obtain ⟨final, normal, projected⟩ := spec
  have effects := register_effects core noStore indices.2.2 epoch
    ⟨Control.destination w, Control.finalPC w⟩ rfl history
  rw [destination] at effects
  have same := (EStateM.Result.ok.inj (projected.symm.trans effects)).2
  simpa only [same] using normal

end Airbender.UnifiedReduced.Proofs
