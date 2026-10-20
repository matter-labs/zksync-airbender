import Human.Circuits.UnifiedReduced.Control
import Slop.UnifiedReduced.Retirement
import Slop.UnifiedReduced.Decoder

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

theorem register_retirement [Fact p.Prime] (hp : 524288 < p)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p} {cells : List Cell}
    {entry : ProgramEntry} {rd : BitVec 5}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (fields : decoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query)
    (registerMask : entry.data.mask < 262144) (destination : entry.data.rd = rd)
    (epoch : Nat) {before after : State}
    (history : SailHistory cells (rowEvents epoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse before after)
    {clause : SailRV32.SailM SailRV32.ExecutionResult}
    (spec : stepSpec (retiredState before (Control.initialPC w).toBitVec) clause (.Regidx rd)
      ⟨Control.destination w, Control.finalPC w⟩) :
    run (normalStep clause) (retiredState before (Control.initialPC w).toBitVec) =
      .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (Control.finalPC w).toBitVec) := by
  have flags := decoder_selectors hp holds (decoder_field_bounds fields).2.1 query
  have noStore : w 29 = 0 := by
    have bit := flags 18
    have zero : entry.data.mask.testBit 18 = false := Nat.testBit_eq_false_of_lt registerMask
    simpa [importedConstraintsDecoderColumns, zero] using bit
  have index := congrArg (fun q : Vector (ZMod p) 9 => q[4]) query
  change w 7 = (entry.data.rd.toNat : ZMod p) at index
  have destinationIndex : (w 7).val = rd.toNat := by
    rw [index, destination, ZMod.val_natCast, Nat.mod_eq_of_lt]
    have := rd.isLt
    omega
  obtain ⟨written, normal, projected⟩ := spec
  have effects := register_effects holds noStore destinationIndex epoch
    ⟨Control.destination w, Control.finalPC w⟩ rfl history
  have same := (EStateM.Result.ok.inj (projected.symm.trans effects)).2
  simpa only [same] using normal

end Airbender.UnifiedReduced.Proofs
