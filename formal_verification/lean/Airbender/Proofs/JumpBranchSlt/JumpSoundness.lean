import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.JumpBranchSlt.JumpRowModel
import Airbender.Proofs.JumpBranchSlt.Jump
import Airbender.Proofs.Sail.JumpRetirement

namespace Airbender.JumpBranchSlt.Proofs
open Airbender.Arithmetic
open Airbender.Reference.RiscV
open Airbender.Reference.Sail

/-- JAL and JALR share target/link algebra, native writes and retirement. -/
theorem jump_soundness {p : Nat} [Fact p.Prime] (hp : FieldCapacity.NativeRomCapacity p) :
    Jump.rowCircuitModel.SoundnessUnder (Jump.RowInterfaces (p := p)) Jump.spec := by
  intro input output w ⟨interface, h, mapping⟩
  have selected : w 11 + w 12 = 1 := by
    rw [interface.selected.1, interface.selected.2]
    cases input.instruction.indirect <;> simp
  have link := (jump_link hp h selected interface.otherSelectors mapping.initialPC
    interface.initialPCLoBound).1
  have destination : output.destination = ⟨(w 30).val, (w 31).val⟩ := by
    exact congrArg₂ Word.mk mapping.destination.1 mapping.destination.2
  rw [← destination] at link
  obtain ⟨pc, aligned⟩ := jump_pc hp input.instruction.indirect h interface.selected
    interface.otherSelectors mapping.targetWords interface.baseLoBound interface.sourceHiBound
    interface.offsetBound interface.directEven interface.finalPCHiBound
  have observedLink : output.destination.toBitVec =
      if input.rd = Sail.zeroRegister then 0 else input.pc.toBitVec + 4 := by
    by_cases zero : input.rd = Sail.zeroRegister
    · have masked := interface.zeroDestination.mpr zero
      simpa [zero, masked] using link
    · have unmasked : w 15 ≠ 1 := fun masked => zero (interface.zeroDestination.mp masked)
      simpa [zero, unmasked] using link
  exact Sail.retire_jump input output observedLink pc aligned interface.signExtension
    interface.sourceRead interface.pcRead interface.misaRead interface.landingPad

end Airbender.JumpBranchSlt.Proofs
