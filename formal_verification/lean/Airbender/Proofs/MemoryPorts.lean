import Airbender.Review.MemoryPorts
import Airbender.Proofs.Arithmetic.Word

namespace Airbender.Verification
open Arithmetic

/-- A word index in a 64-byte aligned block cannot carry into the next limb. -/
theorem block64_offset_bound {low index : Nat} (bound : low < limbBase)
    (aligned : low % 64 = 0) (indexBound : index < 16) : low + 4 * index < limbBase := by
  unfold limbBase at *
  omega

/-- Interpret the imported low-limb address formula as native word addition,
    after excluding carry and field wrap. Shared by indirect-memory families. -/
theorem IndirectPort.word_address {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    {port : IndirectPort} {w : Nat → ZMod p} {base : Word} {index : Nat}
    (scale : port.scale = 4) (constant : port.constant = 0)
    (mapping : base = ⟨(w port.baseColumns[0]).val, (w port.baseColumns[1]).val⟩)
    (offset : (w port.offsetColumn).val = index)
    (bound : base.lo < limbBase) (aligned : base.lo % 64 = 0) (indexBound : index < 16) :
    port.address w = base.toBitVec + BitVec.ofNat 32 (4 * index) := by
  have low := block64_offset_bound bound aligned indexBound
  have fieldBase : w port.baseColumns[0] = (base.lo : ZMod p) := by
    rw [mapping]
    exact (ZMod.natCast_zmod_val _).symm
  have fieldOffset : w port.offsetColumn = (index : ZMod p) := by
    rw [← offset]
    exact (ZMod.natCast_zmod_val _).symm
  have encoded : w port.baseColumns[0] + (port.scale : ZMod p) * w port.offsetColumn + port.constant =
      ((base.lo + 4 * index : Nat) : ZMod p) := by
    rw [fieldBase, fieldOffset, scale, constant]
    simp
  unfold IndirectPort.address
  rw [encoded, ZMod.val_natCast_of_lt (by unfold limbBase at low; omega)]
  apply Word.toBitVec_add_of_value
  have high : base.hi = (w port.baseColumns[1]).val := congrArg Word.hi mapping
  simp [Word.value, high]
  omega

end Airbender.Verification
