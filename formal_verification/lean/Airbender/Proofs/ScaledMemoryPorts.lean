import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.MemoryPorts

namespace Airbender.Verification
open Arithmetic
set_option warningAsError true

/-- A variable-index port may also add a fixed byte offset. This covers both
    words of a 64-bit lane and reuses the shared native word interpretation. -/
theorem IndirectPort.scaled_address {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 65536)
    {port : IndirectPort} {w : Nat → ZMod p} {base : Word} {index column : Nat}
    (variableOffset : port.offsetColumn = some column)
    (mapping : base = ⟨(w port.baseColumns[0]).val, (w port.baseColumns[1]).val⟩)
    (offset : (w column).val = index)
    (noCarry : base.lo + port.scale * index + port.constant < limbBase) :
    port.address w = base.toBitVec + BitVec.ofNat 32 (port.scale * index + port.constant) := by
  have fieldBase : w port.baseColumns[0] = (base.lo : ZMod p) := by
    rw [mapping]
    exact (ZMod.natCast_zmod_val _).symm
  have fieldOffset : w column = (index : ZMod p) := by
    rw [← offset]
    exact (ZMod.natCast_zmod_val _).symm
  have encoded : w port.baseColumns[0] + (port.scale : ZMod p) * w column + port.constant =
      ((base.lo + port.scale * index + port.constant : Nat) : ZMod p) := by
    rw [fieldBase, fieldOffset]
    simp
  simp only [IndirectPort.address, variableOffset, Option.elim_some]
  rw [encoded, ZMod.val_natCast_of_lt (by unfold limbBase at noCarry; omega)]
  apply Word.toBitVec_add_of_value
  have high : base.hi = (w port.baseColumns[1]).val := congrArg Word.hi mapping
  simp [Word.value, high]
  omega

end Airbender.Verification
