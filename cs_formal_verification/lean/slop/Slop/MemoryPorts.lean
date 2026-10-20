import Human.Helpers.Memory.IndirectPorts
import Slop.Arithmetic.Word

namespace Airbender.Verification
open Arithmetic

/-- An aligned block that tiles a limb cannot cross its boundary at an offset
    inside that block. Shared by 64- and 128-byte ABI regions. -/
theorem block_offset_bound {block low offset : Nat} (tiles : limbBase % block = 0)
    (bound : low < limbBase) (aligned : low % block = 0) (inside : offset < block) :
    low + offset < limbBase := by
  have lowEq := Nat.mod_add_div low block
  have sizeEq := Nat.mod_add_div limbBase block
  rw [aligned] at lowEq
  rw [tiles] at sizeEq
  have quotient : low / block < limbBase / block := by
    by_contra impossible
    have order : limbBase / block ≤ low / block := by omega
    have product := Nat.mul_le_mul_left block order
    omega
  calc
    _ < low + block := Nat.add_lt_add_left inside _
    _ = block * (low / block) + block := by omega
    _ = block * (low / block + 1) := by ring
    _ ≤ block * (limbBase / block) := Nat.mul_le_mul_left _ (by omega)
    _ = limbBase := by omega

/-- A word index in a 64-byte aligned block cannot carry into the next limb. -/
theorem block64_offset_bound {low index : Nat} (bound : low < limbBase)
    (aligned : low % 64 = 0) (indexBound : index < 16) : low + 4 * index < limbBase := by
  exact block_offset_bound (block := 64) (by decide) bound aligned (by omega)

/-- Interpret the imported low-limb address formula as native word addition,
    after excluding carry and field wrap. Shared by indirect-memory families. -/
theorem IndirectPort.word_address {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    {port : IndirectPort} {w : Nat → ZMod p} {base : Word} {index column : Nat}
    (scale : port.scale = 4) (constant : port.constant = 0)
    (variableOffset : port.offsetColumn = some column)
    (mapping : base = ⟨(w port.baseColumns[0]).val, (w port.baseColumns[1]).val⟩)
    (offset : (w column).val = index)
    (bound : base.lo < limbBase) (aligned : base.lo % 64 = 0) (indexBound : index < 16) :
    port.address w = base.toBitVec + BitVec.ofNat 32 (4 * index) := by
  have low := block64_offset_bound bound aligned indexBound
  have fieldBase : w port.baseColumns[0] = (base.lo : ZMod p) := by
    rw [mapping]
    exact (ZMod.natCast_zmod_val _).symm
  have fieldOffset : w column = (index : ZMod p) := by
    rw [← offset]
    exact (ZMod.natCast_zmod_val _).symm
  have encoded : w port.baseColumns[0] + (port.scale : ZMod p) * w column + port.constant =
      ((base.lo + 4 * index : Nat) : ZMod p) := by
    rw [fieldBase, fieldOffset, scale, constant]
    simp
  simp only [IndirectPort.address, variableOffset, Option.elim_some]
  rw [encoded, ZMod.val_natCast_of_lt (by unfold limbBase at low; omega)]
  apply Word.toBitVec_add_of_value
  have high : base.hi = (w port.baseColumns[1]).val := congrArg Word.hi mapping
  simp [Word.value, high]
  omega

/-- Constant-offset ports use the same native word interpretation. The proof
    needs no offset witness and explicitly excludes low-limb carry. -/
theorem IndirectPort.constant_address {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    {port : IndirectPort} {w : Nat → ZMod p} {base : Word}
    (fixed : port.offsetColumn = none)
    (mapping : base = ⟨(w port.baseColumns[0]).val, (w port.baseColumns[1]).val⟩)
    (noCarry : base.lo + port.constant < limbBase) :
    port.address w = base.toBitVec + BitVec.ofNat 32 port.constant := by
  have fieldBase : w port.baseColumns[0] = (base.lo : ZMod p) := by
    rw [mapping]
    exact (ZMod.natCast_zmod_val _).symm
  have encoded : w port.baseColumns[0] + (port.constant : ZMod p) =
      ((base.lo + port.constant : Nat) : ZMod p) := by rw [fieldBase]; simp
  simp only [IndirectPort.address, fixed, Option.elim_none, mul_zero, add_zero]
  rw [encoded, ZMod.val_natCast_of_lt (by unfold limbBase at noCarry; omega)]
  apply Word.toBitVec_add_of_value
  have high : base.hi = (w port.baseColumns[1]).val := congrArg Word.hi mapping
  simp [Word.value, high]
  omega

end Airbender.Verification
