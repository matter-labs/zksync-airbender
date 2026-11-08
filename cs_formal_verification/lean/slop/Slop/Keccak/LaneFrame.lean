module
public import Human.Trace.Workers.Keccak.Permutation
public import Slop.Keccak.StateCells

@[expose] public section

namespace Airbender.Keccak.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384

theorem lane_half_address_injective (pointer : BitVec 32) (a b : Fin 31) (h k : Fin 2)
    (same : pointer + BitVec.ofNat 32 (8 * a.val + 4 * h.val) =
      pointer + BitVec.ofNat 32 (8 * b.val + 4 * k.val)) : a = b ∧ h = k := by
  have bits := (BitVec.add_right_inj pointer).mp same
  have values := congrArg BitVec.toNat bits
  have ab := a.isLt
  have bb := b.isLt
  have hb := h.isLt
  have kb := k.isLt
  simp only [BitVec.toNat_ofNat] at values
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at values
  exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

private def halfPort (i : Fin 12) : MemoryPort :=
  importedConstraintsMemoryPorts[2 + i.val]'(by change 2 + i.val < 14; omega)

private theorem half_port_shape (i : Fin 12) :
    (halfPort i).address = .indirect importedConstraintsIndirectPorts[i] := by
  fin_cases i <;> rfl

end Airbender.Keccak.Proofs
