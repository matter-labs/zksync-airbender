import Airbender.Proofs.ShiftBinop.Soundness
import Airbender.Proofs.Trace.BytePorts

namespace Airbender.ShiftBinop.Proofs
open Arithmetic

/-- Canonical output limbs follow from native byte queries and assembly;
    neither source-word mapping nor the desired instruction result is a premise. -/
theorem binary_written_bounds {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 11 = 0 ∧ w 12 = 1) (tag : Nat)
    (validTag : tag = 4 ∨ tag = 6 ∨ tag = 7) (funct3 : w 10 = (tag : ZMod p)) :
    (w 31).val < limbBase ∧ (w 32).val < limbBase := by
  have bounds (i : Fin 4) : (w (36 + i.val)).val < 256 :=
    (binary_query_values (by omega) h selected tag validTag funct3 i).2.2.1
  have b0 : (w 36).val < 256 := bounds 0
  have b1 : (w 37).val < 256 := bounds 1
  have b2 : (w 38).val < 256 := bounds 2
  have b3 : (w 39).val < 256 := bounds 3
  have low := Verification.assertion_of_holds h ⟨41, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds h ⟨42, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, selected.1, selected.2] at low high
  have lo : w 31 = w 36 + 256 * w 37 := by linear_combination -low
  have hi : w 32 = w 38 + 256 * w 39 := by linear_combination -high
  rw [lo, hi, Trace.Proofs.packed_bytes hp b0 b1, Trace.Proofs.packed_bytes hp b2 b3]
  dsimp [limbBase]
  constructor <;> omega

private theorem left_bytes_of_bounds {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    {w : Nat → ZMod p} (small : ∀ i : Fin 4, (w (19 + i.val)).val < 256) :
    ∀ i : Fin 4, w (19 + i.val) =
      ((Trace.Proofs.memoryWord (importedConstraintsMemoryPorts[0].readCode w)).extractLsb'
        (8 * i.val) 8).toNat := by
  have bounds : ∀ i : Fin 4, (w (#v[19, 20, 21, 22] : Vector Nat 4)[i]).val < 256 := by
    intro i
    have bound := small i
    fin_cases i <;> simpa using bound
  intro i
  have byte := Trace.Proofs.byte_port_bytes hp #v[19, 20, 21, 22] bounds i
  fin_cases i <;> simpa [importedConstraintsMemoryPorts, Trace.MemoryPort.readCode] using byte

/-- The source read is the Rust-packed native word, reconstructed from lookup
    bounds. This connection is shared by register and immediate binary forms. -/
theorem binary_left_bytes {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 11 = 0 ∧ w 12 = 1) (tag : Nat)
    (validTag : tag = 4 ∨ tag = 6 ∨ tag = 7) (funct3 : w 10 = (tag : ZMod p)) :
    ∀ i : Fin 4, w (19 + i.val) =
      ((Trace.Proofs.memoryWord (importedConstraintsMemoryPorts[0].readCode w)).extractLsb'
        (8 * i.val) 8).toNat :=
  left_bytes_of_bounds hp fun i => (binary_query_values (by omega) h selected tag validTag funct3 i).1

/-- Shift source bytes are bound in exactly the same native memory model. -/
theorem shift_left_bytes {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 11 = 1 ∧ w 12 = 0) :
    ∀ i : Fin 4, w (19 + i.val) =
      ((Trace.Proofs.memoryWord (importedConstraintsMemoryPorts[0].readCode w)).extractLsb'
        (8 * i.val) 8).toNat :=
  left_bytes_of_bounds hp (shift_source_bounds (by omega) h selected)

/-- Only the ranged low source bytes are used to derive the shift amount;
    the unused high source columns carry no extra range assumption. -/
theorem shift_right_low_byte {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 11 = 1 ∧ w 12 = 0) :
    w 25 = ((Trace.Proofs.memoryWord (importedConstraintsMemoryPorts[1].readCode w)).extractLsb'
      0 8).toNat := by
  have small := shift_amount (by omega) h selected
  have bounds : ∀ i : Fin 2, (w (#v[25, 26, 27, 28] : Vector Nat 4)[i.val]).val < 256 := by
    intro i
    fin_cases i
    · exact small.1
    · exact small.2.1
  have byte := Trace.Proofs.byte_port_low_bytes hp #v[25, 26, 27, 28] bounds 0
  simpa [importedConstraintsMemoryPorts, Trace.MemoryPort.readCode] using byte

end Airbender.ShiftBinop.Proofs
