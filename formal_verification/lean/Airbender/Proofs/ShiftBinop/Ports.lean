import Airbender.Proofs.ShiftBinop.Soundness
import Airbender.Proofs.Trace.BytePorts

namespace Airbender.ShiftBinop.Proofs
open Arithmetic

/-- The fixed query determines the immediate's upper sign byte. -/
theorem binary_sign_byte {p : Nat} [Fact p.Prime] (hp : 256 < p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 11 = 0 ∧ w 12 = 1) :
    (w 9).val < 256 ∧ (w 35).val = if (w 9).val < 128 then 0 else 255 := by
  have equations (i : Fin 4) := Verification.assertion_of_holds h
    ⟨1 + i.val, by rw [constraint_count]; have := i.isLt; omega⟩
  have a := equations 0
  have b := equations 1
  have tag := equations 3
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, selected.1, selected.2] at a b tag
  have wa : w 52 = w 9 := by linear_combination a
  have wb : w 53 = w 35 := by linear_combination b
  have wt : w 55 = 3 := by linear_combination tag
  have query := Verification.lookup_of_holds h ⟨2, by rw [lookup_count]; decide⟩
  have values := Verification.binary_sign_lookup hp query
    (by simpa [Expression.eval, Verification.environment] using wt)
  simpa [Expression.eval, Verification.environment, wa, wb] using values

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

/-- A register form's zero immediate forces a zero sign scratch byte, so the
    bounded binary operands are exactly the native rs2 register word. -/
theorem binary_register_right_bytes {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 11 = 0 ∧ w 12 = 1) (tag : Nat)
    (validTag : tag = 4 ∨ tag = 6 ∨ tag = 7) (funct3 : w 10 = (tag : ZMod p))
    (immediate : w 8 = 0 ∧ w 9 = 0) :
    ∀ i : Fin 4, w (25 + i.val) +
      (if i.val = 0 then w 8 else if i.val = 1 then w 9 else w 35) =
      ((Trace.Proofs.memoryWord (importedConstraintsMemoryPorts[1].readCode w)).extractLsb'
        (8 * i.val) 8).toNat := by
  have sign := (binary_sign_byte (by omega) h selected).2
  have zero : w 35 = 0 := by
    apply ZMod.val_injective
    simpa [immediate.2] using sign
  have bounds : ∀ i : Fin 4, (w (#v[25, 26, 27, 28] : Vector Nat 4)[i]).val < 256 := by
    intro i
    have small := (binary_query_values (by omega) h selected tag validTag funct3 i).2.1
    fin_cases i <;> simpa [immediate.1, immediate.2, zero] using small
  intro i
  have byte := Trace.Proofs.byte_port_bytes hp #v[25, 26, 27, 28] bounds i
  fin_cases i <;>
    simpa [importedConstraintsMemoryPorts, Trace.MemoryPort.readCode,
      immediate.1, immediate.2, zero] using byte

/-- For an immediate form, the native x0 port packs to zero. Raw byte columns
    may cancel in the field; only lookup-bounded effective bytes are decoded. -/
theorem binary_immediate_right_bytes {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 11 = 0 ∧ w 12 = 1) (tag : Nat)
    (validTag : tag = 4 ∨ tag = 6 ∨ tag = 7) (funct3 : w 10 = (tag : ZMod p))
    (imm : BitVec 12)
    (immediate : w 8 = ((SailRV32.Functions.sign_extend (m := 32) imm).extractLsb' 0 8).toNat ∧
      w 9 = ((SailRV32.Functions.sign_extend (m := 32) imm).extractLsb' 8 8).toNat)
    (zeroRead : importedConstraintsMemoryPorts[1].readCode w = Nat.pair 0 0) :
    ∀ i : Fin 4, w (25 + i.val) +
      (if i.val = 0 then w 8 else if i.val = 1 then w 9 else w 35) =
      ((SailRV32.Functions.sign_extend (m := 32) imm).extractLsb' (8 * i.val) 8).toNat := by
  let x := SailRV32.Functions.sign_extend (m := 32) imm
  let byte (i : Fin 4) := w (25 + i.val) +
    (if i.val = 0 then w 8 else if i.val = 1 then w 9 else w 35)
  let target (i : Fin 4) : ZMod p := (x.extractLsb' (8 * i.val) 8).toNat
  have small (i : Fin 4) : (byte i).val < 256 :=
    (binary_query_values (by omega) h selected tag validTag funct3 i).2.1
  have targetSmall (i : Fin 4) : (target i).val < 256 := by
    rw [show target i = ((x.extractLsb' (8 * i.val) 8).toNat : ZMod p) from rfl,
      ZMod.val_natCast, Nat.mod_eq_of_lt (by have := (x.extractLsb' (8 * i.val) 8).isLt; omega)]
    exact (x.extractLsb' (8 * i.val) 8).isLt
  have sign := (binary_sign_byte (by omega) h selected).2
  have signValue : (w 35).val = if (x.extractLsb' 8 8).toNat < 128 then 0 else 255 := by
    rw [immediate.2, ZMod.val_natCast,
      Nat.mod_eq_of_lt (by have := (x.extractLsb' 8 8).isLt; omega)] at sign
    exact sign
  have upper (i : Fin 2) : w 35 = ((x.extractLsb' (16 + 8 * i.val) 8).toNat : ZMod p) := by
    apply ZMod.val_injective
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by have := (x.extractLsb' (16 + 8 * i.val) 8).isLt; omega)]
    exact signValue.trans (Reference.Sail.sign_extend_high_bytes imm i).symm
  change Nat.pair (w 25 + 256 * w 26).val (w 27 + 256 * w 28).val = Nat.pair 0 0 at zeroRead
  have raw := Nat.pair_eq_pair.mp zeroRead
  have rawLow : w 25 + 256 * w 26 = 0 := by
    apply ZMod.val_injective
    simpa using raw.1
  have rawHigh : w 27 + 256 * w 28 = 0 := by
    apply ZMod.val_injective
    simpa using raw.2
  have low := Trace.Proofs.packed_bytes_unique hp (small 0) (small 1)
    (targetSmall 0) (targetSmall 1) (show byte 0 + 256 * byte 1 = target 0 + 256 * target 1 by
      rw [show target 0 = w 8 from immediate.1.symm,
        show target 1 = w 9 from immediate.2.symm]
      change w 25 + w 8 + 256 * (w 26 + w 9) = w 8 + 256 * w 9
      linear_combination rawLow)
  have high := Trace.Proofs.packed_bytes_unique hp (small 2) (small 3)
    (targetSmall 2) (targetSmall 3) (show byte 2 + 256 * byte 3 = target 2 + 256 * target 3 by
      rw [show target 2 = w 35 from (upper 0).symm,
        show target 3 = w 35 from (upper 1).symm]
      change w 27 + w 35 + 256 * (w 28 + w 35) = w 35 + 256 * w 35
      linear_combination rawHigh)
  intro i
  fin_cases i
  · exact low.1
  · exact low.2
  · exact high.1
  · exact high.2

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
