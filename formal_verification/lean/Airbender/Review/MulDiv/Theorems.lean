import Airbender.Proofs.MulDiv
import Airbender.Proofs.MulDiv.Soundness
import Airbender.Proofs.MulDiv.Product
import Airbender.Proofs.BabyBear

namespace Airbender.MulDiv
open Airbender.Arithmetic

theorem local_flags {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    (w 4 = 0 ∨ w 4 = 1) ∧ ∀ i : Fin 4, w (10 + i.val) = 0 ∨ w (10 + i.val) = 1 :=
  Proofs.local_flags h

/-- Output, extra, comparison and final-PC limbs are bounded by the eight
    imported 16-bit queries, in that order. -/
theorem local_ranges {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    ∀ i : Fin 8, (w ([28, 29, 37, 38, 39, 40, 14, 15].get i)).val < limbBase :=
  Proofs.local_ranges h

/-- Four real low-byte queries: the divisor and selected quotient limbs.
    The latter are resolved through checked scratch aliases during import. -/
theorem byte_values {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    ∀ i : Fin 4, let pair := [(24, 33), (25, 34), (49, 60), (50, 61)].get i
      (w pair.1).val < limbBase ∧ w pair.2 = (((w pair.1).val % 256 : Nat) : ZMod p) :=
  Proofs.byte_values hp h

theorem carry_bounds {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    ∀ i : Fin 3, (w (41 + i.val)).val < 8192 :=
  Proofs.carry_bounds h

/-- The zero flag is derived from fixed-table membership, not an interface. -/
theorem divisor_zero_iff {p : Nat} [Fact p.Prime] (hp : 131072 ≤ p) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    w 32 = 1 ↔ (⟨(w 24).val, (w 25).val⟩ : Word).value = 0 :=
  Proofs.divisor_zero_iff hp h

/-- Imported exceptional-case equations force DIVU=max and REMU=dividend.
    The architectural soundness claim below reuses this local result. -/
theorem division_by_zero {p : Nat} [Fact p.Prime] (hp : 131072 ≤ p)
    {w : Nat → ZMod p} (remainder : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 12 = (if remainder then 0 else 1) ∧ w 13 = (if remainder then 1 else 0))
    (other : w 10 = 0 ∧ w 11 = 0) (zero : w 24 = 0 ∧ w 25 = 0) :
    (⟨(w 28).val, (w 29).val⟩ : Word).toBitVec =
      (if remainder then (⟨(w 20).val, (w 21).val⟩ : Word).toBitVec else 0xffffffff) :=
  Proofs.division_by_zero hp remainder h selected other zero

/-- The same serialized carry inverse and shared word-increment proof as ADD/SUB.
    This local PC update excludes 32-bit overflow. -/
theorem pc_successor {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    (inverse : (-30720 : ZMod p) * 65536 = 1)
    {w : Nat → ZMod p} {initial final : Word}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (mapping : w 0 = (initial.lo : ZMod p) ∧ w 1 = (initial.hi : ZMod p) ∧
      final.lo = (w 14).val ∧ final.hi = (w 15).val)
    (initialBound : initial.Bounded) :
    final.value = initial.value + 4 ∧ initial.value + 4 < wordModulus ∧
      final.toBitVec = initial.toBitVec + 4 :=
  Proofs.pc_successor hp inverse h mapping initialBound

/-- Full integer product from the four imported byte columns. Selector order:
    MUL, MULHU, DIVU, REMU. Register bounds and decoder selection are interfaces;
    quotient, remainder, extra-word and carry bounds come from lookups. -/
theorem product_with_remainder {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p)
    (inverse : (-30720 : ZMod p) * 65536 = 1) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (operation : Fin 4)
    (selected : ∀ i : Fin 4, w (10 + i.val) = if i = operation then 1 else 0)
    (leftBound : (w 20).val < limbBase ∧ (w 21).val < limbBase) :
    (⟨(w 49).val, (w 50).val⟩ : Word).value *
        (⟨(w 24).val, (w 25).val⟩ : Word).value +
      (⟨(w 51).val, (w 52).val⟩ : Word).value =
      (⟨(w 45).val, (w 46).val⟩ : Word).value + wordModulus *
        (⟨(w 47).val, (w 48).val⟩ : Word).value :=
  Proofs.product_with_remainder hp inverse h operation selected leftBound

/-- DIVU/REMU, including zero divisor, proved against original Sail execution plus
    native register/PC effects. Decoder/state interfaces remain explicit. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p)
    (inverse : (-30720 : ZMod p) * 65536 = 1) :
    circuitModel.SoundnessUnder (InterfaceAssumptions (p := p)) spec :=
  Proofs.division_soundness hp inverse

theorem babyBear_soundness :
    circuitModel.SoundnessUnder (InterfaceAssumptions (p := babyBearModulus)) spec :=
  soundness (by decide) (by decide)

end Airbender.MulDiv
