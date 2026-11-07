import Airbender.Review.Circuits.Blake2Worker.Control
import Airbender.Proofs.Constraints
import Airbender.Proofs.Arithmetic.Lemmas
import Mathlib.Tactic.FinCases

namespace Airbender.Blake2Worker.NativeProofs
open Verification Native
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem equations {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 4)) :
    (FlatOperation.constraints (constraints setup)).length = 352 := by
  have c0 : (FlatOperation.constraints (constraintsBlock0 setup)).length = 64 := rfl
  have c1 : (FlatOperation.constraints (constraintsBlock1 setup)).length = 64 := rfl
  have c2 : (FlatOperation.constraints (constraintsBlock2 setup)).length = 64 := rfl
  have c3 : (FlatOperation.constraints (constraintsBlock3 setup)).length = 64 := rfl
  have c4 : (FlatOperation.constraints (constraintsBlock4 setup)).length = 64 := rfl
  have c5 : (FlatOperation.constraints (constraintsBlock5 setup)).length = 32 := rfl
  have c6 : (FlatOperation.constraints (constraintsBlock6 setup)).length = 0 := rfl
  have c7 : (FlatOperation.constraints (constraintsBlock7 setup)).length = 0 := rfl
  have c8 : (FlatOperation.constraints (constraintsBlock8 setup)).length = 0 := rfl
  have c9 : (FlatOperation.constraints (constraintsBlock9 setup)).length = 0 := rfl
  have c10 : (FlatOperation.constraints (constraintsBlock10 setup)).length = 0 := rfl
  simp only [constraints,FlatOperation.constraints_append,List.length_append,c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,
    show (FlatOperation.constraints ([] : List (FlatOperation (ZMod p)))).length = 0 by rfl]

theorem lookups {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 4)) :
    (FlatOperation.lookups (constraints setup)).length = 296 := by
  have c0 : (FlatOperation.lookups (constraintsBlock0 setup)).length = 0 := rfl
  have c1 : (FlatOperation.lookups (constraintsBlock1 setup)).length = 0 := rfl
  have c2 : (FlatOperation.lookups (constraintsBlock2 setup)).length = 0 := rfl
  have c3 : (FlatOperation.lookups (constraintsBlock3 setup)).length = 0 := rfl
  have c4 : (FlatOperation.lookups (constraintsBlock4 setup)).length = 0 := rfl
  have c5 : (FlatOperation.lookups (constraintsBlock5 setup)).length = 32 := rfl
  have c6 : (FlatOperation.lookups (constraintsBlock6 setup)).length = 64 := rfl
  have c7 : (FlatOperation.lookups (constraintsBlock7 setup)).length = 64 := rfl
  have c8 : (FlatOperation.lookups (constraintsBlock8 setup)).length = 64 := rfl
  have c9 : (FlatOperation.lookups (constraintsBlock9 setup)).length = 64 := rfl
  have c10 : (FlatOperation.lookups (constraintsBlock10 setup)).length = 8 := rfl
  simp only [constraints,FlatOperation.lookups_append,List.length_append,c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,
    show (FlatOperation.lookups ([] : List (FlatOperation (ZMod p)))).length = 0 by rfl]

theorem geometry : constraintsABI.traceLength = 1048576 ∧
    constraintsABI.witnessWidth = 648 ∧ constraintsABI.memoryWidth = 226 ∧
    constraintsABI.setupWidth = 6 ∧ constraintsABI.genericRows = 344384 ∧
    constraintsABI.processingAux = 1064 ∧ constraintsABI.registers.size = 3 := by decide

theorem processor_columns : constraintsABI.multiplicity = 0 ∧
    constraintsABI.offsetHigh = 1 ∧ constraintsABI.writeTime = #v[740,741] := by decide

theorem register_columns :
    (constraintsABI.registers[0]!).register = 10 ∧
    (constraintsABI.registers[1]!).register = 11 ∧ (constraintsABI.registers[2]!).register = 12 ∧
    (constraintsABI.registers[0]!).access.readValue = #v[2,3] ∧
    (constraintsABI.registers[1]!).access.readValue = #v[100,101] ∧
    (constraintsABI.registers[2]!).access.readValue = #v[134,135] ∧
    (constraintsABI.registers[2]!).access.writeValue = some #v[136,137] ∧
    (constraintsABI.registers[0]!).indirects.size = 24 ∧
    (constraintsABI.registers[1]!).indirects.size = 16 ∧ (constraintsABI.registers[2]!).indirects.size = 0 := by decide

private theorem block0 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) :
    FlatOperation.ConstraintsHoldFlat (environment w) (constraintsBlock0 setup) := by
  apply holds_of_sublist holds
  have base : (constraintsBlock0 setup).Sublist ([] ++ constraintsBlock0 setup) := by
    simp
  exact ((((((((((base.trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _))

private theorem block4 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) :
    FlatOperation.ConstraintsHoldFlat (environment w) (constraintsBlock4 setup) := by
  apply holds_of_sublist holds
  have base : (constraintsBlock4 setup).Sublist ([] ++ constraintsBlock0 setup ++ constraintsBlock1 setup ++ constraintsBlock2 setup ++ constraintsBlock3 setup ++ constraintsBlock4 setup) := by
    exact List.sublist_append_right _ _
  exact ((((((base.trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _))

theorem bit_bounds {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup))
    (slot : Fin 13) : (w (138+slot.val)).val ≤ 1 := by
  have bit := assertion_of_holds (block0 (setup := setup) (w := w) holds) ⟨slot.val,by change slot.val < 64; omega⟩
  fin_cases slot
  all_goals
    simp [constraintsBlock0,FlatOperation.constraints,Expression.eval,environment] at bit ⊢
    obtain ⟨n,bound,same⟩ := Arithmetic.boolean_nat (by linear_combination bit)
    rw [same]
    simpa only [ZMod.val_natCast] using le_trans (Nat.mod_le n mersenne31Modulus) bound

theorem input_packed {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) :
    (w 138).val + 2 * (w 139).val + 4 * (w 140).val + 8 * (w 141).val + 16 * (w 142).val + 32 * (w 143).val + 64 * (w 144).val + 128 * (w 145).val + 256 * (w 146).val + 512 * (w 147).val + 1024 * (w 148).val + 2048 * (w 149).val + 4096 * (w 150).val = (w 135).val := by
  have b0 : (w 138).val ≤ 1 := bit_bounds (setup := setup) (w := w) holds ⟨0,by decide⟩
  have b1 : (w 139).val ≤ 1 := bit_bounds (setup := setup) (w := w) holds ⟨1,by decide⟩
  have b2 : (w 140).val ≤ 1 := bit_bounds (setup := setup) (w := w) holds ⟨2,by decide⟩
  have b3 : (w 141).val ≤ 1 := bit_bounds (setup := setup) (w := w) holds ⟨3,by decide⟩
  have b4 : (w 142).val ≤ 1 := bit_bounds (setup := setup) (w := w) holds ⟨4,by decide⟩
  have b5 : (w 143).val ≤ 1 := bit_bounds (setup := setup) (w := w) holds ⟨5,by decide⟩
  have b6 : (w 144).val ≤ 1 := bit_bounds (setup := setup) (w := w) holds ⟨6,by decide⟩
  have b7 : (w 145).val ≤ 1 := bit_bounds (setup := setup) (w := w) holds ⟨7,by decide⟩
  have b8 : (w 146).val ≤ 1 := bit_bounds (setup := setup) (w := w) holds ⟨8,by decide⟩
  have b9 : (w 147).val ≤ 1 := bit_bounds (setup := setup) (w := w) holds ⟨9,by decide⟩
  have b10 : (w 148).val ≤ 1 := bit_bounds (setup := setup) (w := w) holds ⟨10,by decide⟩
  have b11 : (w 149).val ≤ 1 := bit_bounds (setup := setup) (w := w) holds ⟨11,by decide⟩
  have b12 : (w 150).val ≤ 1 := bit_bounds (setup := setup) (w := w) holds ⟨12,by decide⟩
  have equation := assertion_of_holds (block4 (setup := setup) (w := w) holds) ⟨45,by change 45 < 64; decide⟩
  simp [constraintsBlock4,FlatOperation.constraints,Expression.eval,environment] at equation
  apply Arithmetic.bounded_nat_eq (F := ZMod mersenne31Modulus) (p := mersenne31Modulus)
    (by change _ < 2147483647; omega) (ZMod.val_lt _)
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,ZMod.natCast_zmod_val]
  linear_combination equation

theorem output_packed {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) :
    (w 138).val + 2 * (w 139).val + 4 * (w 140).val + 16 * (w 141).val + 32 * (w 142).val + 64 * (w 143).val + 128 * (w 144).val + 256 * (w 145).val + 512 * (w 146).val + 1024 * (w 147).val + 2048 * (w 148).val + 4096 * (w 149).val = (w 137).val := by
  have b0 : (w 138).val ≤ 1 := bit_bounds (setup := setup) (w := w) holds ⟨0,by decide⟩
  have b1 : (w 139).val ≤ 1 := bit_bounds (setup := setup) (w := w) holds ⟨1,by decide⟩
  have b2 : (w 140).val ≤ 1 := bit_bounds (setup := setup) (w := w) holds ⟨2,by decide⟩
  have b3 : (w 141).val ≤ 1 := bit_bounds (setup := setup) (w := w) holds ⟨3,by decide⟩
  have b4 : (w 142).val ≤ 1 := bit_bounds (setup := setup) (w := w) holds ⟨4,by decide⟩
  have b5 : (w 143).val ≤ 1 := bit_bounds (setup := setup) (w := w) holds ⟨5,by decide⟩
  have b6 : (w 144).val ≤ 1 := bit_bounds (setup := setup) (w := w) holds ⟨6,by decide⟩
  have b7 : (w 145).val ≤ 1 := bit_bounds (setup := setup) (w := w) holds ⟨7,by decide⟩
  have b8 : (w 146).val ≤ 1 := bit_bounds (setup := setup) (w := w) holds ⟨8,by decide⟩
  have b9 : (w 147).val ≤ 1 := bit_bounds (setup := setup) (w := w) holds ⟨9,by decide⟩
  have b10 : (w 148).val ≤ 1 := bit_bounds (setup := setup) (w := w) holds ⟨10,by decide⟩
  have b11 : (w 149).val ≤ 1 := bit_bounds (setup := setup) (w := w) holds ⟨11,by decide⟩
  have b12 : (w 150).val ≤ 1 := bit_bounds (setup := setup) (w := w) holds ⟨12,by decide⟩
  have equation := assertion_of_holds (block4 (setup := setup) (w := w) holds) ⟨47,by change 47 < 64; decide⟩
  simp [constraintsBlock4,FlatOperation.constraints,Expression.eval,environment] at equation
  apply Arithmetic.bounded_nat_eq (F := ZMod mersenne31Modulus) (p := mersenne31Modulus)
    (by change _ < 2147483647; omega) (ZMod.val_lt _)
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,ZMod.natCast_zmod_val]
  linear_combination equation

theorem low_cleared {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) : w 136 = 0 := by
  have equation := assertion_of_holds (block4 (setup := setup) (w := w) holds) ⟨46,by change 46 < 64; decide⟩
  simpa [constraintsBlock4,FlatOperation.constraints,Expression.eval,environment] using equation

private theorem bounds_of_flags (w : Nat → Nat)
    (bits : ∀ slot : Fin 13, w (138+slot.val) ≤ 1)
    (input : w 138 + 2 * w 139 + 4 * w 140 + 8 * w 141 + 16 * w 142 + 32 * w 143 + 64 * w 144 + 128 * w 145 + 256 * w 146 + 512 * w 147 + 1024 * w 148 + 2048 * w 149 + 4096 * w 150 = w 135)
    (output : w 138 + 2 * w 139 + 4 * w 140 + 16 * w 141 + 32 * w 142 + 64 * w 143 + 128 * w 144 + 256 * w 145 + 512 * w 146 + 1024 * w 147 + 2048 * w 148 + 4096 * w 149 = w 137) : w 135 < 8192 ∧ w 137 < 8192 := by
  have b0 : w 138 ≤ 1 := bits ⟨0,by decide⟩
  have b1 : w 139 ≤ 1 := bits ⟨1,by decide⟩
  have b2 : w 140 ≤ 1 := bits ⟨2,by decide⟩
  have b3 : w 141 ≤ 1 := bits ⟨3,by decide⟩
  have b4 : w 142 ≤ 1 := bits ⟨4,by decide⟩
  have b5 : w 143 ≤ 1 := bits ⟨5,by decide⟩
  have b6 : w 144 ≤ 1 := bits ⟨6,by decide⟩
  have b7 : w 145 ≤ 1 := bits ⟨7,by decide⟩
  have b8 : w 146 ≤ 1 := bits ⟨8,by decide⟩
  have b9 : w 147 ≤ 1 := bits ⟨9,by decide⟩
  have b10 : w 148 ≤ 1 := bits ⟨10,by decide⟩
  have b11 : w 149 ≤ 1 := bits ⟨11,by decide⟩
  have b12 : w 150 ≤ 1 := bits ⟨12,by decide⟩
  constructor <;> omega

theorem effects {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) : ControlEffects w := by
  have bits := bit_bounds (setup := setup) (w := w) holds
  have bounded := bounds_of_flags (fun i => (w i).val) bits
    (input_packed (setup := setup) (w := w) holds) (output_packed (setup := setup) (w := w) holds)
  exact ⟨bits,bounded.1,bounded.2,low_cleared (setup := setup) (w := w) holds⟩

end Airbender.Blake2Worker.NativeProofs
