import Airbender.Proofs.SubwordMemory.Controls
import Mathlib.Tactic.IntervalCases
import Airbender.Review.Circuits.SubwordMemory.ValuesModel
import Airbender.Review.Helpers.Tables.SubwordOffsetTheorems

namespace Airbender.SubwordMemory.Proofs
open Arithmetic Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- The native mask retains all three bits, including the possible trap bit. -/
theorem offset_mask_bound (key : Nat) : SubwordOffset.mask key ≤ 7 := by
  simp only [SubwordOffset.mask]
  split_ifs <;> omega

/-- The mask's middle bit is exactly the selected 16-bit half of the word. -/
theorem offset_mask_upper (key : Nat) :
    SubwordOffset.mask key / 2 % 2 = key % 4 / 2 := by
  have bound : key % 4 < 4 := Nat.mod_lt _ (by decide)
  simp only [SubwordOffset.mask]
  split_ifs <;> omega

variable {rom : WordROM} {w : Nat → ZMod mersenne31Modulus}

private theorem fixed_values (table : Table (ZMod mersenne31Modulus) (fields 3))
    (entry : Vector (Expression (ZMod mersenne31Modulus)) 3)
    (w : Nat → ZMod mersenne31Modulus) :
    (fixed3 table entry).Contains (environment w) ↔
      table.Contains #[] (entry.map (Expression.eval (environment w))) := by
  simp [Lookup.Contains,fixed3,Table.toRaw,environment,ProvableType.fromElements]

/-- Reduce the native lookup before evaluating its three fields, so no large
    combined constraint/table expression enters the simplifier at once. -/
theorem offset_query
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom)) :
    SubwordOffset.table.Contains #[] #v[offsetKey w,w 22,w 23] := by
  let entry : Vector (Expression (ZMod mersenne31Modulus)) 3 :=
    ((FlatOperation.lookups (importedConstraints rom)).get ⟨10,by rw [lookup_count]; decide⟩).entry
  have query : (fixed3 SubwordOffset.table entry).Contains (environment w) :=
    lookup_of_holds holds ⟨10,by rw [lookup_count]; decide⟩
  have member := (fixed_values SubwordOffset.table entry w).mp query
  have evaluated : entry.map (Expression.eval (environment w)) = #v[offsetKey w,w 22,w 23] := by
    ext i
    interval_cases i
    · simp [entry,importedConstraints,FlatOperation.lookups,fixed3,Expression.eval,environment,offsetKey]
      ring
    · simp [entry,importedConstraints,FlatOperation.lookups,fixed3,Expression.eval,environment]
    · simp [entry,importedConstraints,FlatOperation.lookups,fixed3,Expression.eval,environment]
  rw [evaluated] at member
  exact member

/-- Native acceptance derives offset, mask, absence of a trap bit and exact
    selector meaning; none is assumed as a decoder or alignment premise. -/
theorem accepted_offset_values
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom)) :
    OffsetValues w := by
  obtain ⟨keyBound,offset,mask⟩ := SubwordOffset.native_values (offset_query holds)
  have maskBound := offset_mask_bound (offsetKey w).val
  have sizeBound := boolean_val (size_bit holds)
  have upperBound := boolean_val (upper_bit holds)
  have packed := assertion_of_holds holds ⟨47,by rw [constraint_count]; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at packed
  have field : (((w 24).val + 2 * (w 25).val : Nat) : ZMod mersenne31Modulus) =
      (SubwordOffset.mask (offsetKey w).val : Nat) := by
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,ZMod.natCast_zmod_val]
    linear_combination packed + mask
  have natural := congrArg ZMod.val field
  rw [ZMod.val_natCast_of_lt (by change _ < 2147483647; omega),
    ZMod.val_natCast_of_lt (by change _ < 2147483647; omega)] at natural
  have offsetNatural : (w 22).val = (offsetKey w).val % 4 := by
    rw [offset,ZMod.val_natCast_of_lt (by have := Nat.mod_lt (offsetKey w).val (by decide : 0 < 4); change _ < 2147483647; omega)]
  have upper := offset_mask_upper (offsetKey w).val
  refine ⟨keyBound,offsetNatural,?_,?_,?_,?_⟩
  · rw [mask,ZMod.val_natCast_of_lt (by change _ < 2147483647; omega)]
  · omega
  · omega
  · omega

end Airbender.SubwordMemory.Proofs
