import Airbender.Proofs.ReducedMachine.NativeBranchCondition
import Airbender.Proofs.ReducedMachine.NativeBranchCleanup
import Airbender.Proofs.ReducedMachine.NativePC

namespace Airbender.ReducedMachine.NativeBranchPCProofs
open Native Arithmetic Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Both actual branch-target limbs are checked by native scalar lookups2/3. -/
theorem target_bounds {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup)) :
    (branchTargetWord w).Bounded := by
  have lo := range16_bound (lookup_of_holds holds ⟨2,by change 2 < 22; decide⟩)
  have hi := range16_bound (lookup_of_holds holds ⟨3,by change 3 < 22; decide⟩)
  simpa [Expression.eval,environment,limbBase,branchTargetWord,Word.Bounded] using And.intro lo hi

/-- Target carry and high wrap are actual native Boolean columns. -/
theorem carries {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup)) :
    (w 96).val ≤ 1 ∧ (w 71).val ≤ 1 := by
  have lo := assertion_of_holds holds ⟨24,by change 24 < 117; decide⟩
  have hi := assertion_of_holds holds ⟨22,by change 22 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at lo hi
  obtain ⟨a,ab,ae⟩ := boolean_nat (by linear_combination lo)
  obtain ⟨b,bb,be⟩ := boolean_nat (by linear_combination hi)
  constructor
  · rw [ae]; simpa only [ZMod.val_natCast] using le_trans (Nat.mod_le a mersenne31Modulus) ab
  · rw [be]; simpa only [ZMod.val_natCast] using le_trans (Nat.mod_le b mersenne31Modulus) bb

/-- Exact native PC+offset equations; no expected target or carry is supplied. -/
theorem target_equations {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mask : w 12 = (branchMask : ZMod mersenne31Modulus)) :
    w 0+w 9 = w 69+65536*w 96 ∧ w 96+w 1+w 10 = w 70+65536*w 71 := by
  have lo := assertion_of_holds holds ⟨76,by change 76 < 117; decide⟩
  have hi := assertion_of_holds holds ⟨77,by change 77 < 117; decide⟩
  have active : w 23 = 1 := by simpa [NativeBranchSelectorProofs.bit] using
    NativeBranchSelectorProofs.flags holds mask ⟨6,by decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment,active] at lo hi
  exact ⟨by linear_combination lo,by linear_combination hi⟩

/-- Internal canonical inputs give full RV32 target arithmetic including rollover.
    Original public decoding must discharge both input bounds. -/
theorem target_result {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mask : w 12 = (branchMask : ZMod mersenne31Modulus))
    (pc : (initialPCWord w).Bounded) (offset : (branchOffsetWord w).Bounded) :
    (branchTargetWord w).toBitVec = (initialPCWord w).toBitVec + (branchOffsetWord w).toBitVec := by
  have equations := target_equations holds mask
  have carry := carries holds
  have sum := Word.add_of_limbs (p := mersenne31Modulus) (by decide)
    (left := initialPCWord w) (right := branchOffsetWord w) (immediate := ⟨0,0⟩)
    (output := branchTargetWord w) (carry := (w 96).val) (wrap := (w 71).val)
    pc offset (by constructor <;> decide) (target_bounds holds)
    (le_trans carry.1 (by decide)) (le_trans carry.2 (by decide))
    (by simpa [initialPCWord,branchOffsetWord,branchTargetWord,ZMod.natCast_zmod_val] using equations.1)
    (by simpa [initialPCWord,branchOffsetWord,branchTargetWord,ZMod.natCast_zmod_val] using equations.2)
  simpa [Word.toBitVec,Word.value] using sum

/-- Recover actual cleanup17 membership and numerical bit1/cleared values. -/
theorem cleanup {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (mask : w 12 = (branchMask : ZMod mersenne31Modulus)) :
    (w 69).val < 65536 ∧ w 64 = ((w 69).val / 2 % 2 : Nat) ∧
      w 65 = (4*((w 69).val / 4) : Nat) := by
  have member := NativeQueryProofs.dynamic_queries holds 0
  change (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[w 100,w 101,w 102,w 103] at member
  rw [(NativeBranchFieldProofs.query_fields holds mask).1] at member
  exact NativeBranchCleanupProofs.values member

/-- Generic equation extraction avoids elaborating the foreign fixed pool. -/
theorem taken_product {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mask : w 12 = (branchMask : ZMod mersenne31Modulus)) : w 64*w 66 = 0 := by
  have e40 := assertion_of_holds holds ⟨40,by change 40 < 117; decide⟩
  have e41 := assertion_of_holds holds ⟨41,by change 41 < 117; decide⟩
  have active : w 23 = 1 := by simpa [NativeBranchSelectorProofs.bit] using
    NativeBranchSelectorProofs.flags holds mask ⟨6,by decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment,active] at e40 e41
  linear_combination e40+e41

/-- Actual constraints reject a taken target with bit1 set. No alignment or
    chosen-condition answer is supplied to derive this native exclusion. -/
theorem taken_bit {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (mask : w 12 = (branchMask : ZMod mersenne31Modulus)) :
    w 66 = 1 → (w 69).val / 2 % 2 = 0 := by
  intro taken
  have product := taken_product holds mask
  have zero : w 64 = 0 := by simpa only [taken,mul_one] using product
  have cast : (((w 69).val / 2 % 2 : Nat) : ZMod mersenne31Modulus) = 0 := (cleanup holds mask).2.1 ▸ zero
  have val := congrArg ZMod.val cast
  rw [ZMod.val_natCast_of_lt (by have := Nat.mod_lt ((w 69).val / 2) (by decide : 0 < 2); change _ < 2147483647; omega)] at val
  simpa using val

/-- Internal numerical branch PC effects. Original public decoding/history must
    discharge source/PC/offset bounds, incoming alignment and offset parity. The
    actual branch condition, output bounds, selected target and taken alignment
    are conclusions, with full RV32 rollover retained. -/
theorem effects {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (mask : w 12 = (branchMask : ZMod mersenne31Modulus))
    (tags : (w 11).val ∈ [0,1,4,5,6,7])
    (left : (sourceWord w).Bounded) (right : (operandWord w).Bounded)
    (pc : (initialPCWord w).Bounded) (offset : (branchOffsetWord w).Bounded)
    (aligned : (initialPCWord w).lo % 4 = 0)
    (even : (branchOffsetWord w).lo % 2 = 0) :
    (finalPCWord w).Bounded ∧
    (finalPCWord w).toBitVec =
      (if branchCondition (w 11).val (sourceWord w) (operandWord w) then
        (initialPCWord w).toBitVec + (branchOffsetWord w).toBitVec
       else (initialPCWord w).toBitVec + 4) ∧
    (finalPCWord w).toBitVec.toNat % 4 = 0 := by
  have resolved := (NativeBranchConditionProofs.resolution holds mask tags left right).2
  have selection := NativeBranchFieldProofs.pc_selection holds mask
  let fallback : Word := ⟨(w 49).val,(w 50).val⟩
  have increment := NativePCProofs.default_pc_successor (by decide : 196608 < mersenne31Modulus)
    (initial := initialPCWord w) (final := fallback) holds
    ⟨by simp [initialPCWord],by simp [initialPCWord],rfl,rfl⟩ pc aligned
  have target := target_result holds mask pc offset
  have targetBound := target_bounds holds
  cases condition : branchCondition (w 11).val (sourceWord w) (operandWord w)
  · simp only [condition,Bool.false_eq_true,if_false] at resolved ⊢
    rw [resolved] at selection
    have low : w 13 = w 49 := by simpa using selection.1
    have high : w 14 = w 50 := by simpa using selection.2
    have final : finalPCWord w = fallback := by simp [finalPCWord,fallback,low,high]
    rw [final]
    refine ⟨increment.1,increment.2,?_⟩
    rw [increment.2]
    simp only [BitVec.toNat_add,Word.toBitVec_toNat pc]
    change ((initialPCWord w).value+4)%4294967296%4 = 0
    unfold Word.value limbBase
    omega
  · simp only [condition,if_true] at resolved ⊢
    have bit1 := taken_bit holds mask resolved
    rw [resolved] at selection
    have low : w 13 = w 69 := by simpa using selection.1
    have high : w 14 = w 70 := by simpa using selection.2
    have final : finalPCWord w = branchTargetWord w := by
      simp [finalPCWord,branchTargetWord,low,high]
    rw [final]
    refine ⟨targetBound,target,?_⟩
    have equation := (target_equations holds mask).1
    have carry := (carries holds).1
    have lowNat : (initialPCWord w).lo+(branchOffsetWord w).lo =
        (branchTargetWord w).lo+65536*(w 96).val := by
      apply bounded_nat_eq (F := ZMod mersenne31Modulus) (p := mersenne31Modulus)
        (by have := pc.1; have := offset.1; unfold limbBase at *; change _ < 2147483647; omega)
        (by have := targetBound.1; unfold limbBase at *; change _ < 2147483647; omega)
      exact_mod_cast (by simpa [initialPCWord,branchOffsetWord,branchTargetWord,ZMod.natCast_zmod_val] using equation :
        (((initialPCWord w).lo+(branchOffsetWord w).lo : Nat) : ZMod mersenne31Modulus) =
          (((branchTargetWord w).lo+65536*(w 96).val : Nat) : ZMod mersenne31Modulus))
    have targetAligned : (branchTargetWord w).lo % 4 = 0 := by
      change (w 69).val / 2 % 2 = 0 at bit1
      change (w 69).val % 4 = 0
      change (initialPCWord w).lo+(branchOffsetWord w).lo = (w 69).val+65536*(w 96).val at lowNat
      omega
    rw [Word.toBitVec_toNat targetBound]
    unfold Word.value limbBase
    omega

end Airbender.ReducedMachine.NativeBranchPCProofs
