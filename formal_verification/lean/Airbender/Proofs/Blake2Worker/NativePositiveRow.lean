import Airbender.Review.Circuits.Blake2Worker.PositiveRow
import Airbender.Proofs.Blake2Worker.NativeFixedResults
import Airbender.Proofs.Blake2Worker.NativeProcessing
import Airbender.Proofs.Constraints

namespace Airbender.Blake2Worker.PositiveRowProofs
open Verification Airbender.Blake2Worker PositiveRow
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

-- Coordinate and XOR calculations stay abstract before actual literal-table
-- instantiation. Directly evaluating a complete imported row is unnecessary.
private theorem value_zero (a : F) (h : a.val = 0) : a = 0 := by
  apply ZMod.val_injective
  simpa using h
private theorem value_four (a : F) (h : a.val = 4) : a = 4 := by
  apply ZMod.val_injective
  have four : (4 : F).val = 4 := by decide +kernel
  simpa only [four] using h
private theorem zero_vector (q : Vector F 4) (tag : F)
    (a : q[0] = 0) (b : q[1] = 0) (c : q[2] = 0) (d : q[3] = tag) : q = #v[0,0,0,tag] := by
  ext lane bound
  interval_cases lane <;> simp_all
private theorem zero_byte_output (q : Vector F 4) (member : (Fixed.table (p := mersenne31Modulus)).Contains #[] q)
    (a : q[0] = 0) (b : q[1] = 0) (tag : q[3] = 4) : q[2] = 0 := by
  obtain ⟨_,_,bound,result⟩ := FixedProofs.byte_result q member tag
  rw [a,b] at result
  have small : BitVec.ofNat 8 q[2].val = 0 := by simpa [byteOperation] using result
  have congruent : q[2].val % 256 = 0 := congrArg BitVec.toNat small
  apply value_zero
  simpa [Nat.mod_eq_of_lt bound] using congruent
private theorem value_nat (a : F) (n : Nat) (bound : n < mersenne31Modulus) (h : a.val = n) : a = n := by
  apply ZMod.val_injective
  simpa only [ZMod.val_natCast_of_lt bound] using h
private theorem xor_zero (q : Vector F 4) (a : q[0] = 0) (b : q[1] = 0)
    (result : q[2].val = q[0].val ^^^ q[1].val) : q[2] = 0 := by
  apply value_zero
  simpa only [a,b,ZMod.val_zero,Nat.xor_self] using result
private theorem transport (q : Vector F 4) (tag : F) (member : (Fixed.table (p := mersenne31Modulus)).Contains #[] q)
    (same : q = #v[0,0,0,tag]) : (Fixed.table (p := mersenne31Modulus)).Contains #[] (#v[0,0,0,tag] : Vector F 4) := same ▸ member

theorem zero_member (kind : Fixed.Kind) :
    (Fixed.table (p := mersenne31Modulus)).Contains #[] (#v[0,0,0,(kind.tag : F)] : Vector F 4) := by
  let i : Fin (Fixed.data kind).length := ⟨0,by rw [FixedProofs.length_eq]; cases kind <;> decide⟩
  let q : Vector F 4 := (Fixed.data kind).row i
  have member := FixedProofs.every_row kind i
  obtain ⟨first,second,tag⟩ := FixedProofs.fields kind i
  have a : q[0] = 0 := value_zero _ (by simpa only [show i.val = 0 from rfl,Nat.zero_div] using first)
  have b : q[1] = 0 := value_zero _ (by simpa only [show i.val = 0 from rfl,Nat.zero_mod] using second)
  have d : q[3] = (kind.tag : F) := value_nat _ kind.tag (by cases kind <;> decide) tag
  have c : q[2] = 0 := by
    cases kind with
    | byte => exact zero_byte_output q member a b d
    | three => exact xor_zero q a b (FixedProofs.three_result q member d)
    | four => exact xor_zero q a b (FixedProofs.four_result q member d)
    | seven => exact xor_zero q a b (FixedProofs.seven_result q member d)
    | nine => exact xor_zero q a b (FixedProofs.nine_result q member d)
  exact transport q kind.tag member (zero_vector q kind.tag a b c d)
open Airbender.Blake2Worker.Native
private theorem table_lookup (setup : Table F (fields 4)) (entries : Vector (Expression F) 4) (w : Nat → F) :
    (Lookup.mk setup.toRaw entries).Contains (environment w) ↔ setup.Contains #[] (entries.map (Expression.eval (environment w))) := by
  simp [Lookup.Contains,Table.toRaw,environment,ProvableType.fromElements]
private theorem fixed_lookup (kind : Fixed.Kind) (entries : Vector (Expression F) 4) (w : Nat → F)
    (computed : entries.map (Expression.eval (environment w)) = #v[0,0,0,(kind.tag : F)]) :
    (Lookup.mk Fixed.table.toRaw entries).Contains (environment w) := by
  apply (table_lookup Fixed.table entries w).mpr
  rw [computed]
  exact zero_member kind

private theorem assertions0 : FlatOperation.ConstraintsHoldFlat (environment assignment)
    (constraintsBlock0 Fixed.table) := by
  simp only [constraintsBlock0,FlatOperation.ConstraintsHoldFlat]
  repeat' apply And.intro
  all_goals decide +kernel

private theorem assertions1 : FlatOperation.ConstraintsHoldFlat (environment assignment)
    (constraintsBlock1 Fixed.table) := by
  simp only [constraintsBlock1,FlatOperation.ConstraintsHoldFlat]
  repeat' apply And.intro
  all_goals decide +kernel

private theorem assertions2 : FlatOperation.ConstraintsHoldFlat (environment assignment)
    (constraintsBlock2 Fixed.table) := by
  simp only [constraintsBlock2,FlatOperation.ConstraintsHoldFlat]
  repeat' apply And.intro
  all_goals decide +kernel

private theorem assertions3 : FlatOperation.ConstraintsHoldFlat (environment assignment)
    (constraintsBlock3 Fixed.table) := by
  simp only [constraintsBlock3,FlatOperation.ConstraintsHoldFlat]
  repeat' apply And.intro
  all_goals decide +kernel

private theorem assertions4 : FlatOperation.ConstraintsHoldFlat (environment assignment)
    (constraintsBlock4 Fixed.table) := by
  simp only [constraintsBlock4,FlatOperation.ConstraintsHoldFlat]
  repeat' apply And.intro
  all_goals decide +kernel

private theorem assertions5 : FlatOperation.ConstraintsHoldFlat (environment assignment)
    ((constraintsBlock5 Fixed.table).take 32) := by
  simp only [constraintsBlock5,List.take,FlatOperation.ConstraintsHoldFlat]
  repeat' apply And.intro
  all_goals decide +kernel
private theorem lookups5 : FlatOperation.ConstraintsHoldFlat (environment assignment)
    ((constraintsBlock5 Fixed.table).drop 32) := by
  simp only [constraintsBlock5,List.drop,FlatOperation.ConstraintsHoldFlat]
  repeat' apply And.intro
  all_goals first
    | (apply range16_contains; decide +kernel)
    | (apply timestamp19_contains; decide +kernel)
    | trivial

private theorem lookups6 : FlatOperation.ConstraintsHoldFlat (environment assignment)
    (constraintsBlock6 Fixed.table) := by
  simp only [constraintsBlock6,FlatOperation.ConstraintsHoldFlat]
  repeat' apply And.intro
  all_goals first
    | (apply timestamp19_contains; decide +kernel)
    | trivial
    | (apply fixed_lookup .byte; decide +kernel)
    | (apply fixed_lookup .three; decide +kernel)
    | (apply fixed_lookup .four; decide +kernel)
    | (apply fixed_lookup .nine; decide +kernel)

private theorem lookups7 : FlatOperation.ConstraintsHoldFlat (environment assignment)
    (constraintsBlock7 Fixed.table) := by
  simp only [constraintsBlock7,FlatOperation.ConstraintsHoldFlat]
  repeat' apply And.intro
  all_goals first
    | trivial
    | (apply fixed_lookup .byte; decide +kernel)
    | (apply fixed_lookup .three; decide +kernel)
    | (apply fixed_lookup .four; decide +kernel)
    | (apply fixed_lookup .seven; decide +kernel)
    | (apply fixed_lookup .nine; decide +kernel)

private theorem lookups8 : FlatOperation.ConstraintsHoldFlat (environment assignment)
    (constraintsBlock8 Fixed.table) := by
  simp only [constraintsBlock8,FlatOperation.ConstraintsHoldFlat]
  repeat' apply And.intro
  all_goals first
    | trivial
    | (apply fixed_lookup .byte; decide +kernel)
    | (apply fixed_lookup .three; decide +kernel)
    | (apply fixed_lookup .four; decide +kernel)
    | (apply fixed_lookup .seven; decide +kernel)
    | (apply fixed_lookup .nine; decide +kernel)

private theorem lookups9 : FlatOperation.ConstraintsHoldFlat (environment assignment)
    (constraintsBlock9 Fixed.table) := by
  simp only [constraintsBlock9,FlatOperation.ConstraintsHoldFlat]
  repeat' apply And.intro
  all_goals first
    | trivial
    | (apply fixed_lookup .byte; decide +kernel)
    | (apply fixed_lookup .seven; decide +kernel)
    | (apply fixed_lookup .nine; decide +kernel)

private theorem lookups10 : FlatOperation.ConstraintsHoldFlat (environment assignment)
    (constraintsBlock10 Fixed.table) := by
  simp only [constraintsBlock10,FlatOperation.ConstraintsHoldFlat]
  repeat' apply And.intro
  all_goals first
    | trivial
    | (apply fixed_lookup .byte; decide +kernel)
    | (apply fixed_lookup .seven; decide +kernel)
    | (apply fixed_lookup .nine; decide +kernel)

private theorem block5 : FlatOperation.ConstraintsHoldFlat (environment assignment) (constraintsBlock5 Fixed.table) := by
  have combined := holds_append assertions5 lookups5
  rw [List.take_append_drop] at combined
  exact combined

theorem body : FlatOperation.ConstraintsHoldFlat (environment assignment) (constraints Fixed.table) := by
  unfold constraints
  exact (holds_append (holds_append (holds_append (holds_append (holds_append (holds_append (holds_append (holds_append (holds_append (holds_append (holds_append (by trivial) assertions0) assertions1) assertions2) assertions3) assertions4) block5) lookups6) lookups7) lookups8) lookups9) lookups10)

theorem local_processing : LocalProcessingAccepted assignment := by
  refine ⟨body,?_⟩
  rw [ProcessingProofs.conventions_iff]
  change processingBitTerm 1 (assignment 0) = 0 ∧ ∀ column ∈ ProcessingArtifact.processingMaskedColumns.toList,
    processingMaskTerm 1 (assignment 0) (assignment column) = 0
  have active : assignment 0 = 1 := rfl
  simp [active,processingBitTerm,processingMaskTerm]

end Airbender.Blake2Worker.PositiveRowProofs
