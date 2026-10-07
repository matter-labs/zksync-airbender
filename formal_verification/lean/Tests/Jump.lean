import Airbender.Review.JumpBranchSlt.Theorems

namespace Tests.Jump
open Airbender

private def initial (wrap : Bool) : Arithmetic.Word :=
  if wrap then ⟨65532, 65535⟩ else ⟨0, 0⟩

private def base (indirect wrap : Bool) : Arithmetic.Word :=
  if indirect then (if wrap then ⟨65535, 65535⟩ else ⟨5, 0⟩) else initial wrap

private def offset (indirect wrap : Bool) : Arithmetic.Word :=
  if wrap then ⟨if indirect then 6 else 8, 0⟩ else ⟨65532, 65535⟩

private def final (indirect wrap : Bool) : Arithmetic.Word :=
  if wrap then ⟨4, 0⟩ else if indirect then ⟨0, 0⟩ else ⟨65532, 65535⟩

private def row (indirect wrap zero : Bool) : Nat → ZMod babyBearModulus
  | 0 => (initial wrap).lo
  | 1 => (initial wrap).hi
  | 4 => 1
  | 5 => if indirect then 1 else 0
  | 7 => if zero then 0 else 1
  | 8 => (offset indirect wrap).lo
  | 9 => (offset indirect wrap).hi
  | 11 => if indirect then 0 else 1
  | 12 => if indirect then 1 else 0
  | 15 => if zero then 1 else 0
  | 16 => (final indirect wrap).lo
  | 17 => (final indirect wrap).hi
  | 18 => 4
  | 22 => if indirect then (base indirect wrap).lo else 0
  | 23 => if indirect then (base indirect wrap).hi else 0
  | 30 => if zero || wrap then 0 else 4
  | 34 | 47 => if wrap then 0 else 4
  | 36 => if wrap then (if indirect then 5 else 4) else (if indirect then 1 else 65532)
  | 37 | 38 | 41 | 44 => if wrap then 1 else 0
  | 39 | 40 => if indirect || wrap then 1 else 0
  | 42 => if indirect && wrap then 1 else 0
  | _ => 0

set_option maxHeartbeats 800000 in
private theorem satisfies (indirect wrap zero : Bool) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (row indirect wrap zero))
      JumpBranchSlt.importedConstraints := by
  cases indirect <;> cases wrap <;> cases zero <;>
    simp [JumpBranchSlt.importedConstraints, FlatOperation.ConstraintsHoldFlat,
      Expression.eval, Verification.environment, row, initial, offset, base, final]
  repeat' apply And.intro
  all_goals solve
    | (apply Verification.range16_contains; decide)
    | (with_unfolding_all change ∃ i : Fin 65536,
         ((0, 0) : fieldPair (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((i.val / 32768 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨0, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 65536,
         ((65535, 1) : fieldPair (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((i.val / 32768 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨65535, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 131072,
         ((0, 1) : fieldPair (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((if i.val = 0 then 1 else 0 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨0, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 131072,
         ((4, 0) : fieldPair (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((if i.val = 0 then 1 else 0 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨4, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 4194304,
         ((0, 0) : fieldPair (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), (Verification.conditionalValue i.val : ZMod babyBearModulus))
       exact ⟨⟨0, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 4194304,
         ((393216, 1) : fieldPair (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), (Verification.conditionalValue i.val : ZMod babyBearModulus))
       exact ⟨⟨393216, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 4194304,
         ((458752, 1) : fieldPair (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), (Verification.conditionalValue i.val : ZMod babyBearModulus))
       exact ⟨⟨458752, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 65536,
         ((65532, 0, 65532) : fieldTriple (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((i.val / 2 % 2 : Nat) : ZMod babyBearModulus), ((i.val - i.val % 4 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨65532, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 65536,
         ((4, 0, 4) : fieldTriple (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((i.val / 2 % 2 : Nat) : ZMod babyBearModulus), ((i.val - i.val % 4 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨4, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 65536,
         ((1, 0, 0) : fieldTriple (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((i.val / 2 % 2 : Nat) : ZMod babyBearModulus), ((i.val - i.val % 4 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨1, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 65536,
         ((5, 0, 4) : fieldTriple (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((i.val / 2 % 2 : Nat) : ZMod babyBearModulus), ((i.val - i.val % 4 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨5, by decide⟩, rfl⟩)
    | decide

/-- Eight imported rows: JAL/JALR, PC+4 and target wrapping, x0/nonzero rd.
    JALR's sums are odd; their bit-0 cleanup is exercised explicitly. -/
example (indirect wrap zero : Bool) :
    (⟨(row indirect wrap zero 30).val, (row indirect wrap zero 31).val⟩ : Arithmetic.Word).toBitVec =
      (if row indirect wrap zero 15 = 1 then 0 else (initial wrap).toBitVec + 4) ∧
    (⟨(row indirect wrap zero 30).val, (row indirect wrap zero 31).val⟩ : Arithmetic.Word).Bounded := by
  apply JumpBranchSlt.jump_link (by decide) (satisfies indirect wrap zero)
  · cases indirect <;> simp [row]
  · exact ⟨rfl, rfl⟩
  · constructor <;> cases wrap <;> simp [row, initial] <;> decide
  · cases wrap <;> decide

example (indirect wrap zero : Bool) :
    (final indirect wrap).toBitVec =
      (if indirect then ((base indirect wrap).toBitVec + (offset indirect wrap).toBitVec) &&& 0xfffffffe
        else (base indirect wrap).toBitVec + (offset indirect wrap).toBitVec) ∧
      (final indirect wrap).toBitVec.toNat % 4 = 0 := by
  apply JumpBranchSlt.jump_pc (w := row indirect wrap zero) (by decide) indirect
    (satisfies indirect wrap zero) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
  · constructor <;> cases indirect <;> cases wrap <;>
      simp [row, initial, base, offset, final] <;> decide
  · cases indirect <;> cases wrap <;> decide
  · cases indirect <;> cases wrap <;> decide
  · cases indirect <;> cases wrap <;> exact ⟨by decide, by decide⟩
  · cases indirect <;> cases wrap <;> decide
  · cases indirect <;> cases wrap <;> decide

private def misalignedRow (i : Nat) : ZMod babyBearModulus :=
  if i = 22 then 7 else if i = 36 then 3 else if i = 46 then 1 else row true false false i

/-- Clearing bit 0 of 7+(-4) gives PC 2, rejected by the imported bit-1 check. -/
example : ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment misalignedRow)
    JumpBranchSlt.importedConstraints := by
  intro h
  have target := JumpBranchSlt.jump_pc (base := ⟨7, 0⟩) (offset := ⟨65532, 65535⟩)
    (final := ⟨0, 0⟩) (by decide) true h ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
    (by constructor <;> decide) (by decide) (by decide)
    ⟨by decide, by decide⟩ (by decide) (by decide)
  exact (by decide : ¬ ((⟨0, 0⟩ : Arithmetic.Word).toBitVec =
    ((⟨7, 0⟩ : Arithmetic.Word).toBitVec + (⟨65532, 65535⟩ : Arithmetic.Word).toBitVec) &&& 0xfffffffe)) target.1

end Tests.Jump
