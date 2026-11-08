import Slop.JumpBranchSlt.Claims
import Slop.JumpBranchSlt.Completeness.Witness

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

def row (indirect wrap zero : Bool) : Nat → ZMod babyBearModulus
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

/-- The honest inputs `row` is built from: the operands, PC and offset; zero clocks. -/
private def witness (indirect wrap zero : Bool) : JumpBranchSlt.Completeness.Inputs where
  sel := if indirect then 1 else 0
  rdZero := zero
  funct3 := 0
  rs1 := if indirect then 1 else 0
  rs2 := 0
  rd := if zero then 0 else 1
  pcLo := (initial wrap).lo
  pcHi := (initial wrap).hi
  aLo := if indirect then (base indirect wrap).lo else 0
  aHi := if indirect then (base indirect wrap).hi else 0
  bLo := 0
  bHi := 0
  immLo := (offset indirect wrap).lo
  immHi := (offset indirect wrap).hi
  oldLo := 0
  oldHi := 0
  tsLo := 0
  tsHi := 0
  prev0Lo := 0
  prev0Hi := 0
  prev1Lo := 0
  prev1Hi := 0
  prev2Lo := 0
  prev2Hi := 0
  borrow0 := 0
  borrow1 := 0
  borrow2 := 0

private theorem valid (indirect wrap zero : Bool) : (witness indirect wrap zero).Valid := by
  cases indirect <;> cases wrap <;> cases zero <;> constructor <;> decide

private theorem agree (indirect wrap zero : Bool) : ∀ i ∈ JumpBranchSlt.Completeness.columns,
    row indirect wrap zero i = (witness indirect wrap zero).honest i := by
  cases indirect <;> cases wrap <;> cases zero <;> decide

theorem satisfies (indirect wrap zero : Bool) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (row indirect wrap zero))
      JumpBranchSlt.importedConstraints :=
  JumpBranchSlt.Completeness.complete_of_agree _ (valid indirect wrap zero) (agree indirect wrap zero)

/-- Eight imported rows: JAL/JALR, PC+4 and target wrapping, x0/nonzero rd.
    JALR's sums are odd; their bit-0 cleanup is exercised explicitly. -/
example (indirect wrap zero : Bool) :
    (⟨(row indirect wrap zero 30).val, (row indirect wrap zero 31).val⟩ : Arithmetic.Word).toBitVec =
      (if row indirect wrap zero 15 = 1 then 0 else (initial wrap).toBitVec + 4) ∧
    (⟨(row indirect wrap zero 30).val, (row indirect wrap zero 31).val⟩ : Arithmetic.Word).Bounded := by
  apply JumpBranchSlt.Proofs.jump_link (by decide) (satisfies indirect wrap zero)
  · cases indirect <;> simp [row]
  · exact ⟨rfl, rfl⟩
  · constructor <;> cases wrap <;> simp [row, initial] <;> decide
  · cases wrap <;> decide

example (indirect wrap zero : Bool) :
    (final indirect wrap).toBitVec =
      (if indirect then ((base indirect wrap).toBitVec + (offset indirect wrap).toBitVec) &&& 0xfffffffe
        else (base indirect wrap).toBitVec + (offset indirect wrap).toBitVec) ∧
      (final indirect wrap).toBitVec.toNat % 4 = 0 := by
  apply JumpBranchSlt.Proofs.jump_pc (w := row indirect wrap zero) (by decide) indirect
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
  have target := JumpBranchSlt.Proofs.jump_pc (base := ⟨7, 0⟩) (offset := ⟨65532, 65535⟩)
    (final := ⟨0, 0⟩) (by decide) true h ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
    (by constructor <;> decide) (by decide) (by decide)
    ⟨by decide, by decide⟩ (by decide) (by decide)
  exact (by decide : ¬ ((⟨0, 0⟩ : Arithmetic.Word).toBitVec =
    ((⟨7, 0⟩ : Arithmetic.Word).toBitVec + (⟨65532, 65535⟩ : Arithmetic.Word).toBitVec) &&& 0xfffffffe)) target.1

end Tests.Jump
