import Slop.JumpBranchSlt.Claims
import Slop.JumpBranchSlt.Completeness.Witness

namespace Tests.Comparison
open Airbender

/-- A selected SLTU row with zero operands and correct lookup results, but an
    unbounded final-PC high limb. This is a local-interface counterexample, not a
    claim that the full decoder/ROM/execution arguments accept the row. -/
private def row : Nat → ZMod babyBearModulus
  | 4 | 7 | 13 | 40 | 41 => 1
  | 10 => 3
  | 16 | 18 | 36 => 4
  | 17 => 2013200385
  | _ => 0

theorem unboundedFinalPCSatisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment row)
      JumpBranchSlt.importedConstraints := by
  simp [JumpBranchSlt.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Expression.eval, Verification.environment, row]
  repeat' apply And.intro
  all_goals first
    | (apply Verification.range16_contains; decide)
    | (with_unfolding_all change ∃ i : Fin 131072,
         ((0, 1) : fieldPair (ZMod babyBearModulus)) = ((i.val : ZMod babyBearModulus), ((if i.val = 0 then 1 else 0 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨0, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 65536,
         ((0, 0) : fieldPair (ZMod babyBearModulus)) = ((i.val : ZMod babyBearModulus), ((i.val / 32768 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨0, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 4194304,
         ((1835008, 0) : fieldPair (ZMod babyBearModulus)) = ((i.val : ZMod babyBearModulus), (Verification.conditionalValue i.val : ZMod babyBearModulus))
       exact ⟨⟨1835008, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 65536,
         ((4, 0, 4) : fieldTriple (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((i.val / 2 % 2 : Nat) : ZMod babyBearModulus), ((i.val - i.val % 4 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨4, by decide⟩, rfl⟩)
    | decide

example : ¬ ((⟨4, (row 17).val⟩ : Arithmetic.Word).toBitVec =
    (⟨0, 0⟩ : Arithmetic.Word).toBitVec + 4) := by decide

/-- The malformed local row cannot be an outgoing PC in the logical global
    interface, for any program or terminal boundary. Cryptographic enforcement
    of this interface is not claimed here. -/
theorem unboundedFinalPCNotComposable {n : Nat}
    (context : PCState.Context babyBearModulus n)
    (outgoing : PCState.Outgoing context (row 16, row 17)) : ¬ PCState.Interface context := by
  intro global
  have bounds := JumpBranchSlt.final_pc_bounds (by decide) global outgoing unboundedFinalPCSatisfies
  exact (by decide : ¬ (row 17).val < Arithmetic.limbBase) bounds.2

def edgeRow (signed immediate wrapPC : Bool) : Nat → ZMod babyBearModulus
  | 0 => if wrapPC then 65532 else 0
  | 1 => if wrapPC then 65535 else 0
  | 4 | 5 | 13 | 34 | 37 | 38 => 1
  | 30 | 44 | 47 => if signed then 0 else 1
  | 6 => if immediate then 0 else 2
  | 7 => if immediate then 1 else 2
  | 8 | 9 => if immediate then 65535 else 0
  | 10 => if signed then 2 else 3
  | 16 | 36 => if wrapPC then 0 else 4
  | 18 => 4
  | 39 | 40 => if wrapPC then 1 else 0
  | 26 | 27 => if immediate then 0 else 65535
  | 43 => 65535
  | _ => 0

/-- The honest inputs `edgeRow` is built from: `0` against `-1`, rd = x1 or x2. -/
def edgeWitness (signed immediate wrapPC : Bool) : JumpBranchSlt.Completeness.Inputs where
  sel := 2
  rdZero := false
  funct3 := if signed then 2 else 3
  rs1 := 1
  rs2 := if immediate then 0 else 2
  rd := if immediate then 1 else 2
  pcLo := if wrapPC then 65532 else 0
  pcHi := if wrapPC then 65535 else 0
  aLo := 0
  aHi := 0
  bLo := if immediate then 0 else 65535
  bHi := if immediate then 0 else 65535
  immLo := if immediate then 65535 else 0
  immHi := if immediate then 65535 else 0
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

private theorem edgeValid (signed immediate wrapPC : Bool) :
    (edgeWitness signed immediate wrapPC).Valid := by
  cases signed <;> cases immediate <;> cases wrapPC <;> constructor <;> decide

private theorem edgeAgree (signed immediate wrapPC : Bool) : ∀ i ∈ JumpBranchSlt.Completeness.columns,
    edgeRow signed immediate wrapPC i = (edgeWitness signed immediate wrapPC).honest i := by
  cases signed <;> cases immediate <;> cases wrapPC <;> decide

theorem edgeSatisfies (signed immediate wrapPC : Bool) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (edgeRow signed immediate wrapPC))
      JumpBranchSlt.importedConstraints :=
  JumpBranchSlt.Completeness.complete_of_agree _ (edgeValid signed immediate wrapPC)
    (edgeAgree signed immediate wrapPC)

/-- Unsigned 0 < 0xffffffff requires both subtraction borrows and resolves to one. -/
example : (⟨(edgeRow false false false 30).val, (edgeRow false false false 31).val⟩ : Arithmetic.Word).value = 1 := by
  have result := JumpBranchSlt.Proofs.unsigned_destination (p := babyBearModulus) (by decide)
    (left := ⟨0, 0⟩) (right := ⟨65535, 65535⟩) (edgeSatisfies false false false)
    rfl ⟨rfl, rfl, rfl⟩ rfl rfl ⟨rfl, rfl, rfl, rfl⟩
    (output := ⟨(edgeRow false false false 30).val, (edgeRow false false false 31).val⟩)
    ⟨rfl, rfl⟩ ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
  simpa [Arithmetic.Word.value, Arithmetic.limbBase] using result

private def negativeRow : Nat → ZMod babyBearModulus
  | 4 | 5 | 7 | 13 | 30 | 42 | 44 | 47 => 1
  | 6 | 10 => 2
  | 16 | 18 | 36 => 4
  | 22 | 23 | 34 | 35 => 65535
  | _ => 0

/-- `negativeRow`'s honest inputs: SLT of -1 against x0's 0, rd = x1. -/
private def negativeWitness : JumpBranchSlt.Completeness.Inputs :=
  { edgeWitness true false false with rd := 1, aLo := 65535, aHi := 65535, bLo := 0, bHi := 0 }

private theorem negativeSatisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment negativeRow)
      JumpBranchSlt.importedConstraints :=
  JumpBranchSlt.Completeness.complete_of_agree negativeWitness (by constructor <;> decide) (by decide)

end Tests.Comparison
