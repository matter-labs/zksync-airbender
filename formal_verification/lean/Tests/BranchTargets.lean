import Tests.Branches
import Airbender.Review.Trace.Families.JumpBranchSlt.BranchTargets

namespace Tests.BranchTargets
open Airbender Trace Verification Arithmetic
open Tests.Branches (Mode Op)

/-- Reuse all eighteen original-byte, separately initialized branch histories. -/
theorem public_targets (mode : Mode) (op : Op) :
    (Word.mk (Tests.Branches.assignment mode op 13).val
      (Tests.Branches.assignment mode op 14).val).toBitVec = BitVec.ofNat 32 (op.finish mode) ∧
    (Word.mk (Tests.Branches.assignment mode op 13).val
      (Tests.Branches.assignment mode op 14).val).toBitVec.toNat % 4 = 0 := by
  have target := JumpBranchSlt.public_branch_targets (Tests.Branches.program_image mode op)
    (Tests.Branches.public_inputs mode op) (Tests.Branches.accepted mode op)
    (Tests.Branches.decoded mode op) (Tests.Branches.nativeRow mode op)
    (by simp [Tests.Branches.trace]) (by cases mode <;> cases op <;> decide)
  exact ⟨target.1.trans (by cases mode <;> cases op <;> decide),target.2⟩

inductive Case | negative | takenWrap | untakenWrap deriving DecidableEq
namespace Case
def taken : Case → Bool | .untakenWrap => false | _ => true
def target : Case → Nat | .negative => 4294967292 | .takenWrap => 4 | .untakenWrap => 0
end Case

/-- Full native local witnesses: taken -4, taken PC+8 wrap and untaken PC+4
    wrap with an ignored offset two. No initialized/public-decoder wrap trace
    or new native program export is claimed for these local cases. -/
def assignment : Case → Nat → ZMod mersenne31Modulus
  | .negative,i =>
    if i = 0 then 0 else if i = 1 then 0
    else if i = 9 then 65532 else if i = 10 then 65535
    else if i = 13 ∨ i = 42 ∨ i = 48 then 65532
    else if i = 14 ∨ i = 43 then 65535
    else if i = 44 ∨ i = 50 then 0
    else Tests.Branches.assignment .equal .beq i
  | .takenWrap,i =>
    if i = 0 then 65532 else if i = 1 then 65535
    else if i = 9 then 8 else if i = 10 then 0
    else if i = 13 ∨ i = 42 ∨ i = 48 then 4
    else if i = 14 ∨ i = 43 then 0
    else if i = 44 ∨ i = 50 then 1
    else Tests.Branches.assignment .equal .beq i
  | .untakenWrap,i =>
    if i = 0 then 65532 else if i = 1 then 65535
    else if i = 9 then 2 else if i = 10 then 0
    else if i = 13 ∨ i = 42 ∨ i = 48 then 0
    else if i = 14 ∨ i = 43 then 0
    else if i = 44 ∨ i = 50 then 1
    else Tests.Branches.assignment .negative .beq i

theorem native_constraints (test : Case) :
    FlatOperation.ConstraintsHoldFlat (environment (assignment test)) JumpBranchSlt.importedConstraints := by
  cases test
  all_goals
    apply FlatOperation.constraintsHoldFlat_iff_forall_mem.mpr
    constructor
    · simp only [JumpBranchSlt.importedConstraints,FlatOperation.constraints,List.forall_mem_cons]
      repeat' apply And.intro
      all_goals first | (intro a bad; cases bad) | decide +kernel
    · simp only [JumpBranchSlt.importedConstraints,FlatOperation.lookups,List.forall_mem_cons]
      repeat' apply And.intro
      all_goals first | (intro a bad; cases bad) | (apply range16_contains; decide +kernel) |
        (apply timestamp19_contains; decide +kernel) | skip
      all_goals simp only [Lookup.Contains,fixed3,Table.toRaw,conditionalControlTable,
        jumpCleanupTable,Table.fromStatic,StaticTable.toTable,ProvableType.fromElements,
        Expression.eval,Vector.map_mk,List.map_toArray,List.map_cons,List.map_nil,
        environment,assignment,Tests.Branches.assignment,Tests.Branches.Op.tag,Tests.Branches.Op.result]
      all_goals solve
      | refine ⟨⟨16,by decide⟩,?_⟩; norm_num [conditionalControlRow,controlFlag]
      | refine ⟨⟨32,by decide⟩,?_⟩; norm_num [conditionalControlRow,controlFlag]
      | refine ⟨⟨65532,by decide⟩,?_⟩; norm_num [jumpCleanupRow]
      | refine ⟨⟨4,by decide⟩,?_⟩; norm_num [jumpCleanupRow]
      | refine ⟨⟨0,by decide⟩,?_⟩; norm_num [jumpCleanupRow]

theorem local_targets (test : Case) :
    (Word.mk (assignment test 13).val (assignment test 14).val).toBitVec = BitVec.ofNat 32 test.target ∧
    (Word.mk (assignment test 13).val (assignment test 14).val).toBitVec.toNat % 4 = 0 := by
  have target := JumpBranchSlt.Proofs.branch_pc test.taken (native_constraints test)
    (by cases test <;> decide) (by cases test <;> decide) (by cases test <;> decide)
    (initial := ⟨(assignment test 0).val,(assignment test 1).val⟩)
    (offset := ⟨(assignment test 9).val,(assignment test 10).val⟩)
    ⟨rfl,rfl,(ZMod.natCast_zmod_val _).symm,(ZMod.natCast_zmod_val _).symm⟩
    (by constructor <;> cases test <;> decide) (by cases test <;> decide)
    (by constructor <;> cases test <;> decide) (by cases test <;> decide)
  exact ⟨target.1.trans (by cases test <;> decide),target.2⟩

theorem untaken_offset_two : assignment .untakenWrap 9 = 2 ∧ assignment .untakenWrap 46 = 0 ∧
    (Word.mk (assignment .untakenWrap 13).val (assignment .untakenWrap 14).val).toBitVec = 0 :=
  ⟨by decide,by decide,(local_targets .untakenWrap).1⟩

def misaligned (i : Nat) : ZMod mersenne31Modulus :=
  if i = 9 ∨ i = 42 then 2 else if i = 47 then 1 else if i = 13 ∨ i = 48 then 0
  else Tests.Branches.assignment .equal .beq i

/-- Cleanup can round two to zero; the actual taken-branch bit-one assertion
    rejects that row instead of silently changing its branch target. -/
theorem misaligned_cleanup : jumpCleanupTable.Contains #[] #v[misaligned 42,misaligned 47,misaligned 48] := by
  refine ⟨⟨2,by decide⟩,?_⟩
  decide +kernel

theorem misaligned_rejected :
    ¬FlatOperation.ConstraintsHoldFlat (environment misaligned) JumpBranchSlt.importedConstraints := by
  intro holds
  have checked := assertion_of_holds holds ⟨26,by rw [JumpBranchSlt.Proofs.constraint_count]; decide⟩
  exact (by decide +kernel : Expression.eval (environment misaligned)
    (FlatOperation.constraints JumpBranchSlt.importedConstraints)[26] ≠ 0) checked

end Tests.BranchTargets
