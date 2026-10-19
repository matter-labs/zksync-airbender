import Tests.ControlComparisons
import Airbender.Review.Trace.Families.JumpBranchSlt.ComparisonPC

namespace Tests.ComparisonPC
open Airbender Trace Verification Arithmetic ControlComparisons

/-- Reuse the four actual-byte, separately initialized comparison histories. -/
theorem public_pc (kind : Kind) :
    (Word.mk (assignment kind 13).val (assignment kind 14).val).toBitVec =
      BitVec.ofNat 32 (4 * kind.index+4) ∧
    (Word.mk (assignment kind 13).val (assignment kind 14).val).toBitVec.toNat % 4 = 0 := by
  have pc := JumpBranchSlt.public_comparison_pc (program_image kind)
    (accepted kind) (decoded kind) (nativeRow kind) (by simp [trace])
    (by cases kind <;> decide)
  exact ⟨pc.1.trans (by cases kind <;> decide),pc.2⟩

/-- Full native local witness for comparison PC rollover. This is not a new
    initialized/public-decoder wrap trace or a native program export. -/
def wrap (i : Nat) : ZMod mersenne31Modulus :=
  if i = 0 then 65532 else if i = 1 then 65535
  else if i = 13 ∨ i = 14 ∨ i = 42 ∨ i = 43 ∨ i = 48 then 0
  else if i = 44 ∨ i = 50 then 1 else assignment .sltu i

theorem wrap_native :
    FlatOperation.ConstraintsHoldFlat (environment wrap) JumpBranchSlt.importedConstraints := by
  simp [JumpBranchSlt.importedConstraints,FlatOperation.ConstraintsHoldFlat,
    Expression.eval,environment,wrap,assignment,Kind.immediate,Kind.zero,
    Kind.result,Kind.control]
  repeat' apply And.intro
  all_goals first | (apply range16_contains; decide) | (apply timestamp19_contains; decide) | try decide
  all_goals
    simp only [Lookup.Contains,fixed3,Table.toRaw,conditionalControlTable,
      jumpCleanupTable,Table.fromStatic,StaticTable.toTable,ProvableType.fromElements,
      Expression.eval,Vector.map_mk,List.map_toArray,List.map_cons,List.map_nil,
      wrap,assignment,Kind.immediate,Kind.signed,Kind.zero,Kind.result,Kind.control]
    solve
    | refine ⟨⟨35,by decide⟩,?_⟩; norm_num [conditionalControlRow,controlFlag]
    | refine ⟨⟨0,by decide⟩,?_⟩; norm_num [jumpCleanupRow]

theorem wrap_pc : (Word.mk (wrap 13).val (wrap 14).val).toBitVec = 0 ∧
    (Word.mk (wrap 13).val (wrap 14).val).toBitVec.toNat % 4 = 0 := by
  have pc := JumpBranchSlt.Proofs.comparison_pc wrap_native (by decide)
    (by decide) (by constructor <;> decide) (by decide)
  exact ⟨pc.1.trans (by decide),pc.2⟩

def altered (i : Nat) : ZMod mersenne31Modulus :=
  if i = 13 then 8 else assignment .slt i

/-- An altered outgoing PC keeps all decoder columns and fails native acceptance. -/
theorem altered_pc_rejected :
    ¬FlatOperation.ConstraintsHoldFlat (environment altered) JumpBranchSlt.importedConstraints := by
  intro holds
  have pc := JumpBranchSlt.Proofs.comparison_pc holds (by decide)
    (by decide) (by constructor <;> decide) (by decide)
  have wrong : (8 : BitVec 32) = 4 := by convert pc.1 using 1 <;> decide
  exact (by decide : (8 : BitVec 32) ≠ 4) wrong

end Tests.ComparisonPC
