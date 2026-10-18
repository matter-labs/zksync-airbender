import Airbender.Review.Circuits.JumpBranchSlt.Theorems
import Airbender.Proofs.JumpBranchSlt.ControlTables
import Airbender.Proofs.JumpBranchSlt.ArtifactChecks
import Airbender.Proofs.Constraints
import Airbender.Review.Helpers.Properties

/-- error: native fixed tables do not match the explicit target -/
#guard_msgs in
import_clean rejectedMemoryMode from "../../cs/jump_branch_slt_preprocessed_layout.json" word_memory_lookups

/-- error: native fixed tables do not match the explicit target -/
#guard_msgs in
import_clean rejectedControlMode from "../../cs/word_only_load_store_preprocessed_layout.json" control_lookups

/-- error: v2 fixed lookups require an explicit native target -/
#guard_msgs in
import_clean rejectedMissingMode from "../../cs/jump_branch_slt_preprocessed_layout.json"

namespace Tests.JumpControl
open Airbender Verification

-- Native JAL x1,+8 at PC zero: actual masked link write four, target PC eight,
-- initialized machine clock four, previous port clocks zero and strict borrows.
def assignment (i : Nat) : ZMod mersenne31Modulus :=
  if i = 2 then 4 else if i = 15 then 8
  else if i = 4 ∨ i = 7 ∨ i = 12 ∨ i = 17 ∨ i = 31 ∨ i = 33 ∨
      i = 36 ∨ i = 53 ∨ i = 56 ∨ i = 59 then 1
  else if i = 9 ∨ i = 13 ∨ i = 42 ∨ i = 48 then 8
  else if i = 26 ∨ i = 38 then 4
  else if i = 30 then 536870912
  else if i = 32 ∨ i = 34 then 32768 else 0

/-- A nonempty active native witness satisfies every imported equation and
    lookup, including both fixed tables. Original Sail execution is separate. -/
theorem native_jal_constraints :
    FlatOperation.ConstraintsHoldFlat (environment assignment) JumpBranchSlt.importedConstraints := by
  simp [JumpBranchSlt.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    environment, assignment]
  repeat' apply And.intro
  all_goals first | (apply range16_contains; decide) |
    (apply timestamp19_contains; decide) | try decide
  all_goals
    simp only [Lookup.Contains, fixed3, Table.toRaw, conditionalControlTable,
      jumpCleanupTable, Table.fromStatic, StaticTable.toTable, ProvableType.fromElements,
      Expression.eval, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, assignment]
    solve
    | refine ⟨⟨0, by decide⟩, ?_⟩
      norm_num [conditionalControlRow, controlFlag]
    | refine ⟨⟨8, by decide⟩, ?_⟩
      norm_num [jumpCleanupRow]

theorem native_jal_effects : JumpBranchSlt.FixedEffects assignment :=
  JumpBranchSlt.native_fixed_effects native_jal_constraints

/-- Bit one is retained for the alignment obligation while both low bits clear. -/
theorem cleanup_low_bits : jumpCleanupRow ⟨3, by decide⟩ = #v[3, 1, 0] ∧
    jumpCleanupRow ⟨65535, by decide⟩ = #v[65535, 1, 65532] := by decide

/-- Signed comparison follows sign1 when signs differ; unsigned retains borrow. -/
theorem signed_unsigned : controlFlag 4 2 = true ∧ controlFlag 4 3 = false ∧
    controlFlag 8 4 = false ∧ controlFlag 8 5 = true := by decide

theorem equality_branches : controlFlag 2 0 = true ∧ controlFlag 2 1 = false ∧
    controlFlag 0 0 = false ∧ controlFlag 0 1 = true := by decide

theorem altered_cleanup_rejected :
    ¬jumpCleanupTable.Contains #[] (#v[3, 1, 4] : Vector (ZMod mersenne31Modulus) 3) := by
  intro member
  have wrong := (JumpBranchSlt.Proofs.cleanup_values member).2.2
  simp only [show (3 : ZMod mersenne31Modulus).val = 3 from by decide] at wrong
  change (4 : ZMod mersenne31Modulus) = 0 at wrong
  exact (by decide : (4 : ZMod mersenne31Modulus) ≠ 0) wrong

theorem altered_signed_result_rejected :
    ¬conditionalControlTable.Contains #[] (#v[4, 2, 0] : Vector (ZMod mersenne31Modulus) 3) := by
  intro member
  have wrong := (JumpBranchSlt.Proofs.conditional_values member).2.2
  simp only [show (4 : ZMod mersenne31Modulus).val = 4 from by decide,
    show (2 : ZMod mersenne31Modulus).val = 2 from by decide] at wrong
  change (0 : ZMod mersenne31Modulus) = 1 at wrong
  exact (by decide : (0 : ZMod mersenne31Modulus) ≠ 1) wrong

theorem oversized_flags_rejected :
    ¬conditionalControlTable.Contains #[] (#v[16, 0, 0] : Vector (ZMod mersenne31Modulus) 3) := by
  intro member
  have wrong := (JumpBranchSlt.Proofs.conditional_values member).1
  exact (by decide : ¬(16 : ZMod mersenne31Modulus).val < 16) wrong

/-- A target with bit one set is excluded by the actual native JAL equation,
    even though its cleanup-table row itself is valid. -/
private def misaligned (i : Nat) : ZMod mersenne31Modulus :=
  if i = 9 ∨ i = 42 then 3 else if i = 47 then 1
  else if i = 13 ∨ i = 48 then 0 else assignment i

theorem unaligned_jal_rejected :
    ¬FlatOperation.ConstraintsHoldFlat (environment misaligned) JumpBranchSlt.importedConstraints := by
  intro holds
  have wrong := assertion_of_holds holds ⟨26, by rw [JumpBranchSlt.Proofs.constraint_count]; decide⟩
  norm_num [JumpBranchSlt.importedConstraints, FlatOperation.constraints, Expression.eval,
    environment, misaligned, assignment] at wrong

end Tests.JumpControl
