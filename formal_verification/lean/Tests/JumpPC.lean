import Tests.JumpControl

namespace Tests.JumpPC
open Airbender Verification

/-- Native JAL x1,-4 at PC zero: canonical RV32 target 0xfffffffc,
    with the same actual link write and port clocks as the +8 fixture. -/
def negativeJal (i : Nat) : ZMod mersenne31Modulus :=
  if i = 9 ∨ i = 13 ∨ i = 42 ∨ i = 48 then 65532
  else if i = 10 ∨ i = 14 ∨ i = 43 then 65535
  else JumpControl.assignment i

theorem negative_jal_constraints :
    FlatOperation.ConstraintsHoldFlat (environment negativeJal) JumpBranchSlt.importedConstraints := by
  simp [JumpBranchSlt.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    environment, negativeJal, JumpControl.assignment]
  repeat' apply And.intro
  all_goals first | (apply range16_contains; decide) |
    (apply timestamp19_contains; decide) | try decide
  all_goals
    simp only [Lookup.Contains, fixed3, Table.toRaw, conditionalControlTable,
      jumpCleanupTable, Table.fromStatic, StaticTable.toTable, ProvableType.fromElements,
      Expression.eval, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil,
      negativeJal, JumpControl.assignment]
    solve
    | refine ⟨⟨0, by decide⟩, ?_⟩
      norm_num [conditionalControlRow, controlFlag]
    | refine ⟨⟨65532, by decide⟩, ?_⟩
      norm_num [jumpCleanupRow]

theorem negative_jal_bounds :
    (negativeJal 13).val < 65536 ∧ (negativeJal 14).val < 65536 :=
  JumpBranchSlt.native_pc_bounds negative_jal_constraints (by decide)

/-- A field -1 target can satisfy every polynomial by changing the native high
    carry to one. The scalar query on candidate variable 43 still excludes it. -/
def noncanonical (i : Nat) : ZMod mersenne31Modulus :=
  if i = 14 ∨ i = 43 then -1 else if i = 44 then 1 else negativeJal i

theorem noncanonical_polynomials :
    ∀ equation ∈ FlatOperation.constraints JumpBranchSlt.importedConstraints,
      equation.eval (environment noncanonical) = 0 := by
  simp [JumpBranchSlt.importedConstraints, FlatOperation.constraints, Expression.eval,
    environment, noncanonical, negativeJal, JumpControl.assignment]
  decide

/-- Every other actual native query still accepts this witness. Only the
    candidate-high scalar query (index five) is removed in this test statement. -/
theorem noncanonical_other_queries :
    ∀ query ∈ (FlatOperation.lookups JumpBranchSlt.importedConstraints).eraseIdx 5,
      query.Contains (environment noncanonical) := by
  simp [JumpBranchSlt.importedConstraints, FlatOperation.lookups,
    environment]
  repeat' apply And.intro
  all_goals first | (apply range16_contains; decide) |
    (apply timestamp19_contains; decide) | try decide
  all_goals
    simp only [Lookup.Contains, fixed3, Table.toRaw, conditionalControlTable,
      jumpCleanupTable, Table.fromStatic, StaticTable.toTable, ProvableType.fromElements,
      Expression.eval, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil,
      noncanonical, negativeJal, JumpControl.assignment]
    solve
    | refine ⟨⟨0, by decide⟩, ?_⟩
      norm_num [conditionalControlRow, controlFlag]
    | refine ⟨⟨65532, by decide⟩, ?_⟩
      norm_num [jumpCleanupRow]


theorem noncanonical_native_rejected :
    ¬FlatOperation.ConstraintsHoldFlat (environment noncanonical) JumpBranchSlt.importedConstraints := by
  intro holds
  have high := JumpBranchSlt.Proofs.candidate_high_bound holds
  change (-1 : ZMod mersenne31Modulus).val < 65536 at high
  exact (by decide : ¬(-1 : ZMod mersenne31Modulus).val < 65536) high

/-- All five supported masks exclude the bad raw outgoing high limb, without a
    supplied terminal range or a verifier-PC closure premise. -/
theorem supported_negative_high_rejected {w : Nat → ZMod mersenne31Modulus}
    (mask : (w 12).val ∈ [1, 2, 4, 8, 16]) (bad : w 14 = -1) :
    ¬FlatOperation.ConstraintsHoldFlat (environment w) JumpBranchSlt.importedConstraints := by
  intro holds
  have high := (JumpBranchSlt.native_pc_bounds holds mask).2
  rw [bad] at high
  exact (by decide : ¬(-1 : ZMod mersenne31Modulus).val < 65536) high

end Tests.JumpPC
