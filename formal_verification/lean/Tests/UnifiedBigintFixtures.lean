import Tests.BigintMemory

namespace Tests.UnifiedDelegation.BigintFixtures
open Airbender Trace Arithmetic Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def abiAssignment (highControl : Bool) (column : Nat) : ZMod babyBearModulus :=
  if column = 55 ∨ column = 56 ∨ column = 59 then (if highControl then 1 else 0)
  else if column = 66 then 0
  else if column = 1 then 5 else Tests.BigintMemory.row column

private def bigintReferenceRow (index : Fin 1390592) : Nat × Nat × Nat :=
  if index.val < 262144 then (index.val / 512, index.val % 512, 22)
  else if index.val < 1310720 then ((index.val - 262144) / 1024, (index.val - 262144) % 1024, 23)
  else if index.val < 1312768 then (index.val - 1310720, 0, 24)
  else if index.val < 1316864 then (index.val - 1312768, 0, 25)
  else if index.val < 1325056 then (index.val - 1316864, 0, 26)
  else (index.val - 1325056, (index.val - 1325056) % 256, 41)

private theorem bigint_lookup_relation (entry : Vector (Expression (ZMod babyBearModulus)) 3)
    (env : Environment (ZMod babyBearModulus)) :
    (Lookup.mk Bigint.setupTable.toRaw entry).Contains env ↔
      ∃ i : Fin 1390592, entry.map (Expression.eval env) =
        #v[((bigintReferenceRow i).1 : ZMod babyBearModulus),
          ((bigintReferenceRow i).2.1 : ZMod babyBearModulus),
          ((bigintReferenceRow i).2.2 : ZMod babyBearModulus)] := by
  change (∃ i : Fin 1390592, entry.map (Expression.eval env) =
        #v[((Bigint.setupRow i).1 : ZMod babyBearModulus),
          ((Bigint.setupRow i).2.1 : ZMod babyBearModulus),
          ((Bigint.setupRow i).2.2 : ZMod babyBearModulus)]) ↔ _
  simp only [Bigint.Proofs.setup_row_characterization, bigintReferenceRow]

theorem abiCore (highControl : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (abiAssignment highControl))
    (Bigint.importedConstraints Bigint.setupTable) := by
  cases highControl <;> simp [Bigint.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, abiAssignment, Tests.BigintMemory.row,
    bigint_lookup_relation]
  all_goals repeat' apply And.intro
  all_goals solve
    | (apply Verification.range16_contains; decide +kernel)
    | (apply Trace.Proofs.range_contains; decide +kernel)
    | (refine ⟨⟨0, by decide +kernel⟩, ?_⟩; simp only [bigintReferenceRow]; decide +kernel)
    | (refine ⟨⟨262144, by decide +kernel⟩, ?_⟩; simp only [bigintReferenceRow]; decide +kernel)
    | (refine ⟨⟨1310720, by decide +kernel⟩, ?_⟩; simp only [bigintReferenceRow]; decide +kernel)
    | (refine ⟨⟨1312768, by decide +kernel⟩, ?_⟩; simp only [bigintReferenceRow]; decide +kernel)
    | (refine ⟨⟨1316864, by decide +kernel⟩, ?_⟩; simp only [bigintReferenceRow]; decide +kernel)
    | (refine ⟨⟨1325056, by decide +kernel⟩, ?_⟩; simp only [bigintReferenceRow]; decide +kernel)


def frameWorkerAssignment (column : Nat) : ZMod babyBearModulus :=
  if column = 1 then 9 else Tests.BigintMemory.row column

theorem frameWorkerCore : FlatOperation.ConstraintsHoldFlat
    (Verification.environment frameWorkerAssignment) (Bigint.importedConstraints Bigint.setupTable) := by
  have established := Tests.BigintMemory.core
  simp only [Bigint.importedConstraints, FlatOperation.ConstraintsHoldFlat] at established ⊢
  simp only [bigint_lookup_relation] at established ⊢
  simpa [Verification.environment, Expression.eval, Lookup.Contains, Table.toRaw, fromElements,
    timestampLookup, Verification.range16, frameWorkerAssignment, Tests.BigintMemory.row] using established

def returnCarryAssignment (column : Nat) : ZMod babyBearModulus :=
  if column = 1 then 5
  else if 39 ≤ column ∧ column < 55 then 65535
  else if column = 55 then 192
  else if column = 57 ∨ column = 65 ∨ (83 ≤ column ∧ column < 99) then 1
  else if column = 215 then 0
  else if 115 ≤ column ∧ column < 131 then 255
  else Tests.BigintMemory.row column

theorem returnCarryCore : FlatOperation.ConstraintsHoldFlat
    (Verification.environment returnCarryAssignment) (Bigint.importedConstraints Bigint.setupTable) := by
  simp [Bigint.importedConstraints, FlatOperation.ConstraintsHoldFlat, Verification.environment,
    Expression.eval, returnCarryAssignment, Tests.BigintMemory.row, bigint_lookup_relation]
  all_goals repeat' apply And.intro
  all_goals solve
    | (apply Verification.range16_contains; decide +kernel)
    | (apply Trace.Proofs.range_contains; decide +kernel)
    | (refine ⟨⟨0, by decide⟩, ?_⟩; simp only [bigintReferenceRow]; decide +kernel)
    | (refine ⟨⟨262144, by decide⟩, ?_⟩; simp only [bigintReferenceRow]; decide +kernel)
    | (refine ⟨⟨1310720, by decide⟩, ?_⟩; simp only [bigintReferenceRow]; decide +kernel)
    | (refine ⟨⟨1312768, by decide⟩, ?_⟩; simp only [bigintReferenceRow]; decide +kernel)
    | (refine ⟨⟨1316864, by decide⟩, ?_⟩; simp only [bigintReferenceRow]; decide +kernel)
    | (refine ⟨⟨1325056, by decide⟩, ?_⟩; simp only [bigintReferenceRow]; decide +kernel)
    | (refine ⟨⟨1390591, by decide⟩, ?_⟩; simp only [bigintReferenceRow]; decide +kernel)
    | norm_num


end Tests.UnifiedDelegation.BigintFixtures
