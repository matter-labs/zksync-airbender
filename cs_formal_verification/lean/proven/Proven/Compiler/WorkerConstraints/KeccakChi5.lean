module
public import Proven.Compiler.WorkerConstraints.KeccakChi5.Lookups000
public import Proven.Compiler.WorkerConstraints.KeccakChi5.Lookups001
public import Proven.Compiler.WorkerConstraints.KeccakChi5.Converse0_000
public import Proven.Compiler.WorkerConstraints.KeccakChi5.Converse0_001
public import Proven.Compiler.WorkerConstraints.KeccakChi5.Converse2_000
public import Mathlib.Tactic.FinCases
public import Proven.KernelExact

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakChi5
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- All description queries follow from the actual native lookup argument. -/
theorem lookups (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical)
    (arguments : NativeLookups.Arguments (circuitFor .chi5) (selectorsFor .chi5) physical (NativeWorkerSetup.rows .chi5)) :
    ∀ query ∈ FlatOperation.lookups (constraints .chi5), query.Contains (Verification.environment logical) := by
  rw [source_binding]
  kernel_exact (all_append (first := queries000) (rest := (queries001 ++ [])) (lookups000 physical logical agreement arguments) (all_append (first := queries001) (rest := []) (lookups001 physical logical agreement arguments) (by intro value member; cases member)))

/-- Complete accepted source queries supply every actual native request. -/
theorem tuples_membership (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .chi5)) :
    ∀ group values, values ∈ tuples physical group → ∃ index, values = NativeWorkerSetup.rows .chi5 group index := by
  intro group
  fin_cases group
  · kernel_exact (all_append (first := tuple0_000 physical) (rest := (tuple0_001 physical ++ [])) (converse0_000 physical logical agreement holds) (all_append (first := tuple0_001 physical) (rest := []) (converse0_001 physical logical agreement holds) (by intro value member; cases member)))
  · intro values member
    change values ∈ ([] : List (List F)) at member
    cases member
  · kernel_exact (all_append (first := tuple2_000 physical) (rest := []) (converse2_000 physical logical agreement holds) (by intro value member; cases member))

/-- Source lookup acceptance and actual placement construct the full native matching argument. -/
noncomputable def arguments_of_description (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .chi5)) :
    NativeLookups.Arguments (circuitFor .chi5) (selectorsFor .chi5) physical (NativeWorkerSetup.rows .chi5) :=
  native_arguments (family := .chi5) (physical := physical) (tuples physical) (binding physical) (tuples_membership physical logical agreement holds)

end Airbender.Compiler.WorkerConstraints.KeccakChi5
