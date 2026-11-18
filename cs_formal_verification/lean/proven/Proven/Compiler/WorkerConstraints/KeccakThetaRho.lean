module
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Lookups000
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Lookups001
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Lookups002
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Lookups003
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Converse0_000
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Converse0_001
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Converse0_002
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Converse0_003
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Converse2_000
public import Mathlib.Tactic.FinCases
public import Proven.KernelExact

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakThetaRho
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- All description queries follow from the actual native lookup argument. -/
theorem lookups (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (arguments : NativeLookups.Arguments (circuitFor .thetaRho) (selectorsFor .thetaRho) physical (NativeWorkerSetup.rows .thetaRho)) :
    ∀ query ∈ FlatOperation.lookups (constraints .thetaRho), query.Contains (Verification.environment logical) := by
  rw [source_binding]
  kernel_exact (all_append (first := queries000) (rest := (queries001 ++ (queries002 ++ (queries003 ++ [])))) (lookups000 physical logical agreement arguments) (all_append (first := queries001) (rest := (queries002 ++ (queries003 ++ []))) (lookups001 physical logical agreement arguments) (all_append (first := queries002) (rest := (queries003 ++ [])) (lookups002 physical logical agreement arguments) (all_append (first := queries003) (rest := []) (lookups003 physical logical agreement arguments) (by intro value member; cases member)))))

/-- Complete accepted source queries supply every actual native request. -/
theorem tuples_membership (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∀ group values, values ∈ tuples physical group → ∃ index, values = NativeWorkerSetup.rows .thetaRho group index := by
  intro group
  fin_cases group
  · kernel_exact (all_append (first := tuple0_000 physical) (rest := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (converse0_000 physical logical agreement holds) (all_append (first := tuple0_001 physical) (rest := (tuple0_002 physical ++ (tuple0_003 physical ++ []))) (converse0_001 physical logical agreement holds) (all_append (first := tuple0_002 physical) (rest := (tuple0_003 physical ++ [])) (converse0_002 physical logical agreement holds) (all_append (first := tuple0_003 physical) (rest := []) (converse0_003 physical logical agreement holds) (by intro value member; cases member)))))
  · intro values member
    change values ∈ ([] : List (List F)) at member
    cases member
  · kernel_exact (all_append (first := tuple2_000 physical) (rest := []) (converse2_000 physical logical agreement holds) (by intro value member; cases member))

/-- Source lookup acceptance and actual placement construct the full native matching argument. -/
noncomputable def arguments_of_description (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    NativeLookups.Arguments (circuitFor .thetaRho) (selectorsFor .thetaRho) physical (NativeWorkerSetup.rows .thetaRho) :=
  native_arguments (family := .thetaRho) (physical := physical) (tuples physical) (binding physical) (tuples_membership physical logical agreement holds)

end Airbender.Compiler.WorkerConstraints.KeccakThetaRho
