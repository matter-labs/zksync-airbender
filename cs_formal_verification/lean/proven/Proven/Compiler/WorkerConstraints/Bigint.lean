module
public import Proven.Compiler.WorkerConstraints.Bigint.Lookups000
public import Proven.Compiler.WorkerConstraints.Bigint.Lookups001
public import Proven.Compiler.WorkerConstraints.Bigint.Lookups002
public import Proven.Compiler.WorkerConstraints.Bigint.Lookups003
public import Proven.Compiler.WorkerConstraints.Bigint.Lookups004
public import Proven.Compiler.WorkerConstraints.Bigint.Lookups005
public import Proven.Compiler.WorkerConstraints.Bigint.Lookups006
public import Proven.Compiler.WorkerConstraints.Bigint.Lookups007
public import Proven.Compiler.WorkerConstraints.Bigint.Lookups008
public import Proven.Compiler.WorkerConstraints.Bigint.Converse0_000
public import Proven.Compiler.WorkerConstraints.Bigint.Converse0_001
public import Proven.Compiler.WorkerConstraints.Bigint.Converse0_002
public import Proven.Compiler.WorkerConstraints.Bigint.Converse0_003
public import Proven.Compiler.WorkerConstraints.Bigint.Converse1_000
public import Proven.Compiler.WorkerConstraints.Bigint.Converse1_001
public import Proven.Compiler.WorkerConstraints.Bigint.Converse2_000
public import Proven.Compiler.WorkerConstraints.Bigint.Converse2_001
public import Proven.Compiler.WorkerConstraints.Bigint.Converse2_002
public import Mathlib.Tactic.FinCases
public import Proven.KernelExact

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.Bigint
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- All description queries follow from the actual native lookup argument. -/
theorem lookups (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∀ query ∈ FlatOperation.lookups (constraints .bigint), query.Contains (Verification.environment logical) := by
  rw [source_binding]
  kernel_exact (all_append (first := queries000) (rest := (queries001 ++ (queries002 ++ (queries003 ++ (queries004 ++ (queries005 ++ (queries006 ++ (queries007 ++ (queries008 ++ []))))))))) (lookups000 physical logical agreement arguments) (all_append (first := queries001) (rest := (queries002 ++ (queries003 ++ (queries004 ++ (queries005 ++ (queries006 ++ (queries007 ++ (queries008 ++ [])))))))) (lookups001 physical logical agreement arguments) (all_append (first := queries002) (rest := (queries003 ++ (queries004 ++ (queries005 ++ (queries006 ++ (queries007 ++ (queries008 ++ []))))))) (lookups002 physical logical agreement arguments) (all_append (first := queries003) (rest := (queries004 ++ (queries005 ++ (queries006 ++ (queries007 ++ (queries008 ++ [])))))) (lookups003 physical logical agreement arguments) (all_append (first := queries004) (rest := (queries005 ++ (queries006 ++ (queries007 ++ (queries008 ++ []))))) (lookups004 physical logical agreement arguments) (all_append (first := queries005) (rest := (queries006 ++ (queries007 ++ (queries008 ++ [])))) (lookups005 physical logical agreement arguments) (all_append (first := queries006) (rest := (queries007 ++ (queries008 ++ []))) (lookups006 physical logical agreement arguments) (all_append (first := queries007) (rest := (queries008 ++ [])) (lookups007 physical logical agreement arguments) (all_append (first := queries008) (rest := []) (lookups008 physical logical agreement arguments) (by intro value member; cases member))))))))))

/-- Complete accepted source queries supply every actual native request. -/
theorem tuples_membership (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∀ group values, values ∈ tuples physical group → ∃ index, values = NativeWorkerSetup.rows .bigint group index := by
  intro group
  fin_cases group
  · kernel_exact (all_append (first := tuple0_000 physical) (rest := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (converse0_000 physical logical agreement holds) (all_append (first := tuple0_001 physical) (rest := (tuple0_002 physical ++ (tuple0_003 physical ++ []))) (converse0_001 physical logical agreement holds) (all_append (first := tuple0_002 physical) (rest := (tuple0_003 physical ++ [])) (converse0_002 physical logical agreement holds) (all_append (first := tuple0_003 physical) (rest := []) (converse0_003 physical logical agreement holds) (by intro value member; cases member)))))
  · kernel_exact (all_append (first := tuple1_000 physical) (rest := (tuple1_001 physical ++ [])) (converse1_000 physical logical agreement holds) (all_append (first := tuple1_001 physical) (rest := []) (converse1_001 physical logical agreement holds) (by intro value member; cases member)))
  · kernel_exact (all_append (first := tuple2_000 physical) (rest := (tuple2_001 physical ++ (tuple2_002 physical ++ []))) (converse2_000 physical logical agreement holds) (all_append (first := tuple2_001 physical) (rest := (tuple2_002 physical ++ [])) (converse2_001 physical logical agreement holds) (all_append (first := tuple2_002 physical) (rest := []) (converse2_002 physical logical agreement holds) (by intro value member; cases member))))

/-- Source lookup acceptance and actual placement construct the full native matching argument. -/
noncomputable def arguments_of_description (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint) :=
  native_arguments (family := .bigint) (physical := physical) (tuples physical) (binding physical) (tuples_membership physical logical agreement holds)

end Airbender.Compiler.WorkerConstraints.Bigint
