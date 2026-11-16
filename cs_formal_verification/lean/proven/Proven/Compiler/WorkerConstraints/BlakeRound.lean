module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Lookups000
public import Proven.Compiler.WorkerConstraints.BlakeRound.Lookups001
public import Proven.Compiler.WorkerConstraints.BlakeRound.Lookups002
public import Proven.Compiler.WorkerConstraints.BlakeRound.Lookups003
public import Proven.Compiler.WorkerConstraints.BlakeRound.Lookups004
public import Proven.Compiler.WorkerConstraints.BlakeRound.Lookups005
public import Proven.Compiler.WorkerConstraints.BlakeRound.Lookups006
public import Proven.Compiler.WorkerConstraints.BlakeRound.Lookups007
public import Proven.Compiler.WorkerConstraints.BlakeRound.Lookups008
public import Proven.Compiler.WorkerConstraints.BlakeRound.Lookups009
public import Proven.Compiler.WorkerConstraints.BlakeRound.Lookups010
public import Proven.Compiler.WorkerConstraints.BlakeRound.Lookups011
public import Proven.Compiler.WorkerConstraints.BlakeRound.Lookups012
public import Proven.Compiler.WorkerConstraints.BlakeRound.Lookups013
public import Proven.Compiler.WorkerConstraints.BlakeRound.Lookups014
public import Proven.Compiler.WorkerConstraints.BlakeRound.Lookups015
public import Proven.Compiler.WorkerConstraints.BlakeRound.Lookups016
public import Proven.Compiler.WorkerConstraints.BlakeRound.Lookups017
public import Proven.Compiler.WorkerConstraints.BlakeRound.Converse0_000
public import Proven.Compiler.WorkerConstraints.BlakeRound.Converse0_001
public import Proven.Compiler.WorkerConstraints.BlakeRound.Converse0_002
public import Proven.Compiler.WorkerConstraints.BlakeRound.Converse0_003
public import Proven.Compiler.WorkerConstraints.BlakeRound.Converse0_004
public import Proven.Compiler.WorkerConstraints.BlakeRound.Converse0_005
public import Proven.Compiler.WorkerConstraints.BlakeRound.Converse0_006
public import Proven.Compiler.WorkerConstraints.BlakeRound.Converse0_007
public import Proven.Compiler.WorkerConstraints.BlakeRound.Converse0_008
public import Proven.Compiler.WorkerConstraints.BlakeRound.Converse0_009
public import Proven.Compiler.WorkerConstraints.BlakeRound.Converse0_010
public import Proven.Compiler.WorkerConstraints.BlakeRound.Converse0_011
public import Proven.Compiler.WorkerConstraints.BlakeRound.Converse2_000
public import Proven.Compiler.WorkerConstraints.BlakeRound.Converse2_001
public import Proven.Compiler.WorkerConstraints.BlakeRound.Converse2_002
public import Proven.Compiler.WorkerConstraints.BlakeRound.Converse2_003
public import Proven.Compiler.WorkerConstraints.BlakeRound.Converse2_004
public import Proven.Compiler.WorkerConstraints.BlakeRound.Converse2_005
public import Mathlib.Tactic.FinCases
public import Proven.KernelExact

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- All description queries follow from the actual native lookup argument. -/
theorem lookups (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (arguments : NativeLookups.Arguments (circuitFor .blakeRound) (selectorsFor .blakeRound) physical (NativeWorkerSetup.rows .blakeRound)) :
    ∀ query ∈ FlatOperation.lookups (constraints .blakeRound), query.Contains (Verification.environment logical) := by
  rw [source_binding]
  kernel_exact (all_append (first := queries000) (rest := (queries001 ++ (queries002 ++ (queries003 ++ (queries004 ++ (queries005 ++ (queries006 ++ (queries007 ++ (queries008 ++ (queries009 ++ (queries010 ++ (queries011 ++ (queries012 ++ (queries013 ++ (queries014 ++ (queries015 ++ (queries016 ++ (queries017 ++ [])))))))))))))))))) (lookups000 physical logical agreement arguments) (all_append (first := queries001) (rest := (queries002 ++ (queries003 ++ (queries004 ++ (queries005 ++ (queries006 ++ (queries007 ++ (queries008 ++ (queries009 ++ (queries010 ++ (queries011 ++ (queries012 ++ (queries013 ++ (queries014 ++ (queries015 ++ (queries016 ++ (queries017 ++ []))))))))))))))))) (lookups001 physical logical agreement arguments) (all_append (first := queries002) (rest := (queries003 ++ (queries004 ++ (queries005 ++ (queries006 ++ (queries007 ++ (queries008 ++ (queries009 ++ (queries010 ++ (queries011 ++ (queries012 ++ (queries013 ++ (queries014 ++ (queries015 ++ (queries016 ++ (queries017 ++ [])))))))))))))))) (lookups002 physical logical agreement arguments) (all_append (first := queries003) (rest := (queries004 ++ (queries005 ++ (queries006 ++ (queries007 ++ (queries008 ++ (queries009 ++ (queries010 ++ (queries011 ++ (queries012 ++ (queries013 ++ (queries014 ++ (queries015 ++ (queries016 ++ (queries017 ++ []))))))))))))))) (lookups003 physical logical agreement arguments) (all_append (first := queries004) (rest := (queries005 ++ (queries006 ++ (queries007 ++ (queries008 ++ (queries009 ++ (queries010 ++ (queries011 ++ (queries012 ++ (queries013 ++ (queries014 ++ (queries015 ++ (queries016 ++ (queries017 ++ [])))))))))))))) (lookups004 physical logical agreement arguments) (all_append (first := queries005) (rest := (queries006 ++ (queries007 ++ (queries008 ++ (queries009 ++ (queries010 ++ (queries011 ++ (queries012 ++ (queries013 ++ (queries014 ++ (queries015 ++ (queries016 ++ (queries017 ++ []))))))))))))) (lookups005 physical logical agreement arguments) (all_append (first := queries006) (rest := (queries007 ++ (queries008 ++ (queries009 ++ (queries010 ++ (queries011 ++ (queries012 ++ (queries013 ++ (queries014 ++ (queries015 ++ (queries016 ++ (queries017 ++ [])))))))))))) (lookups006 physical logical agreement arguments) (all_append (first := queries007) (rest := (queries008 ++ (queries009 ++ (queries010 ++ (queries011 ++ (queries012 ++ (queries013 ++ (queries014 ++ (queries015 ++ (queries016 ++ (queries017 ++ []))))))))))) (lookups007 physical logical agreement arguments) (all_append (first := queries008) (rest := (queries009 ++ (queries010 ++ (queries011 ++ (queries012 ++ (queries013 ++ (queries014 ++ (queries015 ++ (queries016 ++ (queries017 ++ [])))))))))) (lookups008 physical logical agreement arguments) (all_append (first := queries009) (rest := (queries010 ++ (queries011 ++ (queries012 ++ (queries013 ++ (queries014 ++ (queries015 ++ (queries016 ++ (queries017 ++ []))))))))) (lookups009 physical logical agreement arguments) (all_append (first := queries010) (rest := (queries011 ++ (queries012 ++ (queries013 ++ (queries014 ++ (queries015 ++ (queries016 ++ (queries017 ++ [])))))))) (lookups010 physical logical agreement arguments) (all_append (first := queries011) (rest := (queries012 ++ (queries013 ++ (queries014 ++ (queries015 ++ (queries016 ++ (queries017 ++ []))))))) (lookups011 physical logical agreement arguments) (all_append (first := queries012) (rest := (queries013 ++ (queries014 ++ (queries015 ++ (queries016 ++ (queries017 ++ [])))))) (lookups012 physical logical agreement arguments) (all_append (first := queries013) (rest := (queries014 ++ (queries015 ++ (queries016 ++ (queries017 ++ []))))) (lookups013 physical logical agreement arguments) (all_append (first := queries014) (rest := (queries015 ++ (queries016 ++ (queries017 ++ [])))) (lookups014 physical logical agreement arguments) (all_append (first := queries015) (rest := (queries016 ++ (queries017 ++ []))) (lookups015 physical logical agreement arguments) (all_append (first := queries016) (rest := (queries017 ++ [])) (lookups016 physical logical agreement arguments) (all_append (first := queries017) (rest := []) (lookups017 physical logical agreement arguments) (by intro value member; cases member)))))))))))))))))))

/-- Complete accepted source queries supply every actual native request. -/
theorem tuples_membership (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∀ group values, values ∈ tuples physical group → ∃ index, values = NativeWorkerSetup.rows .blakeRound group index := by
  intro group
  fin_cases group
  · kernel_exact (all_append (first := tuple0_000 physical) (rest := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ (tuple0_004 physical ++ (tuple0_005 physical ++ (tuple0_006 physical ++ (tuple0_007 physical ++ (tuple0_008 physical ++ (tuple0_009 physical ++ (tuple0_010 physical ++ (tuple0_011 physical ++ [])))))))))))) (converse0_000 physical logical agreement holds) (all_append (first := tuple0_001 physical) (rest := (tuple0_002 physical ++ (tuple0_003 physical ++ (tuple0_004 physical ++ (tuple0_005 physical ++ (tuple0_006 physical ++ (tuple0_007 physical ++ (tuple0_008 physical ++ (tuple0_009 physical ++ (tuple0_010 physical ++ (tuple0_011 physical ++ []))))))))))) (converse0_001 physical logical agreement holds) (all_append (first := tuple0_002 physical) (rest := (tuple0_003 physical ++ (tuple0_004 physical ++ (tuple0_005 physical ++ (tuple0_006 physical ++ (tuple0_007 physical ++ (tuple0_008 physical ++ (tuple0_009 physical ++ (tuple0_010 physical ++ (tuple0_011 physical ++ [])))))))))) (converse0_002 physical logical agreement holds) (all_append (first := tuple0_003 physical) (rest := (tuple0_004 physical ++ (tuple0_005 physical ++ (tuple0_006 physical ++ (tuple0_007 physical ++ (tuple0_008 physical ++ (tuple0_009 physical ++ (tuple0_010 physical ++ (tuple0_011 physical ++ []))))))))) (converse0_003 physical logical agreement holds) (all_append (first := tuple0_004 physical) (rest := (tuple0_005 physical ++ (tuple0_006 physical ++ (tuple0_007 physical ++ (tuple0_008 physical ++ (tuple0_009 physical ++ (tuple0_010 physical ++ (tuple0_011 physical ++ [])))))))) (converse0_004 physical logical agreement holds) (all_append (first := tuple0_005 physical) (rest := (tuple0_006 physical ++ (tuple0_007 physical ++ (tuple0_008 physical ++ (tuple0_009 physical ++ (tuple0_010 physical ++ (tuple0_011 physical ++ []))))))) (converse0_005 physical logical agreement holds) (all_append (first := tuple0_006 physical) (rest := (tuple0_007 physical ++ (tuple0_008 physical ++ (tuple0_009 physical ++ (tuple0_010 physical ++ (tuple0_011 physical ++ [])))))) (converse0_006 physical logical agreement holds) (all_append (first := tuple0_007 physical) (rest := (tuple0_008 physical ++ (tuple0_009 physical ++ (tuple0_010 physical ++ (tuple0_011 physical ++ []))))) (converse0_007 physical logical agreement holds) (all_append (first := tuple0_008 physical) (rest := (tuple0_009 physical ++ (tuple0_010 physical ++ (tuple0_011 physical ++ [])))) (converse0_008 physical logical agreement holds) (all_append (first := tuple0_009 physical) (rest := (tuple0_010 physical ++ (tuple0_011 physical ++ []))) (converse0_009 physical logical agreement holds) (all_append (first := tuple0_010 physical) (rest := (tuple0_011 physical ++ [])) (converse0_010 physical logical agreement holds) (all_append (first := tuple0_011 physical) (rest := []) (converse0_011 physical logical agreement holds) (by intro value member; cases member)))))))))))))
  · intro values member
    change values ∈ ([] : List (List F)) at member
    cases member
  · kernel_exact (all_append (first := tuple2_000 physical) (rest := (tuple2_001 physical ++ (tuple2_002 physical ++ (tuple2_003 physical ++ (tuple2_004 physical ++ (tuple2_005 physical ++ [])))))) (converse2_000 physical logical agreement holds) (all_append (first := tuple2_001 physical) (rest := (tuple2_002 physical ++ (tuple2_003 physical ++ (tuple2_004 physical ++ (tuple2_005 physical ++ []))))) (converse2_001 physical logical agreement holds) (all_append (first := tuple2_002 physical) (rest := (tuple2_003 physical ++ (tuple2_004 physical ++ (tuple2_005 physical ++ [])))) (converse2_002 physical logical agreement holds) (all_append (first := tuple2_003 physical) (rest := (tuple2_004 physical ++ (tuple2_005 physical ++ []))) (converse2_003 physical logical agreement holds) (all_append (first := tuple2_004 physical) (rest := (tuple2_005 physical ++ [])) (converse2_004 physical logical agreement holds) (all_append (first := tuple2_005 physical) (rest := []) (converse2_005 physical logical agreement holds) (by intro value member; cases member)))))))

/-- Source lookup acceptance and actual placement construct the full native matching argument. -/
noncomputable def arguments_of_description (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    NativeLookups.Arguments (circuitFor .blakeRound) (selectorsFor .blakeRound) physical (NativeWorkerSetup.rows .blakeRound) :=
  native_arguments (family := .blakeRound) (physical := physical) (tuples physical) (binding physical) (tuples_membership physical logical agreement holds)

end Airbender.Compiler.WorkerConstraints.BlakeRound
