module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries023

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields280 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand280.input.fields physical = sourceFields280 logical := by
  have p100 : physical (.BaseLayerMemory 147) = logical 100 :=
    placed agreement (position := 100) (by kernel_rfl)
  have p441 : physical (.BaseLayerWitness 302) = logical 441 :=
    placed agreement (position := 441) (by kernel_rfl)
  have p628 : physical (.BaseLayerWitness 489) = logical 628 :=
    placed agreement (position := 628) (by kernel_rfl)
  have p629 : physical (.BaseLayerWitness 490) = logical 629 :=
    placed agreement (position := 629) (by kernel_rfl)
  have p631 : physical (.BaseLayerWitness 492) = logical 631 :=
    placed agreement (position := 631) (by kernel_rfl)
  simp only [operand280, NativeLookups.Input.fields, sourceFields280, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p100, p441, p628, p629, p631]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement280 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup280).Contains (Verification.environment logical) ↔
      ∃ index, operand280.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields280 physical logical agreement]
  exact source_semantics280 logical


end Airbender.Compiler.WorkerConstraints.BlakeRound
