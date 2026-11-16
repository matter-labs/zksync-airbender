module
public import Proven.Compiler.WorkerConstraints.KeccakChi5.Queries001

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakChi5
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields16 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical) :
    operand16.input.fields physical = sourceFields16 logical := by
  have p66 : physical (.BaseLayerWitness 12) = logical 66 :=
    placed agreement (position := 66) (by kernel_rfl)
  have p78 : physical (.BaseLayerWitness 24) = logical 78 :=
    placed agreement (position := 78) (by kernel_rfl)
  have p90 : physical (.BaseLayerWitness 36) = logical 90 :=
    placed agreement (position := 90) (by kernel_rfl)
  have p102 : physical (.BaseLayerWitness 48) = logical 102 :=
    placed agreement (position := 102) (by kernel_rfl)
  have p114 : physical (.BaseLayerWitness 60) = logical 114 :=
    placed agreement (position := 114) (by kernel_rfl)
  have p126 : physical (.BaseLayerWitness 72) = logical 126 :=
    placed agreement (position := 126) (by kernel_rfl)
  have p138 : physical (.BaseLayerWitness 84) = logical 138 :=
    placed agreement (position := 138) (by kernel_rfl)
  have p150 : physical (.BaseLayerWitness 96) = logical 150 :=
    placed agreement (position := 150) (by kernel_rfl)
  have p162 : physical (.BaseLayerWitness 108) = logical 162 :=
    placed agreement (position := 162) (by kernel_rfl)
  have p174 : physical (.BaseLayerWitness 120) = logical 174 :=
    placed agreement (position := 174) (by kernel_rfl)
  simp only [operand16, NativeLookups.Input.fields, sourceFields16, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p66, p78, p90, p102, p114, p126, p138, p150, p162, p174]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement16 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical) :
    (sourceLookup16).Contains (Verification.environment logical) ↔
      ∃ index, operand16.input.fields physical = NativeWorkerSetup.rows .chi5 0 index := by
  rw [fields16 physical logical agreement]
  exact source_semantics16 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields17 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical) :
    operand17.input.fields physical = sourceFields17 logical := by
  have p19 : physical (.BaseLayerMemory 16) = logical 19 :=
    placed agreement (position := 19) (by kernel_rfl)
  have p64 : physical (.BaseLayerWitness 10) = logical 64 :=
    placed agreement (position := 64) (by kernel_rfl)
  have p65 : physical (.BaseLayerWitness 11) = logical 65 :=
    placed agreement (position := 65) (by kernel_rfl)
  have p66 : physical (.BaseLayerWitness 12) = logical 66 :=
    placed agreement (position := 66) (by kernel_rfl)
  have p27 : physical (.BaseLayerMemory 27) = logical 27 :=
    placed agreement (position := 27) (by kernel_rfl)
  have p76 : physical (.BaseLayerWitness 22) = logical 76 :=
    placed agreement (position := 76) (by kernel_rfl)
  have p77 : physical (.BaseLayerWitness 23) = logical 77 :=
    placed agreement (position := 77) (by kernel_rfl)
  have p78 : physical (.BaseLayerWitness 24) = logical 78 :=
    placed agreement (position := 78) (by kernel_rfl)
  have p35 : physical (.BaseLayerMemory 38) = logical 35 :=
    placed agreement (position := 35) (by kernel_rfl)
  have p88 : physical (.BaseLayerWitness 34) = logical 88 :=
    placed agreement (position := 88) (by kernel_rfl)
  have p89 : physical (.BaseLayerWitness 35) = logical 89 :=
    placed agreement (position := 89) (by kernel_rfl)
  have p90 : physical (.BaseLayerWitness 36) = logical 90 :=
    placed agreement (position := 90) (by kernel_rfl)
  have p43 : physical (.BaseLayerMemory 49) = logical 43 :=
    placed agreement (position := 43) (by kernel_rfl)
  have p100 : physical (.BaseLayerWitness 46) = logical 100 :=
    placed agreement (position := 100) (by kernel_rfl)
  have p101 : physical (.BaseLayerWitness 47) = logical 101 :=
    placed agreement (position := 101) (by kernel_rfl)
  have p102 : physical (.BaseLayerWitness 48) = logical 102 :=
    placed agreement (position := 102) (by kernel_rfl)
  have p51 : physical (.BaseLayerMemory 60) = logical 51 :=
    placed agreement (position := 51) (by kernel_rfl)
  have p112 : physical (.BaseLayerWitness 58) = logical 112 :=
    placed agreement (position := 112) (by kernel_rfl)
  have p113 : physical (.BaseLayerWitness 59) = logical 113 :=
    placed agreement (position := 113) (by kernel_rfl)
  have p114 : physical (.BaseLayerWitness 60) = logical 114 :=
    placed agreement (position := 114) (by kernel_rfl)
  have p21 : physical (.BaseLayerMemory 18) = logical 21 :=
    placed agreement (position := 21) (by kernel_rfl)
  have p124 : physical (.BaseLayerWitness 70) = logical 124 :=
    placed agreement (position := 124) (by kernel_rfl)
  have p125 : physical (.BaseLayerWitness 71) = logical 125 :=
    placed agreement (position := 125) (by kernel_rfl)
  have p126 : physical (.BaseLayerWitness 72) = logical 126 :=
    placed agreement (position := 126) (by kernel_rfl)
  have p29 : physical (.BaseLayerMemory 29) = logical 29 :=
    placed agreement (position := 29) (by kernel_rfl)
  have p136 : physical (.BaseLayerWitness 82) = logical 136 :=
    placed agreement (position := 136) (by kernel_rfl)
  have p137 : physical (.BaseLayerWitness 83) = logical 137 :=
    placed agreement (position := 137) (by kernel_rfl)
  have p138 : physical (.BaseLayerWitness 84) = logical 138 :=
    placed agreement (position := 138) (by kernel_rfl)
  have p37 : physical (.BaseLayerMemory 40) = logical 37 :=
    placed agreement (position := 37) (by kernel_rfl)
  have p148 : physical (.BaseLayerWitness 94) = logical 148 :=
    placed agreement (position := 148) (by kernel_rfl)
  have p149 : physical (.BaseLayerWitness 95) = logical 149 :=
    placed agreement (position := 149) (by kernel_rfl)
  have p150 : physical (.BaseLayerWitness 96) = logical 150 :=
    placed agreement (position := 150) (by kernel_rfl)
  have p45 : physical (.BaseLayerMemory 51) = logical 45 :=
    placed agreement (position := 45) (by kernel_rfl)
  have p160 : physical (.BaseLayerWitness 106) = logical 160 :=
    placed agreement (position := 160) (by kernel_rfl)
  have p161 : physical (.BaseLayerWitness 107) = logical 161 :=
    placed agreement (position := 161) (by kernel_rfl)
  have p162 : physical (.BaseLayerWitness 108) = logical 162 :=
    placed agreement (position := 162) (by kernel_rfl)
  have p53 : physical (.BaseLayerMemory 62) = logical 53 :=
    placed agreement (position := 53) (by kernel_rfl)
  have p172 : physical (.BaseLayerWitness 118) = logical 172 :=
    placed agreement (position := 172) (by kernel_rfl)
  have p173 : physical (.BaseLayerWitness 119) = logical 173 :=
    placed agreement (position := 173) (by kernel_rfl)
  have p174 : physical (.BaseLayerWitness 120) = logical 174 :=
    placed agreement (position := 174) (by kernel_rfl)
  simp only [operand17, NativeLookups.Input.fields, sourceFields17, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p19, p64, p65, p66, p27, p76, p77, p78, p35, p88, p89, p90, p43, p100, p101, p102, p51, p112, p113, p114, p21, p124, p125, p126, p29, p136, p137, p138, p37, p148, p149, p150, p45, p160, p161, p162, p53, p172, p173, p174]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement17 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical) :
    (sourceLookup17).Contains (Verification.environment logical) ↔
      ∃ index, operand17.input.fields physical = NativeWorkerSetup.rows .chi5 0 index := by
  rw [fields17 physical logical agreement]
  exact source_semantics17 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields18 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical) :
    operand18.input.fields physical = sourceFields18 logical := by
  have p12 : physical (.BaseLayerMemory 6) = logical 12 :=
    placed agreement (position := 12) (by kernel_rfl)
  simp only [operand18, NativeLookups.Input.fields, sourceFields18]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p12]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement18 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical) :
    (sourceLookup18).Contains (Verification.environment logical) ↔
      ∃ index, operand18.input.fields physical = NativeWorkerSetup.rows .chi5 2 index := by
  rw [fields18 physical logical agreement]
  exact source_semantics18 logical


end Airbender.Compiler.WorkerConstraints.KeccakChi5
