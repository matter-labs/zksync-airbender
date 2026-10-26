import Airbender.Import.Compiler.ArithmeticInstances
import Airbender.Proofs.GKRCompiler.Native.AddSubCached
import Airbender.Proofs.GKRCompiler.Native.AddSubUncached
import Airbender.Proofs.GKRCompiler.Native.BigintCached
import Airbender.Proofs.GKRCompiler.Native.BigintUncached
import Airbender.Proofs.GKRCompiler.Native.BlakeGCached
import Airbender.Proofs.GKRCompiler.Native.BlakeGUncached
import Airbender.Proofs.GKRCompiler.Native.BlakeRoundCached
import Airbender.Proofs.GKRCompiler.Native.BlakeRoundUncached
import Airbender.Proofs.GKRCompiler.Native.JumpBranchCached
import Airbender.Proofs.GKRCompiler.Native.JumpBranchUncached
import Airbender.Proofs.GKRCompiler.Native.KeccakCached
import Airbender.Proofs.GKRCompiler.Native.KeccakUncached
import Airbender.Proofs.GKRCompiler.Native.MulDivCached
import Airbender.Proofs.GKRCompiler.Native.MulDivUncached
import Airbender.Proofs.GKRCompiler.Native.ShiftBinopCached
import Airbender.Proofs.GKRCompiler.Native.ShiftBinopUncached
import Airbender.Proofs.GKRCompiler.Native.SubwordMemoryCached
import Airbender.Proofs.GKRCompiler.Native.SubwordMemoryUncached
import Airbender.Proofs.GKRCompiler.Native.UnifiedCached
import Airbender.Proofs.GKRCompiler.Native.UnifiedUncached
import Airbender.Proofs.GKRCompiler.Native.WordMemoryCached
import Airbender.Proofs.GKRCompiler.Native.WordMemoryUncached

namespace Airbender.Compiler.ArithmeticInstances

/-- All retained captures, with no extra assumption beyond native arithmetic. -/
theorem source_preserved (configuration : Configuration)
    {values : Fin (arithmeticCapture configuration).lowerVariables → Source.BaseField}
    (holds : (arithmeticCapture configuration).artifact.LoweredHolds values) :
    (arithmeticCapture configuration).artifact.SourceHolds
      (values ∘ (arithmeticCapture configuration).artifact.placement) := by
  cases configuration with
  | addSubCached => exact Native.AddSubCached.source_preserved holds
  | addSubUncached => exact Native.AddSubUncached.source_preserved holds
  | bigintCached => exact Native.BigintCached.source_preserved holds
  | bigintUncached => exact Native.BigintUncached.source_preserved holds
  | blakeGCached => exact Native.BlakeGCached.source_preserved holds
  | blakeGUncached => exact Native.BlakeGUncached.source_preserved holds
  | blakeRoundCached => exact Native.BlakeRoundCached.source_preserved holds
  | blakeRoundUncached => exact Native.BlakeRoundUncached.source_preserved holds
  | jumpBranchCached => exact Native.JumpBranchCached.source_preserved holds
  | jumpBranchUncached => exact Native.JumpBranchUncached.source_preserved holds
  | keccakCached => exact Native.KeccakCached.source_preserved holds
  | keccakUncached => exact Native.KeccakUncached.source_preserved holds
  | mulDivCached => exact Native.MulDivCached.source_preserved holds
  | mulDivUncached => exact Native.MulDivUncached.source_preserved holds
  | shiftBinopCached => exact Native.ShiftBinopCached.source_preserved holds
  | shiftBinopUncached => exact Native.ShiftBinopUncached.source_preserved holds
  | subwordMemoryCached => exact Native.SubwordMemoryCached.source_preserved holds
  | subwordMemoryUncached => exact Native.SubwordMemoryUncached.source_preserved holds
  | unifiedCached => exact Native.UnifiedCached.source_preserved holds
  | unifiedUncached => exact Native.UnifiedUncached.source_preserved holds
  | wordMemoryCached => exact Native.WordMemoryCached.source_preserved holds
  | wordMemoryUncached => exact Native.WordMemoryUncached.source_preserved holds

/-- Extension covers the selected arithmetic slice, not the complete graph. -/
theorem source_extends (configuration : Configuration)
    {values : Fin (arithmeticCapture configuration).sourceVariables → Source.BaseField}
    (holds : (arithmeticCapture configuration).artifact.SourceHolds values) :
    ∃ extended : Fin (arithmeticCapture configuration).lowerVariables → Source.BaseField,
      (∀ wire, extended ((arithmeticCapture configuration).artifact.placement wire) = values wire) ∧
      (∀ index ∈ (arithmeticCapture configuration).selected,
        ((arithmeticCapture configuration).artifact.gates.get index).expressionResidual extended = 0) := by
  cases configuration with
  | addSubCached => exact Native.AddSubCached.source_extends holds
  | addSubUncached => exact Native.AddSubUncached.source_extends holds
  | bigintCached => exact Native.BigintCached.source_extends holds
  | bigintUncached => exact Native.BigintUncached.source_extends holds
  | blakeGCached => exact Native.BlakeGCached.source_extends holds
  | blakeGUncached => exact Native.BlakeGUncached.source_extends holds
  | blakeRoundCached => exact Native.BlakeRoundCached.source_extends holds
  | blakeRoundUncached => exact Native.BlakeRoundUncached.source_extends holds
  | jumpBranchCached => exact Native.JumpBranchCached.source_extends holds
  | jumpBranchUncached => exact Native.JumpBranchUncached.source_extends holds
  | keccakCached => exact Native.KeccakCached.source_extends holds
  | keccakUncached => exact Native.KeccakUncached.source_extends holds
  | mulDivCached => exact Native.MulDivCached.source_extends holds
  | mulDivUncached => exact Native.MulDivUncached.source_extends holds
  | shiftBinopCached => exact Native.ShiftBinopCached.source_extends holds
  | shiftBinopUncached => exact Native.ShiftBinopUncached.source_extends holds
  | subwordMemoryCached => exact Native.SubwordMemoryCached.source_extends holds
  | subwordMemoryUncached => exact Native.SubwordMemoryUncached.source_extends holds
  | unifiedCached => exact Native.UnifiedCached.source_extends holds
  | unifiedUncached => exact Native.UnifiedUncached.source_extends holds
  | wordMemoryCached => exact Native.WordMemoryCached.source_extends holds
  | wordMemoryUncached => exact Native.WordMemoryUncached.source_extends holds

end Airbender.Compiler.ArithmeticInstances
