import Airbender.Review.Compiler.Pooled
import Airbender.Review.Compiler.Unified
import Airbender.Import.Compiler.LogicalRows

namespace Airbender.Compiler.PooledExecution
open Airbender Airbender.Compiler Airbender.Trace Reference.RiscV.Sail

/-- Captured native row inputs and exact physical lookup matching. Helper
ranges and authored membership are derived by the supporting composition. -/
inductive LogicalRowCertificate where
  | addSubUncached (input : PooledRowNative.AddSubUncached.Input) (arguments : PooledRowNative.AddSubUncached.LookupArguments input)
  | addSubCached (input : PooledRowNative.AddSubCached.Input) (arguments : PooledRowNative.AddSubCached.LookupArguments input)
  | jumpBranchUncached (input : PooledRowNative.JumpBranchUncached.Input) (arguments : PooledRowNative.JumpBranchUncached.LookupArguments input)
  | jumpBranchCached (input : PooledRowNative.JumpBranchCached.Input) (arguments : PooledRowNative.JumpBranchCached.LookupArguments input)
  | mulDivUncached (input : PooledRowNative.MulDivUncached.Input) (arguments : PooledRowNative.MulDivUncached.LookupArguments input)
  | mulDivCached (input : PooledRowNative.MulDivCached.Input) (arguments : PooledRowNative.MulDivCached.LookupArguments input)
  | shiftBinopUncached (input : PooledRowNative.ShiftBinopUncached.Input) (arguments : PooledRowNative.ShiftBinopUncached.LookupArguments input)
  | shiftBinopCached (input : PooledRowNative.ShiftBinopCached.Input) (arguments : PooledRowNative.ShiftBinopCached.LookupArguments input)
  | wordMemoryUncached (input : PooledRowNative.WordMemoryUncached.Input) (arguments : PooledRowNative.WordMemoryUncached.LookupArguments input)
  | wordMemoryCached (input : PooledRowNative.WordMemoryCached.Input) (arguments : PooledRowNative.WordMemoryCached.LookupArguments input)
  | subwordMemoryUncached (input : PooledRowNative.SubwordMemoryUncached.Input) (arguments : PooledRowNative.SubwordMemoryUncached.LookupArguments input)
  | subwordMemoryCached (input : PooledRowNative.SubwordMemoryCached.Input) (arguments : PooledRowNative.SubwordMemoryCached.LookupArguments input)

def LogicalRowCertificate.row : LogicalRowCertificate → Row babyBearModulus PooledFamily
  | .addSubUncached input _ => PooledRowNative.AddSubUncached.inputRow input
  | .addSubCached input _ => PooledRowNative.AddSubCached.inputRow input
  | .jumpBranchUncached input _ => PooledRowNative.JumpBranchUncached.inputRow input
  | .jumpBranchCached input _ => PooledRowNative.JumpBranchCached.inputRow input
  | .mulDivUncached input _ => PooledRowNative.MulDivUncached.inputRow input
  | .mulDivCached input _ => PooledRowNative.MulDivCached.inputRow input
  | .shiftBinopUncached input _ => PooledRowNative.ShiftBinopUncached.inputRow input
  | .shiftBinopCached input _ => PooledRowNative.ShiftBinopCached.inputRow input
  | .wordMemoryUncached input _ => PooledRowNative.WordMemoryUncached.inputRow input
  | .wordMemoryCached input _ => PooledRowNative.WordMemoryCached.inputRow input
  | .subwordMemoryUncached input _ => PooledRowNative.SubwordMemoryUncached.inputRow input
  | .subwordMemoryCached input _ => PooledRowNative.SubwordMemoryCached.inputRow input

end Airbender.Compiler.PooledExecution

namespace Airbender.Compiler.UnifiedExecution
open Airbender Airbender.Compiler Airbender.Trace Reference.RiscV.Sail

/-- Captured native row inputs and exact physical lookup matching. Helper
ranges and authored membership are derived by the supporting composition. -/
inductive LogicalRowCertificate where
  | plain (input : UnifiedRowNative.UnifiedUncached.Input) (arguments : UnifiedRowNative.UnifiedUncached.LookupArguments input)
  | preprocessed (input : UnifiedRowNative.UnifiedCached.Input) (arguments : UnifiedRowNative.UnifiedCached.LookupArguments input)

def LogicalRowCertificate.row : LogicalRowCertificate → Row babyBearModulus UnifiedFamily
  | .plain input _ => UnifiedRowNative.UnifiedUncached.inputRow input
  | .preprocessed input _ => UnifiedRowNative.UnifiedCached.inputRow input

end Airbender.Compiler.UnifiedExecution
