import Airbender.Review.Compiler.Arithmetic
import Airbender.Review.Compiler.LogicalRows

namespace Airbender.Compiler

/-- Setup row parameters for each native configuration and lookup group.
The public boundary binds these parameters to program and fixed setup data. -/
abbrev ProgramLookupRows := Configuration → Fin 3 → Nat → List Source.BaseField

namespace PooledExecution

/-- Physical native inputs and exact lookup matching against setup parameters.
Each constructor selects its actual circuit and cache configuration. -/
inductive ProgramLogicalRowCertificate (tables : ProgramLookupRows) where
  | addSubUncached (input : PooledRowNative.AddSubUncached.Input)
      (arguments : PooledRowNative.AddSubUncached.LookupArgumentsWith
        (fun group index => tables .addSubUncached group index.val) input)
  | addSubCached (input : PooledRowNative.AddSubCached.Input)
      (arguments : PooledRowNative.AddSubCached.LookupArgumentsWith
        (fun group index => tables .addSubCached group index.val) input)
  | jumpBranchUncached (input : PooledRowNative.JumpBranchUncached.Input)
      (arguments : PooledRowNative.JumpBranchUncached.LookupArgumentsWith
        (fun group index => tables .jumpBranchUncached group index.val) input)
  | jumpBranchCached (input : PooledRowNative.JumpBranchCached.Input)
      (arguments : PooledRowNative.JumpBranchCached.LookupArgumentsWith
        (fun group index => tables .jumpBranchCached group index.val) input)
  | mulDivUncached (input : PooledRowNative.MulDivUncached.Input)
      (arguments : PooledRowNative.MulDivUncached.LookupArgumentsWith
        (fun group index => tables .mulDivUncached group index.val) input)
  | mulDivCached (input : PooledRowNative.MulDivCached.Input)
      (arguments : PooledRowNative.MulDivCached.LookupArgumentsWith
        (fun group index => tables .mulDivCached group index.val) input)
  | shiftBinopUncached (input : PooledRowNative.ShiftBinopUncached.Input)
      (arguments : PooledRowNative.ShiftBinopUncached.LookupArgumentsWith
        (fun group index => tables .shiftBinopUncached group index.val) input)
  | shiftBinopCached (input : PooledRowNative.ShiftBinopCached.Input)
      (arguments : PooledRowNative.ShiftBinopCached.LookupArgumentsWith
        (fun group index => tables .shiftBinopCached group index.val) input)
  | wordMemoryUncached (input : PooledRowNative.WordMemoryUncached.Input)
      (arguments : PooledRowNative.WordMemoryUncached.LookupArgumentsWith
        (fun group index => tables .wordMemoryUncached group index.val) input)
  | wordMemoryCached (input : PooledRowNative.WordMemoryCached.Input)
      (arguments : PooledRowNative.WordMemoryCached.LookupArgumentsWith
        (fun group index => tables .wordMemoryCached group index.val) input)
  | subwordMemoryUncached (input : PooledRowNative.SubwordMemoryUncached.Input)
      (arguments : PooledRowNative.SubwordMemoryUncached.LookupArgumentsWith
        (fun group index => tables .subwordMemoryUncached group index.val) input)
  | subwordMemoryCached (input : PooledRowNative.SubwordMemoryCached.Input)
      (arguments : PooledRowNative.SubwordMemoryCached.LookupArgumentsWith
        (fun group index => tables .subwordMemoryCached group index.val) input)

def ProgramLogicalRowCertificate.row {tables : ProgramLookupRows} :
    ProgramLogicalRowCertificate tables → Trace.Row babyBearModulus Trace.PooledFamily
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

end PooledExecution

namespace UnifiedExecution

/-- Physical native inputs and exact lookup matching against setup parameters.
Each constructor selects its actual circuit and cache configuration. -/
inductive ProgramLogicalRowCertificate (tables : ProgramLookupRows) where
  | unifiedUncached (input : UnifiedRowNative.UnifiedUncached.Input)
      (arguments : UnifiedRowNative.UnifiedUncached.LookupArgumentsWith
        (fun group index => tables .unifiedUncached group index.val) input)
  | unifiedCached (input : UnifiedRowNative.UnifiedCached.Input)
      (arguments : UnifiedRowNative.UnifiedCached.LookupArgumentsWith
        (fun group index => tables .unifiedCached group index.val) input)

def ProgramLogicalRowCertificate.row {tables : ProgramLookupRows} :
    ProgramLogicalRowCertificate tables → Trace.Row babyBearModulus Trace.UnifiedFamily
  | .unifiedUncached input _ => UnifiedRowNative.UnifiedUncached.inputRow input
  | .unifiedCached input _ => UnifiedRowNative.UnifiedCached.inputRow input

end UnifiedExecution

end Airbender.Compiler
