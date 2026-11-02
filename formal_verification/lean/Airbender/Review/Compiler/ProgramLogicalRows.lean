import Airbender.Review.Compiler.Arithmetic
import Airbender.Import.Compiler.LogicalRows

namespace Airbender.Compiler

/-- Setup row parameters for each native configuration and lookup group.
The public boundary binds these parameters to program and fixed setup data. -/
abbrev ProgramLookupRows := Configuration → Fin 3 → Nat → List Source.BaseField

namespace PooledExecution

/-- Physical native inputs and exact lookup matching against setup parameters.
Each constructor selects its actual circuit and cache configuration. -/
inductive ProgramLogicalRowCertificate (tables : ProgramLookupRows) where
  | addSubCached (input : PooledRowNative.AddSubCached.Input)
      (arguments : PooledRowNative.AddSubCached.LookupArgumentsWith
        (fun group index => tables .addSubCached group index.val) input)
  | jumpBranchCached (input : PooledRowNative.JumpBranchCached.Input)
      (arguments : PooledRowNative.JumpBranchCached.LookupArgumentsWith
        (fun group index => tables .jumpBranchCached group index.val) input)
  | mulDivCached (input : PooledRowNative.MulDivCached.Input)
      (arguments : PooledRowNative.MulDivCached.LookupArgumentsWith
        (fun group index => tables .mulDivCached group index.val) input)
  | shiftBinopCached (input : PooledRowNative.ShiftBinopCached.Input)
      (arguments : PooledRowNative.ShiftBinopCached.LookupArgumentsWith
        (fun group index => tables .shiftBinopCached group index.val) input)
  | wordMemoryCached (input : PooledRowNative.WordMemoryCached.Input)
      (arguments : PooledRowNative.WordMemoryCached.LookupArgumentsWith
        (fun group index => tables .wordMemoryCached group index.val) input)
  | subwordMemoryCached (input : PooledRowNative.SubwordMemoryCached.Input)
      (arguments : PooledRowNative.SubwordMemoryCached.LookupArgumentsWith
        (fun group index => tables .subwordMemoryCached group index.val) input)

def ProgramLogicalRowCertificate.row {tables : ProgramLookupRows} :
    ProgramLogicalRowCertificate tables → Trace.Row babyBearModulus Trace.PooledFamily
  | .addSubCached input _ => PooledRowNative.AddSubCached.inputRow input
  | .jumpBranchCached input _ => PooledRowNative.JumpBranchCached.inputRow input
  | .mulDivCached input _ => PooledRowNative.MulDivCached.inputRow input
  | .shiftBinopCached input _ => PooledRowNative.ShiftBinopCached.inputRow input
  | .wordMemoryCached input _ => PooledRowNative.WordMemoryCached.inputRow input
  | .subwordMemoryCached input _ => PooledRowNative.SubwordMemoryCached.inputRow input

def ProgramLogicalRowCertificate.configuration {tables : ProgramLookupRows} :
    ProgramLogicalRowCertificate tables → Configuration
  | .addSubCached _ _ => .addSubCached
  | .jumpBranchCached _ _ => .jumpBranchCached
  | .mulDivCached _ _ => .mulDivCached
  | .shiftBinopCached _ _ => .shiftBinopCached
  | .wordMemoryCached _ _ => .wordMemoryCached
  | .subwordMemoryCached _ _ => .subwordMemoryCached

def ProgramLogicalRowCertificate.lookupLength {tables : ProgramLookupRows} :
    ProgramLogicalRowCertificate tables → Nat
  | .addSubCached _ _ => Airbender.Compiler.MaterializedNative.AddSubCached.native.model.imported.data.length
  | .jumpBranchCached _ _ => Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.imported.data.length
  | .mulDivCached _ _ => Airbender.Compiler.MaterializedNative.MulDivCached.native.model.imported.data.length
  | .shiftBinopCached _ _ => Airbender.Compiler.MaterializedNative.ShiftBinopCached.native.model.imported.data.length
  | .wordMemoryCached _ _ => Airbender.Compiler.MaterializedNative.WordMemoryCached.native.model.imported.data.length
  | .subwordMemoryCached _ _ => Airbender.Compiler.MaterializedNative.SubwordMemoryCached.native.model.imported.data.length

/-- Source tuples projected from the actual native input coordinates. -/
noncomputable def ProgramLogicalRowCertificate.sourceRequests {tables : ProgramLookupRows}
    (cert : ProgramLogicalRowCertificate tables) (group : Fin 3) : List MaterializedQuery :=
  match cert with
  | .addSubCached input _ => PooledRowNative.AddSubCached.physicalRequests input group
  | .jumpBranchCached input _ => PooledRowNative.JumpBranchCached.physicalRequests input group
  | .mulDivCached input _ => PooledRowNative.MulDivCached.physicalRequests input group
  | .shiftBinopCached input _ => PooledRowNative.ShiftBinopCached.physicalRequests input group
  | .wordMemoryCached input _ => PooledRowNative.WordMemoryCached.physicalRequests input group
  | .subwordMemoryCached input _ => PooledRowNative.SubwordMemoryCached.physicalRequests input group

end PooledExecution

namespace UnifiedExecution

/-- Physical native inputs and exact lookup matching against setup parameters.
Each constructor selects its actual circuit and cache configuration. -/
inductive ProgramLogicalRowCertificate (tables : ProgramLookupRows) where
  | unifiedCached (input : UnifiedRowNative.UnifiedCached.Input)
      (arguments : UnifiedRowNative.UnifiedCached.LookupArgumentsWith
        (fun group index => tables .unifiedCached group index.val) input)

def ProgramLogicalRowCertificate.row {tables : ProgramLookupRows} :
    ProgramLogicalRowCertificate tables → Trace.Row babyBearModulus Trace.UnifiedFamily
  | .unifiedCached input _ => UnifiedRowNative.UnifiedCached.inputRow input

def ProgramLogicalRowCertificate.configuration {tables : ProgramLookupRows} :
    ProgramLogicalRowCertificate tables → Configuration
  | .unifiedCached _ _ => .unifiedCached

def ProgramLogicalRowCertificate.lookupLength {tables : ProgramLookupRows} :
    ProgramLogicalRowCertificate tables → Nat
  | .unifiedCached _ _ => Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.imported.data.length

/-- Source tuples projected from the actual native input coordinates. -/
noncomputable def ProgramLogicalRowCertificate.sourceRequests {tables : ProgramLookupRows}
    (cert : ProgramLogicalRowCertificate tables) (group : Fin 3) : List MaterializedQuery :=
  match cert with
  | .unifiedCached input _ => UnifiedRowNative.UnifiedCached.physicalRequests input group

end UnifiedExecution

end Airbender.Compiler
