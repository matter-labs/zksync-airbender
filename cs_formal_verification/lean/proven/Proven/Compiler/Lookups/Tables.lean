module
public import Proven.Compiler.Lookups.Tables.AddSub
public import Proven.Compiler.Lookups.Tables.JumpBranch
public import Proven.Compiler.Lookups.Tables.MulDiv
public import Proven.Compiler.Lookups.Tables.ShiftBinop
public import Proven.Compiler.Lookups.Tables.WordMemory
public import Proven.Compiler.Lookups.Tables.SubwordMemory
public import Proven.Compiler.Lookups.Tables.Unified
public import Proven.Compiler.Lookups.Tables.Bigint
public import Proven.Compiler.Lookups.Tables.BlakeG
public import Proven.Compiler.Lookups.Tables.BlakeRound
public import Proven.Compiler.Lookups.Tables.KeccakColumnParity
public import Proven.Compiler.Lookups.Tables.KeccakThetaRho
public import Proven.Compiler.Lookups.Tables.KeccakChi5

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler

/-- Each cached CPU capture reads its declared setup columns on the table side. -/
theorem NativeLookups.Proofs.Tables.cpu :
    ∀ family, NativeLookups.TableSidesRead (NativeLookups.circuitFor family)
  | .pooled .addSub => NativeLookups.Proofs.AddSub.tables
  | .pooled .jumpBranchSlt => NativeLookups.Proofs.JumpBranch.tables
  | .pooled .mulDiv => NativeLookups.Proofs.MulDiv.tables
  | .pooled .shiftBinop => NativeLookups.Proofs.ShiftBinop.tables
  | .pooled .wordMemory => NativeLookups.Proofs.WordMemory.tables
  | .pooled .subwordMemory => NativeLookups.Proofs.SubwordMemory.tables
  | .unified => NativeLookups.Proofs.Unified.tables

/-- Each cached worker capture reads its declared setup columns on the table side. -/
theorem NativeWorkerLookups.Proofs.tables :
    ∀ family, NativeLookups.TableSidesRead (NativeWorkerLookups.circuitFor family)
  | .bigint => NativeWorkerLookups.Proofs.Bigint.tables
  | .blakeG => NativeWorkerLookups.Proofs.BlakeG.tables
  | .blakeRound => NativeWorkerLookups.Proofs.BlakeRound.tables
  | .columnParity => NativeWorkerLookups.Proofs.KeccakColumnParity.tables
  | .thetaRho => NativeWorkerLookups.Proofs.KeccakThetaRho.tables
  | .chi5 => NativeWorkerLookups.Proofs.KeccakChi5.tables

end Airbender.Compiler
