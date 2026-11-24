module
public import Human.Compiler.WorkerPublicSetup
public import Human.Compiler.NativeSetups.Rows
public import Human.Compiler.NativeSetups.Bigint
public import Human.Compiler.NativeSetups.BlakeG

@[expose] public section
namespace Airbender.Compiler.NativeWorkerSetup
open NativeArithmetic NativeWorkerLookups

/- The import claim of the public worker tables. This module reads the raw setup data; the definitions that the
   machine claims use (`WorkerPublicSetup`) do not import the bigint and G data. -/

/-- The imported native setup of each worker. -/
noncomputable def setupData : Family → Import.Setup.SetupData
  | .bigint => NativeSetups.bigintSetup
  | .blakeG => NativeSetups.blakeGSetup
  | .blakeRound => Blake2Round.blake2RoundSetup
  | .columnParity => Keccak.Split.ColumnParity.columnParitySetup
  | .thetaRho => Keccak.Split.ThetaRho.thetaRhoSetup
  | .chi5 => Keccak.Split.Chi5.chi5Setup

/-- The public worker tables are the imported native rows on the complete trace domain, in native column and group
    order. -/
def SetupImportClaim : Prop :=
  ∀ family : Family, (setupData family).traceLen = (circuitFor family).trace_len ∧
    ∀ (group : Fin 3) (index : Fin (circuitFor family).trace_len),
      rows family group index = NativeSetups.importedRows (setupData family) group index.val

end Airbender.Compiler.NativeWorkerSetup
