module
public import Human.Compiler.WorkerLookups
public import Human.Circuits.Bigint.Tables.Setup
public import Human.Circuits.Blake2G.Tables.Controller
public import Human.Circuits.Blake2Round.Tables.Setup
public import Human.Circuits.KeccakSplit.Tables.Setup
public import Human.Compiler.NativeSetups.Rows

@[expose] public section
namespace Airbender.Compiler.NativeWorkerSetup
open NativeArithmetic NativeWorkerLookups

/-- Generic worker tables retain the native fixed regions and their zero padding. -/
noncomputable def genericRow (family : Family) (index : Nat) : List F :=
  match family with
  | .bigint =>
      if bound : index < 1390592 then
        let row := Bigint.setupRow ⟨index, bound⟩
        [(row.1 : F), (row.2.1 : F), (row.2.2 : F)]
      else List.replicate 3 0
  | .blakeG =>
      if bound : index < 344896 then
        ((Blake2G.setupRow Blake2G.Control.controllerRows ⟨index, bound⟩).toList).map (fun (n : Nat) => (n : F))
      else List.replicate 9 0
  | .blakeRound => (Blake2Round.setupRow index).toList.map (fun (n : Int) => (n : F))
  | .columnParity =>
      (Keccak.Split.setupRow Keccak.Split.ColumnParity.columnParitySetup 8 index).toList.map (fun (n : Int) => (n : F))
  | .thetaRho =>
      (Keccak.Split.setupRow Keccak.Split.ThetaRho.thetaRhoSetup 9 index).toList.map (fun (n : Int) => (n : F))
  | .chi5 =>
      (Keccak.Split.setupRow Keccak.Split.Chi5.chi5Setup 11 index).toList.map (fun (n : Int) => (n : F))

/-- The three public worker tables are generic tuples, 16-bit values and timestamp values. -/
noncomputable def rows (family : Family) : Fin 3 → Fin (circuitFor family).trace_len → List F :=
  fun group index =>
    if group.val = 0 then genericRow family index.val
    else if group.val = 1 then [if index.val < 65536 then (index.val : F) else 0]
    else [if index.val < 524288 then (index.val : F) else 0]

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
