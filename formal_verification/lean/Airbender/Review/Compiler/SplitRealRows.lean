import Airbender.Review.Compiler.SplitPhysicalRows

namespace Airbender.Compiler.MachineTargets

/-- Canonical membership for the real rows of the parsed source.
The original parse, column shape and complete row values stay explicit. -/
def SetupRowsBelow (source : String) (table : Table F (fields width)) (limit : Nat) : Prop :=
  ∀ artifact : Setup.Artifact,
    Setup.parse source = .ok artifact → artifact.columns.size = width →
    ∀ (row : Vector F width) (index : Fin artifact.trace_len), index.val < limit →
      (∀ column : Fin width,
        row[column] = (Setup.signedValue
          ((((artifact.columns[column.val]?).getD ⟨#[]⟩).get? index.val).getD 0) : F)) →
      table.toRaw.Contains #[] row

def SplitParityRealRows : Prop :=
  ∀ [Fact babyBearModulus.Prime], SetupRowsBelow Setup.SourceCaptureParity.source
    Keccak.Split.Native.Fixed.columnParityGenericTable 1114356

def SplitThetaRealRows : Prop :=
  ∀ [Fact babyBearModulus.Prime], SetupRowsBelow Setup.SourceCaptureTheta.source
    Keccak.Split.Native.Fixed.thetaRhoPhysicalGenericTable 590066

def SplitChiRealRows : Prop :=
  ∀ [Fact babyBearModulus.Prime], SetupRowsBelow Setup.SourceCaptureChi.source
    (Keccak.Split.Native.Fixed.chi5Generic.table "Airbender.SplitChi5Generic") 1048697

end Airbender.Compiler.MachineTargets
