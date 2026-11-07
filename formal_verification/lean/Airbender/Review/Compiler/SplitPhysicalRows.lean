import Airbender.Review.Compiler.SetupSource
import Airbender.Data.Setup.Source.ParityRLE
import Airbender.Data.Setup.Source.ThetaRLE
import Airbender.Data.Setup.Source.ChiRLE
import Airbender.Data.Setup.Keccak.ColumnParityGeneric
import Airbender.Data.Setup.Keccak.ThetaRhoPhysical
import Airbender.Data.Setup.Keccak.Chi5Generic

namespace Airbender.Compiler.MachineTargets

/-- Every decoded physical row belongs to the original canonical table. -/
def PhysicalRows {width : Nat} (columns : Array Setup.Column) (length : Nat)
    (table : Table F (fields width)) : Prop :=
  ∀ index : Fin length, table.toRaw.Contains #[]
    (Vector.ofFn fun column : Fin width =>
      (Setup.signedValue
        ((((columns[column.val]?).getD ⟨#[]⟩).get? index.val).getD 0) : F))

def SplitParityPhysicalRows : Prop :=
  ∀ [Fact babyBearModulus.Prime], PhysicalRows Setup.SourceCaptureParity.columns
    Setup.SourceCaptureParity.traceLength Keccak.Split.Native.Fixed.columnParityGenericTable

def SplitThetaPhysicalRows : Prop :=
  ∀ [Fact babyBearModulus.Prime], PhysicalRows Setup.SourceCaptureTheta.columns
    Setup.SourceCaptureTheta.traceLength Keccak.Split.Native.Fixed.thetaRhoPhysicalGenericTable

def SplitChiPhysicalRows : Prop :=
  ∀ [Fact babyBearModulus.Prime], PhysicalRows Setup.SourceCaptureChi.columns
    Setup.SourceCaptureChi.traceLength
    (Keccak.Split.Native.Fixed.chi5Generic.table "Airbender.SplitChi5Generic")

end Airbender.Compiler.MachineTargets
