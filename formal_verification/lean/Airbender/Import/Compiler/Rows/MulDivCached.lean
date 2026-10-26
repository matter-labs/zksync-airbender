import Airbender.Review.Compiler.RowFrame
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.MulDivCached
import Airbender.Proofs.GKRProtocol.CounterFrameNative.MulDivCached
import Airbender.Proofs.GKRProtocol.HelperValidityNative.MulDivCached
import Airbender.Proofs.GKRProtocol.MaterializedWitnessNative.MulDivCached
import Airbender.Review.Helpers.Context.Registries.Pooled

namespace Airbender.Compiler.PooledRowNative.MulDivCached
open Airbender Airbender.Compiler

abbrev Certificate :=
  RowFrame (S := Fin Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputs.length) (C := Fin Airbender.Compiler.TableNative.MulDivCached.native.multiplicityColumns.length)
    Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputBank.address
    (fun sourceValue counts => Airbender.Compiler.CounterFrameNative.MulDivCached.native.assigned (Airbender.Compiler.HelperValidityNative.MulDivCached.native.canonical sourceValue) counts)
    (fun physical => ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates,
    gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0)
    (fun physical => ∀ field ∈ Airbender.Compiler.HelperNative.MulDivCached.native.fields,
    (field.value (Airbender.Compiler.HelperNative.MulDivCached.native.sourceValues physical)).val < 524288)
    Airbender.Compiler.MaterializedWitnessNative.MulDivCached.AuthoredLookupValid
    (fun physical => (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical (fun _ _ => #[])).get
    Airbender.MulDiv.importedConstraintsTraceColumns.execute = 1)

def row (cert : Certificate) : Trace.Row babyBearModulus Trace.PooledFamily :=
  ⟨.mulDiv, (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment cert.physical (fun _ _ => #[])).get⟩

end Airbender.Compiler.PooledRowNative.MulDivCached
