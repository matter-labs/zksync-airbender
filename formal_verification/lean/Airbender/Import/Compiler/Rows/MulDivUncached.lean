import Airbender.Review.Compiler.RowFrame
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.MulDivUncached
import Airbender.Proofs.GKRProtocol.CounterFrameNative.MulDivUncached
import Airbender.Proofs.GKRProtocol.HelperValidityNative.MulDivUncached
import Airbender.Proofs.GKRProtocol.MaterializedWitnessNative.MulDivUncached
import Airbender.Review.Helpers.Context.Registries.Pooled

namespace Airbender.Compiler.PooledRowNative.MulDivUncached
open Airbender Airbender.Compiler

abbrev Certificate :=
  RowFrame (S := Fin Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.inputs.length) (C := Fin Airbender.Compiler.TableNative.MulDivUncached.native.multiplicityColumns.length)
    Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.inputBank.address
    (fun sourceValue counts => Airbender.Compiler.CounterFrameNative.MulDivUncached.native.assigned (Airbender.Compiler.HelperValidityNative.MulDivUncached.native.canonical sourceValue) counts)
    (fun physical => ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.artifact.gates,
    gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.bank.address) = 0)
    (fun physical => ∀ field ∈ Airbender.Compiler.HelperNative.MulDivUncached.native.fields,
    (field.value (Airbender.Compiler.HelperNative.MulDivUncached.native.sourceValues physical)).val < 524288)
    Airbender.Compiler.MaterializedWitnessNative.MulDivUncached.AuthoredLookupValid
    (fun physical => (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment physical (fun _ _ => #[])).get
    Airbender.MulDiv.importedConstraintsTraceColumns.execute = 1)

def row (cert : Certificate) : Trace.Row babyBearModulus Trace.PooledFamily :=
  ⟨.mulDiv, (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment cert.physical (fun _ _ => #[])).get⟩

end Airbender.Compiler.PooledRowNative.MulDivUncached
