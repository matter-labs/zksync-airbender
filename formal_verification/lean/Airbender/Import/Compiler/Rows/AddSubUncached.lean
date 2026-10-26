import Airbender.Review.Compiler.RowFrame
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.AddSubUncached
import Airbender.Proofs.GKRProtocol.CounterFrameNative.AddSubUncached
import Airbender.Proofs.GKRProtocol.HelperValidityNative.AddSubUncached
import Airbender.Proofs.GKRProtocol.MaterializedWitnessNative.AddSubUncached
import Airbender.Review.Helpers.Context.Registries.Pooled

namespace Airbender.Compiler.PooledRowNative.AddSubUncached
open Airbender Airbender.Compiler

abbrev Certificate :=
  RowFrame (S := Fin Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.inputs.length) (C := Fin Airbender.Compiler.TableNative.AddSubUncached.native.multiplicityColumns.length)
    Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.inputBank.address
    (fun sourceValue counts => Airbender.Compiler.CounterFrameNative.AddSubUncached.native.assigned (Airbender.Compiler.HelperValidityNative.AddSubUncached.native.canonical sourceValue) counts)
    (fun physical => ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.artifact.gates,
    gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank.address) = 0)
    (fun physical => ∀ field ∈ Airbender.Compiler.HelperNative.AddSubUncached.native.fields,
    (field.value (Airbender.Compiler.HelperNative.AddSubUncached.native.sourceValues physical)).val < 524288)
    Airbender.Compiler.MaterializedWitnessNative.AddSubUncached.AuthoredLookupValid
    (fun physical => (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment physical (fun _ _ => #[])).get
    Airbender.AddSub.importedConstraintsTraceColumns.execute = 1)

def row (cert : Certificate) : Trace.Row babyBearModulus Trace.PooledFamily :=
  ⟨.addSub, (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment cert.physical (fun _ _ => #[])).get⟩

end Airbender.Compiler.PooledRowNative.AddSubUncached
