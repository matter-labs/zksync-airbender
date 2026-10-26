import Airbender.Review.Compiler.RowFrame
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.AddSubCached
import Airbender.Proofs.GKRProtocol.CounterFrameNative.AddSubCached
import Airbender.Proofs.GKRProtocol.HelperValidityNative.AddSubCached
import Airbender.Proofs.GKRProtocol.MaterializedWitnessNative.AddSubCached
import Airbender.Review.Helpers.Context.Registries.Pooled

namespace Airbender.Compiler.PooledRowNative.AddSubCached
open Airbender Airbender.Compiler

abbrev Certificate :=
  RowFrame (S := Fin Airbender.Compiler.FullArithmeticNative.AddSubCached.native.inputs.length) (C := Fin Airbender.Compiler.TableNative.AddSubCached.native.multiplicityColumns.length)
    Airbender.Compiler.FullArithmeticNative.AddSubCached.native.inputBank.address
    (fun sourceValue counts => Airbender.Compiler.CounterFrameNative.AddSubCached.native.assigned (Airbender.Compiler.HelperValidityNative.AddSubCached.native.canonical sourceValue) counts)
    (fun physical => ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates,
    gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0)
    (fun physical => ∀ field ∈ Airbender.Compiler.HelperNative.AddSubCached.native.fields,
    (field.value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues physical)).val < 524288)
    Airbender.Compiler.MaterializedWitnessNative.AddSubCached.AuthoredLookupValid
    (fun physical => (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical (fun _ _ => #[])).get
    Airbender.AddSub.importedConstraintsTraceColumns.execute = 1)

def row (cert : Certificate) : Trace.Row babyBearModulus Trace.PooledFamily :=
  ⟨.addSub, (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment cert.physical (fun _ _ => #[])).get⟩

end Airbender.Compiler.PooledRowNative.AddSubCached
