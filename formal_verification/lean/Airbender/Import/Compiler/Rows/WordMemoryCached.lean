import Airbender.Review.Compiler.RowFrame
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.WordMemoryCached
import Airbender.Proofs.GKRProtocol.CounterFrameNative.WordMemoryCached
import Airbender.Proofs.GKRProtocol.HelperValidityNative.WordMemoryCached
import Airbender.Proofs.GKRProtocol.MaterializedWitnessNative.WordMemoryCached
import Airbender.Review.Helpers.Context.Registries.Pooled

namespace Airbender.Compiler.PooledRowNative.WordMemoryCached
open Airbender Airbender.Compiler

abbrev Certificate :=
  RowFrame (S := Fin Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.inputs.length) (C := Fin Airbender.Compiler.TableNative.WordMemoryCached.native.multiplicityColumns.length)
    Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.inputBank.address
    (fun sourceValue counts => Airbender.Compiler.CounterFrameNative.WordMemoryCached.native.assigned (Airbender.Compiler.HelperValidityNative.WordMemoryCached.native.canonical sourceValue) counts)
    (fun physical => ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.artifact.gates,
    gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) = 0)
    (fun physical => ∀ field ∈ Airbender.Compiler.HelperNative.WordMemoryCached.native.fields,
    (field.value (Airbender.Compiler.HelperNative.WordMemoryCached.native.sourceValues physical)).val < 524288)
    Airbender.Compiler.MaterializedWitnessNative.WordMemoryCached.AuthoredLookupValid
    (fun physical => (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical (fun _ _ => #[])).get
    Airbender.WordMemory.importedConstraintsTraceColumns.execute = 1)

def row (cert : Certificate) : Trace.Row babyBearModulus Trace.PooledFamily :=
  ⟨.wordMemory, (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment cert.physical (fun _ _ => #[])).get⟩

end Airbender.Compiler.PooledRowNative.WordMemoryCached
