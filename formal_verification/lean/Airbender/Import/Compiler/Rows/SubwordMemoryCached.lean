import Airbender.Review.Compiler.RowFrame
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.SubwordMemoryCached
import Airbender.Proofs.GKRProtocol.CounterFrameNative.SubwordMemoryCached
import Airbender.Proofs.GKRProtocol.HelperValidityNative.SubwordMemoryCached
import Airbender.Proofs.GKRProtocol.MaterializedWitnessNative.SubwordMemoryCached
import Airbender.Review.Helpers.Context.Registries.Pooled

namespace Airbender.Compiler.PooledRowNative.SubwordMemoryCached
open Airbender Airbender.Compiler

abbrev Certificate :=
  RowFrame (S := Fin Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.inputs.length) (C := Fin Airbender.Compiler.TableNative.SubwordMemoryCached.native.multiplicityColumns.length)
    Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.inputBank.address
    (fun sourceValue counts => Airbender.Compiler.CounterFrameNative.SubwordMemoryCached.native.assigned (Airbender.Compiler.HelperValidityNative.SubwordMemoryCached.native.canonical sourceValue) counts)
    (fun physical => ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.gates,
    gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0)
    (fun physical => ∀ field ∈ Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields,
    (field.value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues physical)).val < 524288)
    Airbender.Compiler.MaterializedWitnessNative.SubwordMemoryCached.AuthoredLookupValid
    (fun physical => (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical (fun _ _ => #[])).get
    Airbender.SubwordMemory.importedConstraintsTraceColumns.execute = 1)

def row (cert : Certificate) : Trace.Row babyBearModulus Trace.PooledFamily :=
  ⟨.subwordMemory, (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment cert.physical (fun _ _ => #[])).get⟩

end Airbender.Compiler.PooledRowNative.SubwordMemoryCached
