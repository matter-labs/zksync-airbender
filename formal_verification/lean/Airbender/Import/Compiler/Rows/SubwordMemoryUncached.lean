import Airbender.Review.Compiler.NativeRow
import Airbender.Review.Compiler.RowFrame
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.SubwordMemoryUncached
import Airbender.Proofs.GKRProtocol.CounterFrameNative.SubwordMemoryUncached
import Airbender.Proofs.GKRProtocol.HelperValidityNative.SubwordMemoryUncached
import Airbender.Proofs.GKRProtocol.MaterializedWitnessNative.SubwordMemoryUncached
import Airbender.Review.Helpers.Context.Registries.Pooled

namespace Airbender.Compiler.PooledRowNative.SubwordMemoryUncached
open Airbender Airbender.Compiler

abbrev Certificate :=
  RowFrame (S := Fin Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.inputs.length) (C := Fin Airbender.Compiler.TableNative.SubwordMemoryUncached.native.multiplicityColumns.length)
    Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.inputBank.address
    (fun sourceValue counts => Airbender.Compiler.CounterFrameNative.SubwordMemoryUncached.native.assigned (Airbender.Compiler.HelperValidityNative.SubwordMemoryUncached.native.canonical sourceValue) counts)
    (fun physical => ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.artifact.gates,
    gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.bank.address) = 0)
    (fun physical => ∀ field ∈ Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.fields,
    (field.value (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.sourceValues physical)).val < 524288)
    Airbender.Compiler.MaterializedWitnessNative.SubwordMemoryUncached.AuthoredLookupValid
    (fun physical => (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical (fun _ _ => #[])).get
    Airbender.SubwordMemory.importedConstraintsTraceColumns.execute = 1)

/-- Physical native arithmetic and the execution mask. Logical lookup matching
derives all helper ranges and retained Clean obligations without a canonical
borrow or source-assignment frame. -/
abbrev Input :=
  PhysicalRowInput
    (fun physical => ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.artifact.gates,
    gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.bank.address) = 0)
    (fun physical => (physicalAssignment (fun index => Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.bank.address
      (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.placement index)) physical)
    Airbender.SubwordMemory.importedConstraintsTraceColumns.execute = 1)

def row (cert : Certificate) : Trace.Row babyBearModulus Trace.PooledFamily :=
  ⟨.subwordMemory, (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment cert.physical (fun _ _ => #[])).get⟩

end Airbender.Compiler.PooledRowNative.SubwordMemoryUncached
