import Airbender.Review.Compiler.NativeRow
import Airbender.Review.Compiler.RowFrame
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.WordMemoryUncached
import Airbender.Proofs.GKRProtocol.CounterFrameNative.WordMemoryUncached
import Airbender.Proofs.GKRProtocol.HelperValidityNative.WordMemoryUncached
import Airbender.Proofs.GKRProtocol.MaterializedWitnessNative.WordMemoryUncached
import Airbender.Review.Helpers.Context.Registries.Pooled

namespace Airbender.Compiler.PooledRowNative.WordMemoryUncached
open Airbender Airbender.Compiler

abbrev Certificate :=
  RowFrame (S := Fin Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.inputs.length) (C := Fin Airbender.Compiler.TableNative.WordMemoryUncached.native.multiplicityColumns.length)
    Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.inputBank.address
    (fun sourceValue counts => Airbender.Compiler.CounterFrameNative.WordMemoryUncached.native.assigned (Airbender.Compiler.HelperValidityNative.WordMemoryUncached.native.canonical sourceValue) counts)
    (fun physical => ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.artifact.gates,
    gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank.address) = 0)
    (fun physical => ∀ field ∈ Airbender.Compiler.HelperNative.WordMemoryUncached.native.fields,
    (field.value (Airbender.Compiler.HelperNative.WordMemoryUncached.native.sourceValues physical)).val < 524288)
    Airbender.Compiler.MaterializedWitnessNative.WordMemoryUncached.AuthoredLookupValid
    (fun physical => (Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.environment physical (fun _ _ => #[])).get
    Airbender.WordMemory.importedConstraintsTraceColumns.execute = 1)

/-- Physical native arithmetic and the execution mask. Logical lookup matching
derives all helper ranges and retained Clean obligations without a canonical
borrow or source-assignment frame. -/
abbrev Input :=
  PhysicalRowInput
    (fun physical => ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.artifact.gates,
    gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank.address) = 0)
    (fun physical => (physicalAssignment (fun index => Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank.address
      (Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.placement index)) physical)
    Airbender.WordMemory.importedConstraintsTraceColumns.execute = 1)

def row (cert : Certificate) : Trace.Row babyBearModulus Trace.PooledFamily :=
  ⟨.wordMemory, (Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.environment cert.physical (fun _ _ => #[])).get⟩

end Airbender.Compiler.PooledRowNative.WordMemoryUncached
