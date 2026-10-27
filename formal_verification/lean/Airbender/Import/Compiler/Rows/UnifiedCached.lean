import Airbender.Review.Compiler.NativeRow
import Airbender.Review.Compiler.RowFrame
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.UnifiedCached
import Airbender.Proofs.GKRProtocol.CounterFrameNative.UnifiedCached
import Airbender.Proofs.GKRProtocol.HelperValidityNative.UnifiedCached
import Airbender.Proofs.GKRProtocol.MaterializedWitnessNative.UnifiedCached
import Airbender.Review.Helpers.UnifiedReduced.Registry

namespace Airbender.Compiler.UnifiedRowNative.UnifiedCached
open Airbender Airbender.Compiler

abbrev Certificate :=
  RowFrame (S := Fin Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputs.length) (C := Fin Airbender.Compiler.TableNative.UnifiedCached.native.multiplicityColumns.length)
    Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank.address
    (fun sourceValue counts => Airbender.Compiler.CounterFrameNative.UnifiedCached.native.assigned (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.canonical sourceValue) counts)
    (fun physical => ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates,
    gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0)
    (fun physical => ∀ field ∈ Airbender.Compiler.HelperNative.UnifiedCached.native.fields,
    (field.value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues physical)).val < 524288)
    Airbender.Compiler.MaterializedWitnessNative.UnifiedCached.AuthoredLookupValid
    (fun physical => (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical (fun _ _ => #[])).get
    Airbender.UnifiedReduced.importedConstraintsTraceColumns.execute = 1)

/-- Physical native arithmetic and the execution mask. Logical lookup matching
derives all helper ranges and retained Clean obligations without a canonical
borrow or source-assignment frame. -/
abbrev Input :=
  PhysicalRowInput
    (fun physical => ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates,
    gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0)
    (fun physical => (physicalAssignment (fun index => Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address
      (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.placement index)) physical)
    Airbender.UnifiedReduced.importedConstraintsTraceColumns.execute = 1)

def row (cert : Certificate) : Trace.Row babyBearModulus Trace.UnifiedFamily :=
  ⟨.machine, (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment cert.physical (fun _ _ => #[])).get⟩

end Airbender.Compiler.UnifiedRowNative.UnifiedCached
