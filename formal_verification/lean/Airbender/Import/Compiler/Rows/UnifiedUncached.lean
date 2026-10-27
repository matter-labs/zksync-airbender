import Airbender.Review.Compiler.NativeRow
import Airbender.Review.Compiler.RowFrame
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.UnifiedUncached
import Airbender.Proofs.GKRProtocol.CounterFrameNative.UnifiedUncached
import Airbender.Proofs.GKRProtocol.HelperValidityNative.UnifiedUncached
import Airbender.Proofs.GKRProtocol.MaterializedWitnessNative.UnifiedUncached
import Airbender.Review.Helpers.UnifiedReduced.Registry

namespace Airbender.Compiler.UnifiedRowNative.UnifiedUncached
open Airbender Airbender.Compiler

abbrev Certificate :=
  RowFrame (S := Fin Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.inputs.length) (C := Fin Airbender.Compiler.TableNative.UnifiedUncached.native.multiplicityColumns.length)
    Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.inputBank.address
    (fun sourceValue counts => Airbender.Compiler.CounterFrameNative.UnifiedUncached.native.assigned (Airbender.Compiler.HelperValidityNative.UnifiedUncached.native.canonical sourceValue) counts)
    (fun physical => ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates,
    gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0)
    (fun physical => ∀ field ∈ Airbender.Compiler.HelperNative.UnifiedUncached.native.fields,
    (field.value (Airbender.Compiler.HelperNative.UnifiedUncached.native.sourceValues physical)).val < 524288)
    Airbender.Compiler.MaterializedWitnessNative.UnifiedUncached.AuthoredLookupValid
    (fun physical => (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical (fun _ _ => #[])).get
    Airbender.UnifiedReduced.importedConstraintsTraceColumns.execute = 1)

/-- Physical native arithmetic and the execution mask. Logical lookup matching
derives all helper ranges and retained Clean obligations without a canonical
borrow or source-assignment frame. -/
abbrev Input :=
  PhysicalRowInput
    (fun physical => ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates,
    gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0)
    (fun physical => (physicalAssignment (fun index => Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address
      (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.placement index)) physical)
    Airbender.UnifiedReduced.importedConstraintsTraceColumns.execute = 1)

def row (cert : Certificate) : Trace.Row babyBearModulus Trace.UnifiedFamily :=
  ⟨.machine, (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment cert.physical (fun _ _ => #[])).get⟩

end Airbender.Compiler.UnifiedRowNative.UnifiedUncached
