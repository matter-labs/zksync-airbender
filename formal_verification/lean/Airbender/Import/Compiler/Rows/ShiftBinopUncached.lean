import Airbender.Review.Compiler.NativeRow
import Airbender.Review.Compiler.RowFrame
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.ShiftBinopUncached
import Airbender.Proofs.GKRProtocol.CounterFrameNative.ShiftBinopUncached
import Airbender.Proofs.GKRProtocol.HelperValidityNative.ShiftBinopUncached
import Airbender.Proofs.GKRProtocol.MaterializedWitnessNative.ShiftBinopUncached
import Airbender.Review.Helpers.Context.Registries.Pooled

namespace Airbender.Compiler.PooledRowNative.ShiftBinopUncached
open Airbender Airbender.Compiler

abbrev Certificate :=
  RowFrame (S := Fin Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.inputs.length) (C := Fin Airbender.Compiler.TableNative.ShiftBinopUncached.native.multiplicityColumns.length)
    Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.inputBank.address
    (fun sourceValue counts => Airbender.Compiler.CounterFrameNative.ShiftBinopUncached.native.assigned (Airbender.Compiler.HelperValidityNative.ShiftBinopUncached.native.canonical sourceValue) counts)
    (fun physical => ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.artifact.gates,
    gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank.address) = 0)
    (fun physical => ∀ field ∈ Airbender.Compiler.HelperNative.ShiftBinopUncached.native.fields,
    (field.value (Airbender.Compiler.HelperNative.ShiftBinopUncached.native.sourceValues physical)).val < 524288)
    Airbender.Compiler.MaterializedWitnessNative.ShiftBinopUncached.AuthoredLookupValid
    (fun physical => (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment physical (fun _ _ => #[])).get
    Airbender.ShiftBinop.importedConstraintsTraceColumns.execute = 1)

/-- Physical native arithmetic and the execution mask. Logical lookup matching
derives all helper ranges and retained Clean obligations without a canonical
borrow or source-assignment frame. -/
abbrev Input :=
  PhysicalRowInput
    (fun physical => ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.artifact.gates,
    gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank.address) = 0)
    (fun physical => (physicalAssignment (fun index => Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank.address
      (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement index)) physical)
    Airbender.ShiftBinop.importedConstraintsTraceColumns.execute = 1)

def row (cert : Certificate) : Trace.Row babyBearModulus Trace.PooledFamily :=
  ⟨.shiftBinop, (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment cert.physical (fun _ _ => #[])).get⟩

end Airbender.Compiler.PooledRowNative.ShiftBinopUncached
