import Airbender.Review.Compiler.RowFrame
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.ShiftBinopCached
import Airbender.Proofs.GKRProtocol.CounterFrameNative.ShiftBinopCached
import Airbender.Proofs.GKRProtocol.HelperValidityNative.ShiftBinopCached
import Airbender.Proofs.GKRProtocol.MaterializedWitnessNative.ShiftBinopCached
import Airbender.Review.Helpers.Context.Registries.Pooled

namespace Airbender.Compiler.PooledRowNative.ShiftBinopCached
open Airbender Airbender.Compiler

abbrev Certificate :=
  RowFrame (S := Fin Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.inputs.length) (C := Fin Airbender.Compiler.TableNative.ShiftBinopCached.native.multiplicityColumns.length)
    Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.inputBank.address
    (fun sourceValue counts => Airbender.Compiler.CounterFrameNative.ShiftBinopCached.native.assigned (Airbender.Compiler.HelperValidityNative.ShiftBinopCached.native.canonical sourceValue) counts)
    (fun physical => ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.artifact.gates,
    gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0)
    (fun physical => ∀ field ∈ Airbender.Compiler.HelperNative.ShiftBinopCached.native.fields,
    (field.value (Airbender.Compiler.HelperNative.ShiftBinopCached.native.sourceValues physical)).val < 524288)
    Airbender.Compiler.MaterializedWitnessNative.ShiftBinopCached.AuthoredLookupValid
    (fun physical => (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment physical (fun _ _ => #[])).get
    Airbender.ShiftBinop.importedConstraintsTraceColumns.execute = 1)

def row (cert : Certificate) : Trace.Row babyBearModulus Trace.PooledFamily :=
  ⟨.shiftBinop, (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment cert.physical (fun _ _ => #[])).get⟩

end Airbender.Compiler.PooledRowNative.ShiftBinopCached
