import Airbender.Review.Compiler.RowFrame
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.JumpBranchCached
import Airbender.Proofs.GKRProtocol.CounterFrameNative.JumpBranchCached
import Airbender.Proofs.GKRProtocol.HelperValidityNative.JumpBranchCached
import Airbender.Proofs.GKRProtocol.MaterializedWitnessNative.JumpBranchCached
import Airbender.Review.Helpers.Context.Registries.Pooled

namespace Airbender.Compiler.PooledRowNative.JumpBranchCached
open Airbender Airbender.Compiler

abbrev Certificate :=
  RowFrame (S := Fin Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.inputs.length) (C := Fin Airbender.Compiler.TableNative.JumpBranchCached.native.multiplicityColumns.length)
    Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.inputBank.address
    (fun sourceValue counts => Airbender.Compiler.CounterFrameNative.JumpBranchCached.native.assigned (Airbender.Compiler.HelperValidityNative.JumpBranchCached.native.canonical sourceValue) counts)
    (fun physical => ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.artifact.gates,
    gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address) = 0)
    (fun physical => ∀ field ∈ Airbender.Compiler.HelperNative.JumpBranchCached.native.fields,
    (field.value (Airbender.Compiler.HelperNative.JumpBranchCached.native.sourceValues physical)).val < 524288)
    Airbender.Compiler.MaterializedWitnessNative.JumpBranchCached.AuthoredLookupValid
    (fun physical => (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment physical (fun _ _ => #[])).get
    Airbender.JumpBranchSlt.importedConstraintsTraceColumns.execute = 1)

def row (cert : Certificate) : Trace.Row babyBearModulus Trace.PooledFamily :=
  ⟨.jumpBranchSlt, (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment cert.physical (fun _ _ => #[])).get⟩

end Airbender.Compiler.PooledRowNative.JumpBranchCached
