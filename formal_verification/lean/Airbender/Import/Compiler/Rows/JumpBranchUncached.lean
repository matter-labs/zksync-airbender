import Airbender.Review.Compiler.RowFrame
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.JumpBranchUncached
import Airbender.Proofs.GKRProtocol.CounterFrameNative.JumpBranchUncached
import Airbender.Proofs.GKRProtocol.HelperValidityNative.JumpBranchUncached
import Airbender.Proofs.GKRProtocol.MaterializedWitnessNative.JumpBranchUncached
import Airbender.Review.Helpers.Context.Registries.Pooled

namespace Airbender.Compiler.PooledRowNative.JumpBranchUncached
open Airbender Airbender.Compiler

abbrev Certificate :=
  RowFrame (S := Fin Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputs.length) (C := Fin Airbender.Compiler.TableNative.JumpBranchUncached.native.multiplicityColumns.length)
    Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputBank.address
    (fun sourceValue counts => Airbender.Compiler.CounterFrameNative.JumpBranchUncached.native.assigned (Airbender.Compiler.HelperValidityNative.JumpBranchUncached.native.canonical sourceValue) counts)
    (fun physical => ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.artifact.gates,
    gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.bank.address) = 0)
    (fun physical => ∀ field ∈ Airbender.Compiler.HelperNative.JumpBranchUncached.native.fields,
    (field.value (Airbender.Compiler.HelperNative.JumpBranchUncached.native.sourceValues physical)).val < 524288)
    Airbender.Compiler.MaterializedWitnessNative.JumpBranchUncached.AuthoredLookupValid
    (fun physical => (Airbender.Compiler.CleanArithmeticNative.JumpBranchUncached.native.environment physical (fun _ _ => #[])).get
    Airbender.JumpBranchSlt.importedConstraintsTraceColumns.execute = 1)

def row (cert : Certificate) : Trace.Row babyBearModulus Trace.PooledFamily :=
  ⟨.jumpBranchSlt, (Airbender.Compiler.CleanArithmeticNative.JumpBranchUncached.native.environment cert.physical (fun _ _ => #[])).get⟩

end Airbender.Compiler.PooledRowNative.JumpBranchUncached
