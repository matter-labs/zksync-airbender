import Airbender.Proofs.GKRProtocol.CounterFrameChecks.JumpBranchUncached.Bindings

namespace Airbender.Compiler.CounterFrameChecks.JumpBranchUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericCounterFrameChecks.check 49 data = true := by decide +kernel

theorem originalChecked :
  Airbender.Compiler.TableNative.JumpBranchUncached.native.multiplicityColumns = [28, 26, 27] ∧ Function.Injective Airbender.Compiler.CounterFrameNative.JumpBranchUncached.native.slots ∧
  (∀ index, 49 ≤ (Airbender.Compiler.CounterFrameNative.JumpBranchUncached.native.slots index).val) ∧
  (∀ index, Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputBank.address (Airbender.Compiler.CounterFrameNative.JumpBranchUncached.native.slots index) =
    GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.JumpBranchUncached.native.multiplicityColumns.get index)) ∧
  Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.artifact.source.all (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.JumpBranchUncached.native.slots)) = true ∧
  (Airbender.Compiler.HelperNative.JumpBranchUncached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.helperPlacement)).all
    (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.JumpBranchUncached.native.slots)) = true :=
  NumericCounterFrameChecks.check_sound data 49 Airbender.Compiler.TableNative.JumpBranchUncached.native.multiplicityColumns [28, 26, 27] Airbender.Compiler.CounterFrameNative.JumpBranchUncached.native.slots
    Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.artifact.source
    (Airbender.Compiler.HelperNative.JumpBranchUncached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.helperPlacement)) source_binding checked

end Airbender.Compiler.CounterFrameChecks.JumpBranchUncached
