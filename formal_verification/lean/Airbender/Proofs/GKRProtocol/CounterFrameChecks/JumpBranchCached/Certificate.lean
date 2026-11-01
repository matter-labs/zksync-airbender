import Airbender.Proofs.GKRProtocol.CounterFrameChecks.JumpBranchCached.Bindings

namespace Airbender.Compiler.CounterFrameChecks.JumpBranchCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericCounterFrameChecks.check 49 data = true := by decide +kernel

theorem originalChecked :
  Airbender.Compiler.TableNative.JumpBranchCached.native.multiplicityColumns = [28, 26, 27] ∧ Function.Injective Airbender.Compiler.CounterFrameNative.JumpBranchCached.native.slots ∧
  (∀ index, 49 ≤ (Airbender.Compiler.CounterFrameNative.JumpBranchCached.native.slots index).val) ∧
  (∀ index, Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.inputBank.address (Airbender.Compiler.CounterFrameNative.JumpBranchCached.native.slots index) =
    GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.JumpBranchCached.native.multiplicityColumns.get index)) ∧
  Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.artifact.source.all (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.JumpBranchCached.native.slots)) = true ∧
  (Airbender.Compiler.HelperNative.JumpBranchCached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.helperPlacement)).all
    (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.JumpBranchCached.native.slots)) = true :=
  NumericCounterFrameChecks.check_sound data 49 Airbender.Compiler.TableNative.JumpBranchCached.native.multiplicityColumns [28, 26, 27] Airbender.Compiler.CounterFrameNative.JumpBranchCached.native.slots
    Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.inputBank Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.artifact.source
    (Airbender.Compiler.HelperNative.JumpBranchCached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.helperPlacement)) source_binding checked

end Airbender.Compiler.CounterFrameChecks.JumpBranchCached
