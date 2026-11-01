import Airbender.Proofs.GKRProtocol.CounterFrameChecks.MulDivCached.Bindings

namespace Airbender.Compiler.CounterFrameChecks.MulDivCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericCounterFrameChecks.check 65 data = true := by decide +kernel

theorem originalChecked :
  Airbender.Compiler.TableNative.MulDivCached.native.multiplicityColumns = [23, 21, 22] ∧ Function.Injective Airbender.Compiler.CounterFrameNative.MulDivCached.native.slots ∧
  (∀ index, 65 ≤ (Airbender.Compiler.CounterFrameNative.MulDivCached.native.slots index).val) ∧
  (∀ index, Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputBank.address (Airbender.Compiler.CounterFrameNative.MulDivCached.native.slots index) =
    GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.MulDivCached.native.multiplicityColumns.get index)) ∧
  Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.source.all (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.MulDivCached.native.slots)) = true ∧
  (Airbender.Compiler.HelperNative.MulDivCached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.MulDivCached.native.helperPlacement)).all
    (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.MulDivCached.native.slots)) = true :=
  NumericCounterFrameChecks.check_sound data 65 Airbender.Compiler.TableNative.MulDivCached.native.multiplicityColumns [23, 21, 22] Airbender.Compiler.CounterFrameNative.MulDivCached.native.slots
    Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputBank Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.source
    (Airbender.Compiler.HelperNative.MulDivCached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.MulDivCached.native.helperPlacement)) source_binding checked

end Airbender.Compiler.CounterFrameChecks.MulDivCached
