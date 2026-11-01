import Airbender.Proofs.GKRProtocol.CounterFrameChecks.AddSubUncached.Bindings

namespace Airbender.Compiler.CounterFrameChecks.AddSubUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericCounterFrameChecks.check 42 data = true := by decide +kernel

theorem originalChecked :
  Airbender.Compiler.TableNative.AddSubUncached.native.multiplicityColumns = [21, 19, 20] ∧ Function.Injective Airbender.Compiler.CounterFrameNative.AddSubUncached.native.slots ∧
  (∀ index, 42 ≤ (Airbender.Compiler.CounterFrameNative.AddSubUncached.native.slots index).val) ∧
  (∀ index, Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.inputBank.address (Airbender.Compiler.CounterFrameNative.AddSubUncached.native.slots index) =
    GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.AddSubUncached.native.multiplicityColumns.get index)) ∧
  Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.artifact.source.all (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.AddSubUncached.native.slots)) = true ∧
  (Airbender.Compiler.HelperNative.AddSubUncached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.helperPlacement)).all
    (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.AddSubUncached.native.slots)) = true :=
  NumericCounterFrameChecks.check_sound data 42 Airbender.Compiler.TableNative.AddSubUncached.native.multiplicityColumns [21, 19, 20] Airbender.Compiler.CounterFrameNative.AddSubUncached.native.slots
    Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.artifact.source
    (Airbender.Compiler.HelperNative.AddSubUncached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.helperPlacement)) source_binding checked

end Airbender.Compiler.CounterFrameChecks.AddSubUncached
