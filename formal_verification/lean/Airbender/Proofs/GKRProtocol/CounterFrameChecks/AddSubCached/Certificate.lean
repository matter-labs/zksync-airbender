import Airbender.Proofs.GKRProtocol.CounterFrameChecks.AddSubCached.Bindings

namespace Airbender.Compiler.CounterFrameChecks.AddSubCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericCounterFrameChecks.check 42 data = true := by decide +kernel

theorem originalChecked :
  Airbender.Compiler.TableNative.AddSubCached.native.multiplicityColumns = [21, 19, 20] ∧ Function.Injective Airbender.Compiler.CounterFrameNative.AddSubCached.native.slots ∧
  (∀ index, 42 ≤ (Airbender.Compiler.CounterFrameNative.AddSubCached.native.slots index).val) ∧
  (∀ index, Airbender.Compiler.FullArithmeticNative.AddSubCached.native.inputBank.address (Airbender.Compiler.CounterFrameNative.AddSubCached.native.slots index) =
    GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.AddSubCached.native.multiplicityColumns.get index)) ∧
  Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.source.all (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.AddSubCached.native.slots)) = true ∧
  (Airbender.Compiler.HelperNative.AddSubCached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.AddSubCached.native.helperPlacement)).all
    (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.AddSubCached.native.slots)) = true :=
  NumericCounterFrameChecks.check_sound data 42 Airbender.Compiler.TableNative.AddSubCached.native.multiplicityColumns [21, 19, 20] Airbender.Compiler.CounterFrameNative.AddSubCached.native.slots
    Airbender.Compiler.FullArithmeticNative.AddSubCached.native.inputBank Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.source
    (Airbender.Compiler.HelperNative.AddSubCached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.AddSubCached.native.helperPlacement)) source_binding checked

end Airbender.Compiler.CounterFrameChecks.AddSubCached
