import Airbender.Proofs.GKRProtocol.CounterFrameChecks.UnifiedUncached.Bindings

namespace Airbender.Compiler.CounterFrameChecks.UnifiedUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericCounterFrameChecks.check 123 data = true := by decide +kernel

theorem originalChecked :
  Airbender.Compiler.TableNative.UnifiedUncached.native.multiplicityColumns = [57, 55, 56] ∧ Function.Injective Airbender.Compiler.CounterFrameNative.UnifiedUncached.native.slots ∧
  (∀ index, 123 ≤ (Airbender.Compiler.CounterFrameNative.UnifiedUncached.native.slots index).val) ∧
  (∀ index, Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.inputBank.address (Airbender.Compiler.CounterFrameNative.UnifiedUncached.native.slots index) =
    GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.UnifiedUncached.native.multiplicityColumns.get index)) ∧
  Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.source.all (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.UnifiedUncached.native.slots)) = true ∧
  (Airbender.Compiler.HelperNative.UnifiedUncached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.helperPlacement)).all
    (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.UnifiedUncached.native.slots)) = true :=
  NumericCounterFrameChecks.check_sound data 123 Airbender.Compiler.TableNative.UnifiedUncached.native.multiplicityColumns [57, 55, 56] Airbender.Compiler.CounterFrameNative.UnifiedUncached.native.slots
    Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.source
    (Airbender.Compiler.HelperNative.UnifiedUncached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.helperPlacement)) source_binding checked

end Airbender.Compiler.CounterFrameChecks.UnifiedUncached
