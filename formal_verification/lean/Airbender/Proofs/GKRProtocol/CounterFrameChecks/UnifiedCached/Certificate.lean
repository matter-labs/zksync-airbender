import Airbender.Proofs.GKRProtocol.CounterFrameChecks.UnifiedCached.Bindings

namespace Airbender.Compiler.CounterFrameChecks.UnifiedCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericCounterFrameChecks.check 123 data = true := by decide +kernel

theorem originalChecked :
  Airbender.Compiler.TableNative.UnifiedCached.native.multiplicityColumns = [57, 55, 56] ∧ Function.Injective Airbender.Compiler.CounterFrameNative.UnifiedCached.native.slots ∧
  (∀ index, 123 ≤ (Airbender.Compiler.CounterFrameNative.UnifiedCached.native.slots index).val) ∧
  (∀ index, Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank.address (Airbender.Compiler.CounterFrameNative.UnifiedCached.native.slots index) =
    GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.UnifiedCached.native.multiplicityColumns.get index)) ∧
  Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.source.all (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.UnifiedCached.native.slots)) = true ∧
  (Airbender.Compiler.HelperNative.UnifiedCached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement)).all
    (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.UnifiedCached.native.slots)) = true :=
  NumericCounterFrameChecks.check_sound data 123 Airbender.Compiler.TableNative.UnifiedCached.native.multiplicityColumns [57, 55, 56] Airbender.Compiler.CounterFrameNative.UnifiedCached.native.slots
    Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.source
    (Airbender.Compiler.HelperNative.UnifiedCached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement)) source_binding checked

end Airbender.Compiler.CounterFrameChecks.UnifiedCached
