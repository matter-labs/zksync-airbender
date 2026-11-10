import Airbender.Proofs.GKRProtocol.CounterFrameChecks.BlakeGCached.Bindings

namespace Airbender.Compiler.CounterFrameChecks.BlakeGCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericCounterFrameChecks.check 83 data = true := by decide +kernel

theorem originalChecked :
  Airbender.Compiler.TableNative.BlakeGCached.native.multiplicityColumns = [56, 55] ∧ Function.Injective Airbender.Compiler.CounterFrameNative.BlakeGCached.native.slots ∧
  (∀ index, 83 ≤ (Airbender.Compiler.CounterFrameNative.BlakeGCached.native.slots index).val) ∧
  (∀ index, Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.inputBank.address (Airbender.Compiler.CounterFrameNative.BlakeGCached.native.slots index) =
    GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.BlakeGCached.native.multiplicityColumns.get index)) ∧
  Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.source.all (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.BlakeGCached.native.slots)) = true ∧
  (Airbender.Compiler.HelperNative.BlakeGCached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.helperPlacement)).all
    (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.BlakeGCached.native.slots)) = true :=
  NumericCounterFrameChecks.check_sound data 83 Airbender.Compiler.TableNative.BlakeGCached.native.multiplicityColumns [56, 55] Airbender.Compiler.CounterFrameNative.BlakeGCached.native.slots
    Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.inputBank Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.source
    (Airbender.Compiler.HelperNative.BlakeGCached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.helperPlacement)) source_binding checked

end Airbender.Compiler.CounterFrameChecks.BlakeGCached
