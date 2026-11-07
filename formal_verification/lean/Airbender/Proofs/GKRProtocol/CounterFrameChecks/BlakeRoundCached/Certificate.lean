import Airbender.Proofs.GKRProtocol.CounterFrameChecks.BlakeRoundCached.Bindings

namespace Airbender.Compiler.CounterFrameChecks.BlakeRoundCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericCounterFrameChecks.check 632 data = true := by decide +kernel

theorem originalChecked :
  Airbender.Compiler.TableNative.BlakeRoundCached.native.multiplicityColumns = [537, 536] ∧ Function.Injective Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.slots ∧
  (∀ index, 632 ≤ (Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.slots index).val) ∧
  (∀ index, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank.address (Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.slots index) =
    GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.BlakeRoundCached.native.multiplicityColumns.get index)) ∧
  Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.source.all (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.slots)) = true ∧
  (Airbender.Compiler.HelperNative.BlakeRoundCached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.helperPlacement)).all
    (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.slots)) = true :=
  NumericCounterFrameChecks.check_sound data 632 Airbender.Compiler.TableNative.BlakeRoundCached.native.multiplicityColumns [537, 536] Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.slots
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.source
    (Airbender.Compiler.HelperNative.BlakeRoundCached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.helperPlacement)) source_binding checked

end Airbender.Compiler.CounterFrameChecks.BlakeRoundCached
