import Airbender.Proofs.GKRProtocol.CounterFrameChecks.BlakeGUncached.Bindings

namespace Airbender.Compiler.CounterFrameChecks.BlakeGUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericCounterFrameChecks.check 83 data = true := by decide +kernel

theorem originalChecked :
  Airbender.Compiler.TableNative.BlakeGUncached.native.multiplicityColumns = [56, 55] ∧ Function.Injective Airbender.Compiler.CounterFrameNative.BlakeGUncached.native.slots ∧
  (∀ index, 83 ≤ (Airbender.Compiler.CounterFrameNative.BlakeGUncached.native.slots index).val) ∧
  (∀ index, Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.inputBank.address (Airbender.Compiler.CounterFrameNative.BlakeGUncached.native.slots index) =
    GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.BlakeGUncached.native.multiplicityColumns.get index)) ∧
  Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.artifact.source.all (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.BlakeGUncached.native.slots)) = true ∧
  (Airbender.Compiler.HelperNative.BlakeGUncached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.helperPlacement)).all
    (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.BlakeGUncached.native.slots)) = true :=
  NumericCounterFrameChecks.check_sound data 83 Airbender.Compiler.TableNative.BlakeGUncached.native.multiplicityColumns [56, 55] Airbender.Compiler.CounterFrameNative.BlakeGUncached.native.slots
    Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.artifact.source
    (Airbender.Compiler.HelperNative.BlakeGUncached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.helperPlacement)) source_binding checked

end Airbender.Compiler.CounterFrameChecks.BlakeGUncached
