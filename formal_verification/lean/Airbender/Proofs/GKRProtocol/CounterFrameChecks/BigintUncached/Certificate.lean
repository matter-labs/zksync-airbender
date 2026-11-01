import Airbender.Proofs.GKRProtocol.CounterFrameChecks.BigintUncached.Bindings

namespace Airbender.Compiler.CounterFrameChecks.BigintUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericCounterFrameChecks.check 216 data = true := by decide +kernel

theorem originalChecked :
  Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns = [159, 157, 158] ∧ Function.Injective Airbender.Compiler.CounterFrameNative.BigintUncached.native.slots ∧
  (∀ index, 216 ≤ (Airbender.Compiler.CounterFrameNative.BigintUncached.native.slots index).val) ∧
  (∀ index, Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank.address (Airbender.Compiler.CounterFrameNative.BigintUncached.native.slots index) =
    GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns.get index)) ∧
  Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.source.all (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.BigintUncached.native.slots)) = true ∧
  (Airbender.Compiler.HelperNative.BigintUncached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BigintUncached.native.helperPlacement)).all
    (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.BigintUncached.native.slots)) = true :=
  NumericCounterFrameChecks.check_sound data 216 Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns [159, 157, 158] Airbender.Compiler.CounterFrameNative.BigintUncached.native.slots
    Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.source
    (Airbender.Compiler.HelperNative.BigintUncached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BigintUncached.native.helperPlacement)) source_binding checked

end Airbender.Compiler.CounterFrameChecks.BigintUncached
