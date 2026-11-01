import Airbender.Proofs.GKRProtocol.CounterFrameChecks.MulDivUncached.Bindings

namespace Airbender.Compiler.CounterFrameChecks.MulDivUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericCounterFrameChecks.check 65 data = true := by decide +kernel

theorem originalChecked :
  Airbender.Compiler.TableNative.MulDivUncached.native.multiplicityColumns = [23, 21, 22] ∧ Function.Injective Airbender.Compiler.CounterFrameNative.MulDivUncached.native.slots ∧
  (∀ index, 65 ≤ (Airbender.Compiler.CounterFrameNative.MulDivUncached.native.slots index).val) ∧
  (∀ index, Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.inputBank.address (Airbender.Compiler.CounterFrameNative.MulDivUncached.native.slots index) =
    GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.MulDivUncached.native.multiplicityColumns.get index)) ∧
  Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.artifact.source.all (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.MulDivUncached.native.slots)) = true ∧
  (Airbender.Compiler.HelperNative.MulDivUncached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.helperPlacement)).all
    (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.MulDivUncached.native.slots)) = true :=
  NumericCounterFrameChecks.check_sound data 65 Airbender.Compiler.TableNative.MulDivUncached.native.multiplicityColumns [23, 21, 22] Airbender.Compiler.CounterFrameNative.MulDivUncached.native.slots
    Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.artifact.source
    (Airbender.Compiler.HelperNative.MulDivUncached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.helperPlacement)) source_binding checked

end Airbender.Compiler.CounterFrameChecks.MulDivUncached
