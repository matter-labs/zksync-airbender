import Airbender.Proofs.GKRProtocol.CounterFrameChecks.ShiftBinopUncached.Bindings

namespace Airbender.Compiler.CounterFrameChecks.ShiftBinopUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericCounterFrameChecks.check 92 data = true := by decide +kernel

theorem originalChecked :
  Airbender.Compiler.TableNative.ShiftBinopUncached.native.multiplicityColumns = [27, 25, 26] ∧ Function.Injective Airbender.Compiler.CounterFrameNative.ShiftBinopUncached.native.slots ∧
  (∀ index, 92 ≤ (Airbender.Compiler.CounterFrameNative.ShiftBinopUncached.native.slots index).val) ∧
  (∀ index, Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.inputBank.address (Airbender.Compiler.CounterFrameNative.ShiftBinopUncached.native.slots index) =
    GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.ShiftBinopUncached.native.multiplicityColumns.get index)) ∧
  Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.artifact.source.all (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.ShiftBinopUncached.native.slots)) = true ∧
  (Airbender.Compiler.HelperNative.ShiftBinopUncached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.helperPlacement)).all
    (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.ShiftBinopUncached.native.slots)) = true :=
  NumericCounterFrameChecks.check_sound data 92 Airbender.Compiler.TableNative.ShiftBinopUncached.native.multiplicityColumns [27, 25, 26] Airbender.Compiler.CounterFrameNative.ShiftBinopUncached.native.slots
    Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.artifact.source
    (Airbender.Compiler.HelperNative.ShiftBinopUncached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.helperPlacement)) source_binding checked

end Airbender.Compiler.CounterFrameChecks.ShiftBinopUncached
