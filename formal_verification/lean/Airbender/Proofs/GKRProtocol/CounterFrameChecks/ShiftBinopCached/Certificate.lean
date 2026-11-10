import Airbender.Proofs.GKRProtocol.CounterFrameChecks.ShiftBinopCached.Bindings

namespace Airbender.Compiler.CounterFrameChecks.ShiftBinopCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericCounterFrameChecks.check 92 data = true := by decide +kernel

theorem originalChecked :
  Airbender.Compiler.TableNative.ShiftBinopCached.native.multiplicityColumns = [27, 25, 26] ∧ Function.Injective Airbender.Compiler.CounterFrameNative.ShiftBinopCached.native.slots ∧
  (∀ index, 92 ≤ (Airbender.Compiler.CounterFrameNative.ShiftBinopCached.native.slots index).val) ∧
  (∀ index, Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.inputBank.address (Airbender.Compiler.CounterFrameNative.ShiftBinopCached.native.slots index) =
    GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.ShiftBinopCached.native.multiplicityColumns.get index)) ∧
  Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.artifact.source.all (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.ShiftBinopCached.native.slots)) = true ∧
  (Airbender.Compiler.HelperNative.ShiftBinopCached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.helperPlacement)).all
    (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.ShiftBinopCached.native.slots)) = true :=
  NumericCounterFrameChecks.check_sound data 92 Airbender.Compiler.TableNative.ShiftBinopCached.native.multiplicityColumns [27, 25, 26] Airbender.Compiler.CounterFrameNative.ShiftBinopCached.native.slots
    Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.inputBank Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.artifact.source
    (Airbender.Compiler.HelperNative.ShiftBinopCached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.helperPlacement)) source_binding checked

end Airbender.Compiler.CounterFrameChecks.ShiftBinopCached
