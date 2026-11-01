import Airbender.Proofs.GKRProtocol.QueryFrameChecks.ShiftBinopUncached.Bindings
import Airbender.Proofs.GKRProtocol.QueryFrameChecks.ShiftBinopUncached.IndexedData

namespace Airbender.Compiler.QueryFrameChecks.ShiftBinopUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem indexedChecked : NumericQueryFrameChecks.indexedCheck views data.fields = true := by decide +kernel

theorem checked : NumericQueryFrameChecks.check data = true :=
  NumericQueryFrameChecks.indexedCheck_sound views data coordinates_index_binding
    placement_index_binding nativeAddress_index_binding returnedAddress_index_binding indexedChecked

theorem originalChecked : Airbender.Compiler.QueryFrameNative.ShiftBinopUncached.native.fields.all (fun field =>
    erasureUntouched Airbender.Compiler.QueryFrameNative.ShiftBinopUncached.native.coordinates (field.polynomial Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.originalProjection) &&
      field.transportCheck Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.originalProjection Airbender.Compiler.LookupNative.ShiftBinopUncached.native.sourcePlacement
        Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.inputBank Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank) = true :=
  NumericQueryFrameChecks.check_sound data Airbender.Compiler.QueryFrameNative.ShiftBinopUncached.native.fields Airbender.Compiler.QueryFrameNative.ShiftBinopUncached.native.coordinates
    Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.originalProjection Airbender.Compiler.LookupNative.ShiftBinopUncached.native.sourcePlacement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.inputBank Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank
    coordinates_binding placement_binding nativeAddress_binding returnedAddress_binding fields_binding checked

end Airbender.Compiler.QueryFrameChecks.ShiftBinopUncached
