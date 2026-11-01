import Airbender.Proofs.GKRProtocol.QueryFrameChecks.UnifiedUncached.Bindings
import Airbender.Proofs.GKRProtocol.QueryFrameChecks.UnifiedUncached.IndexedData

namespace Airbender.Compiler.QueryFrameChecks.UnifiedUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem indexedChecked : NumericQueryFrameChecks.indexedCheck views data.fields = true := by decide +kernel

theorem checked : NumericQueryFrameChecks.check data = true :=
  NumericQueryFrameChecks.indexedCheck_sound views data coordinates_index_binding
    placement_index_binding nativeAddress_index_binding returnedAddress_index_binding indexedChecked

theorem originalChecked : Airbender.Compiler.QueryFrameNative.UnifiedUncached.native.fields.all (fun field =>
    erasureUntouched Airbender.Compiler.QueryFrameNative.UnifiedUncached.native.coordinates (field.polynomial Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.originalProjection) &&
      field.transportCheck Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.originalProjection Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement
        Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.inputBank Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank) = true :=
  NumericQueryFrameChecks.check_sound data Airbender.Compiler.QueryFrameNative.UnifiedUncached.native.fields Airbender.Compiler.QueryFrameNative.UnifiedUncached.native.coordinates
    Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.originalProjection Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.inputBank Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank
    coordinates_binding placement_binding nativeAddress_binding returnedAddress_binding fields_binding checked

end Airbender.Compiler.QueryFrameChecks.UnifiedUncached
