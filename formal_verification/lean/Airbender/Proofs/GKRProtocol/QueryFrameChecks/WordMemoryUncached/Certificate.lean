import Airbender.Proofs.GKRProtocol.QueryFrameChecks.WordMemoryUncached.Bindings
import Airbender.Proofs.GKRProtocol.QueryFrameChecks.WordMemoryUncached.IndexedData

namespace Airbender.Compiler.QueryFrameChecks.WordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem indexedChecked : NumericQueryFrameChecks.indexedCheck views data.fields = true := by decide +kernel

theorem checked : NumericQueryFrameChecks.check data = true :=
  NumericQueryFrameChecks.indexedCheck_sound views data coordinates_index_binding
    placement_index_binding nativeAddress_index_binding returnedAddress_index_binding indexedChecked

theorem originalChecked : Airbender.Compiler.QueryFrameNative.WordMemoryUncached.native.fields.all (fun field =>
    erasureUntouched Airbender.Compiler.QueryFrameNative.WordMemoryUncached.native.coordinates (field.polynomial Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.originalProjection) &&
      field.transportCheck Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.originalProjection Airbender.Compiler.LookupNative.WordMemoryUncached.native.sourcePlacement
        Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.inputBank Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank) = true :=
  NumericQueryFrameChecks.check_sound data Airbender.Compiler.QueryFrameNative.WordMemoryUncached.native.fields Airbender.Compiler.QueryFrameNative.WordMemoryUncached.native.coordinates
    Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.originalProjection Airbender.Compiler.LookupNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.inputBank Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank
    coordinates_binding placement_binding nativeAddress_binding returnedAddress_binding fields_binding checked

end Airbender.Compiler.QueryFrameChecks.WordMemoryUncached
