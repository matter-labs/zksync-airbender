import Airbender.Proofs.GKRProtocol.QueryFrameChecks.KeccakUncached.Bindings
import Airbender.Proofs.GKRProtocol.QueryFrameChecks.KeccakUncached.IndexedData

namespace Airbender.Compiler.QueryFrameChecks.KeccakUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem indexedChecked : NumericQueryFrameChecks.indexedCheck views data.fields = true := by decide +kernel

theorem checked : NumericQueryFrameChecks.check data = true :=
  NumericQueryFrameChecks.indexedCheck_sound views data coordinates_index_binding
    placement_index_binding nativeAddress_index_binding returnedAddress_index_binding indexedChecked

theorem originalChecked : Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields.all (fun field =>
    erasureUntouched Airbender.Compiler.QueryFrameNative.KeccakUncached.native.coordinates (field.polynomial Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.originalProjection) &&
      field.transportCheck Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.originalProjection Airbender.Compiler.LookupNative.KeccakUncached.native.sourcePlacement
        Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputBank Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank) = true :=
  NumericQueryFrameChecks.check_sound data Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields Airbender.Compiler.QueryFrameNative.KeccakUncached.native.coordinates
    Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.originalProjection Airbender.Compiler.LookupNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputBank Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank
    coordinates_binding placement_binding nativeAddress_binding returnedAddress_binding fields_binding checked

end Airbender.Compiler.QueryFrameChecks.KeccakUncached
