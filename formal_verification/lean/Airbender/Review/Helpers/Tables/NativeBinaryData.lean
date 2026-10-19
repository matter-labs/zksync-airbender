import Airbender.Import.SetupEmbed

namespace Airbender.Verification.NativeBinary
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
import_native_binary data from "artifacts/setup/shift-binary-native.json"
end Airbender.Verification.NativeBinary
