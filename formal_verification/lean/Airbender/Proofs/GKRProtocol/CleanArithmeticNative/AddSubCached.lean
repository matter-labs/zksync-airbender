import Airbender.Import.GKRProtocol.CleanArithmeticImport
import Airbender.Proofs.GKRProtocol.CleanIdealNative.AddSubCached
import Airbender.Proofs.GKRProtocol.FullArithmeticNative.AddSubCached
import Airbender.Proofs.GKRProtocol.CleanPlacementNative.AddSubCached

namespace Airbender.Compiler.CleanArithmeticNative.AddSubCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_clean_arithmetic native from "artifacts/compiler/add-sub-cached.json"
  selectors "{\"format_version\":1,\"witnesses\":[[[[[1,[]]],9]],[[[[1,[]]],10]],[[[[1,[]]],11]],[[[[1,[]]],12]],[[[[1,[]]],13]],[[[[1,[]]],14]],[[[[1,[]]],15]],[[[[1,[]]],16]],[[[[1,[]]],17]],[[[[1,[]]],18]],[[[[1,[]]],19]],[[[[1,[]]],20]],[[[[1,[]]],21]],[[[[1,[]]],22]],[[[[1,[]]],23]],[[[[1,[]]],24]],[[[[1,[]]],25]],[[[[1,[]]],26]],[[[[1,[]]],27]],[[[[1,[]]],28]],[[[[1,[]]],29]],[[[[1,[]]],30]],[[[[1,[]]],31]],[[[[1,[]]],32]],[[[[1,[]]],33]],[[[[1,[]]],34]],[[[[1,[]]],35]],[[[[1,[]]],36]],[[[[1,[]]],37]],[[[[1,[]]],38]]]}"
  base_model Airbender.Compiler.FullArithmeticNative.AddSubCached.native variables 58
  using Airbender.Compiler.CleanPlacementNative.AddSubCached
  ideal_checks Airbender.Compiler.CleanIdealNative.AddSubCached

end Airbender.Compiler.CleanArithmeticNative.AddSubCached
