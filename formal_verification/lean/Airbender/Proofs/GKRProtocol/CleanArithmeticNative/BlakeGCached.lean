import Airbender.Import.GKRProtocol.CleanArithmeticImport
import Airbender.Proofs.GKRProtocol.FullArithmeticNative.BlakeGCached

namespace Airbender.Compiler.CleanArithmeticNative.BlakeGCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_clean_arithmetic native from "artifacts/compiler/blake-g-cached.json"
  selectors "{\"format_version\":1,\"witnesses\":[[[[[1,[]]],22]],[[[[1,[]]],23]],[[[[1,[]]],24]],[[[[1,[]]],25]],[[[[1,[]]],26]],[[[[1,[]]],27]],[[[[1,[]]],28]],[[[[1,[]]],29]],[[[[1,[]]],30]],[[[[1,[]]],31]],[[[[1,[]]],32]],[[[[1,[]]],33]],[[[[1,[]]],34]],[[[[1,[]]],35]],[[[[1,[]]],36]],[[[[1,[]]],37]],[[[[1,[]]],38]],[[[[1,[]]],39]],[[[[1,[]]],40]],[[[[1,[]]],41]],[[[[1,[]]],42]],[[[[1,[]]],43]],[[[[1,[]]],44]],[[[[1,[]]],45]],[[[[1,[]]],46]],[[[[1,[]]],47]],[[[[1,[]]],48]],[[[[1,[]]],49]],[[[[1,[]]],50]],[[[[1,[]]],51]],[[[[1,[]]],52]],[[[[1,[]]],53]],[[[[1,[]]],54]],[[[[1,[]]],55]]]}"
  base_model Airbender.Compiler.FullArithmeticNative.BlakeGCached.native variables 138

end Airbender.Compiler.CleanArithmeticNative.BlakeGCached
