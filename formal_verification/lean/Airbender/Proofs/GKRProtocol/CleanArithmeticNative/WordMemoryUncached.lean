import Airbender.Import.GKRProtocol.CleanArithmeticImport
import Airbender.Proofs.GKRProtocol.FullArithmeticNative.WordMemoryUncached

namespace Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_clean_arithmetic native from "artifacts/compiler/word-memory-uncached.json"
  selectors "{\"format_version\":1,\"witnesses\":[[[[[1,[]]],11]],[[[[1,[]]],12]],[[[[1,[]]],13]],[[[[1,[]]],1]],[[[[1,[]]],2]],[[[[1,[]]],30]],[[[[1,[]]],31]],[[[[1,[]]],3]],[[[[1,[]]],14]],[[[[1,[]]],4]],[[[[1,[]]],5]],[[[[1,[]]],24]],[[[[1,[]]],6]],[[[[1,[]]],25]],[[[[1,[]]],7]],[[[[1,[]]],26]],[[[[1,[]]],8]],[[[[1,[]]],27]],[[[[1,[]]],15]],[[[[1,[]]],16]],[[[[1,[]]],17]],[[[[1,[]]],18]],[[[[1,[]]],19]],[[[[1,[]]],20]],[[[[1,[]]],21]],[[[[1,[]]],22]],[[[[1,[]]],23]]]}"
  base_model Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native variables 57

end Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached
