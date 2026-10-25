import GKRProtocol.CleanArithmeticImport
import GKRProtocol.FullArithmeticNative.WordMemoryCached

namespace Airbender.Compiler.CleanArithmeticNative.WordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_clean_arithmetic native from "artifacts/compiler/word-memory-cached.json"
  selectors "{\"format_version\":1,\"witnesses\":[[[[[1,[]]],17]],[[[[1,[]]],18]],[[[[1,[]]],19]],[[[[1,[]]],7]],[[[[1,[]]],8]],[[[[1,[]]],36]],[[[[1,[]]],37]],[[[[1,[]]],9]],[[[[1,[]]],20]],[[[[1,[]]],10]],[[[[1,[]]],11]],[[[[1,[]]],30]],[[[[1,[]]],12]],[[[[1,[]]],31]],[[[[1,[]]],13]],[[[[1,[]]],32]],[[[[1,[]]],14]],[[[[1,[]]],33]],[[[[1,[]]],21]],[[[[1,[]]],22]],[[[[1,[]]],23]],[[[[1,[]]],24]],[[[[1,[]]],25]],[[[[1,[]]],26]],[[[[1,[]]],27]],[[[[1,[]]],28]],[[[[1,[]]],29]]]}"
  base_model Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native variables 63

end Airbender.Compiler.CleanArithmeticNative.WordMemoryCached
