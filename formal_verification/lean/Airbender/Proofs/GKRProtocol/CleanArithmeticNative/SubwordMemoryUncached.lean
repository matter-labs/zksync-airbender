import Airbender.Import.GKRProtocol.CleanArithmeticImport
import Airbender.Proofs.GKRProtocol.FullArithmeticNative.SubwordMemoryUncached

namespace Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_clean_arithmetic native from "artifacts/compiler/subword-memory-uncached.json"
  selectors "{\"format_version\":1,\"witnesses\":[[[[[1,[]]],20]],[[[[1,[]]],21]],[[[[1,[]]],22]],[[[[1,[]]],1]],[[[[1,[]]],44]],[[[[1,[]]],2]],[[[[1,[]]],45]],[[[[1,[]]],3]],[[[[1,[]]],23]],[[[[1,[]]],24]],[[[[1,[]]],4]],[[[[1,[]]],25]],[[[[1,[]]],5]],[[[[1,[]]],6]],[[[[1,[]]],7]],[[[[1,[]]],8]],[[[[1,[]]],9]],[[[[1,[]]],10]],[[[[1,[]]],11]],[[[[1,[]]],12]],[[[[1,[]]],39]],[[[[1,[]]],13]],[[[[1,[]]],14]],[[[[1,[]]],40]],[[[[1,[]]],15]],[[[[1,[]]],16]],[[[[1,[]]],41]],[[[[1,[]]],17]],[[[[1,[]]],18]],[[[[1,[]]],42]],[[[[1,[]]],26]],[[[[1,[]]],27]],[[[[1,[]]],28]],[[[[1,[]]],29]],[[[[1,[]]],30]],[[[[1,[]]],31]],[[[[1,[]]],32]],[[[[1,[]]],33]],[[[[1,[]]],34]],[[[[1,[]]],35]],[[[[1,[]]],36]],[[[[1,[]]],37]],[[[[1,[]]],38]]]}"
  base_model Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native variables 71

end Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached
