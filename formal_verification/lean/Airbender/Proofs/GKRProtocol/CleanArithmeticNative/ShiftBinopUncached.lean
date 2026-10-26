import Airbender.Import.GKRProtocol.CleanArithmeticImport
import Airbender.Proofs.GKRProtocol.FullArithmeticNative.ShiftBinopUncached

namespace Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_clean_arithmetic native from "artifacts/compiler/shift-binop-uncached.json"
  selectors "{\"format_version\":1,\"witnesses\":[[[[[1,[]]],43]],[[[[1,[]]],1]],[[[[1,[]]],2]],[[[[1,[]]],3]],[[[[1,[]]],4]],[[[[1,[]]],5]],[[[[1,[]]],6]],[[[[1,[]]],7]],[[[[1,[]]],8]],[[[[1,[]]],9]],[[[[1,[]]],10]],[[[[1,[]]],11]],[[[[1,[]]],12]],[[[[1,[]]],13]],[[[[1,[]]],14]],[[[[1,[]]],15]],[[[[1,[]]],16]],[[[[1,[]]],17]],[[[[1,[]]],18]],[[[[1,[]]],19]],[[[[1,[]]],20]],[[[[1,[]]],21]],[[[[1,[]]],22]],[[[[1,[]]],23]],[[[[1,[]]],24]],[[[[1,[]]],25]],[[[[1,[]]],26]],[[[[1,[]]],27]],[[[[1,[]]],28]],[[[[1,[]]],29]],[[[[1,[]]],30]],[[[[1,[]]],31]],[[[[1,[]]],32]],[[[[1,[]]],33]],[[[[1,[]]],34]],[[[[1,[]]],35]],[[[[1,[]]],36]],[[[[1,[]]],37]],[[[[1,[]]],38]],[[[[1,[]]],39]],[[[[1,[]]],40]],[[[[1,[]]],44]],[[[[1,[]]],45]],[[[[1,[]]],46]],[[[[1,[]]],47]],[[[[1,[]]],48]],[[[[1,[]]],49]],[[[[1,[]]],50]],[[[[1,[]]],51]],[[[[1,[]]],52]],[[[[1,[]]],53]],[[[[1,[]]],54]]]}"
  base_model Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native variables 102

end Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached
