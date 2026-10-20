import Slop.Block.ParSym
import Slop.RV.Code.blake2s_compress
import Slop.RV.Blake.BlockStates

/-! Part 3 of `blake2s_compress`'s symbolic run (`Block.lean`): its kernel check, from the previous boundary state. -/

namespace RV
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

sym_part Blake 240 3 := Code.blake2s_compress

end RV
