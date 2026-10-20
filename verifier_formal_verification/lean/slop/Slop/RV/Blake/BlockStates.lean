import Slop.Block.ParSym
import Slop.RV.Code.blake2s_compress

/-! The symbolic states of `blake2s_compress` at the boundaries of its 240-instruction parts (`Block.lean`). -/

namespace RV
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

sym_states Blake 240 := Code.blake2s_compress

end RV
