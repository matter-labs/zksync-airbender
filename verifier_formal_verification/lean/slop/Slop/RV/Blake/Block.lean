import Slop.RV.Code.blake2s_compress
import Slop.Block.ParSym
import Slop.RV.Blake.BlockStates
import Slop.RV.Blake.BlockP1
import Slop.RV.Blake.BlockP2
import Slop.RV.Blake.BlockP3
import Slop.RV.Blake.BlockP4
import Slop.RV.Blake.BlockP5
import Slop.RV.Blake.BlockP6

/-! `blake2s_compress` (the verifier's `Blake2RoundFunctionEvaluator`, baseline, 7 rounds, fully unrolled): the
symbolic run of its body, in six parts (`BlockP1` … `BlockP6`, checked in parallel) and the glue `sym_glue`. -/

namespace RV
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

sym_glue Blake 240 := Code.blake2s_compress

end RV
