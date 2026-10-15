import Slop.RV.Code.blake2s_compress
import Slop.Sym.Meta

/-! `blake2s_compress` (the verifier's `Blake2RoundFunctionEvaluator`, baseline, 7 rounds, fully unrolled): the
symbolic run of its body, chunk by chunk. -/

namespace RV
set_option maxRecDepth 100000

sym_block Blake := Code.blake2s_compress

end RV
