import Human.Helpers.Context.Registries.Pooled
import Human.Helpers.Decoder.Program
import Human.Circuits.JumpBranchSlt.Decoder
import Human.Circuits.MulDiv.Decoder
import Human.Circuits.ShiftBinop.Decoder
import Human.Circuits.SubwordMemory.Decoder

namespace Airbender.Trace

def pooledArithmeticFamily : Family → PooledFamily
  | .addSub => .addSub
  | .wordMemory => .wordMemory

end Airbender.Trace
