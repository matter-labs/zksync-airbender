module
public import Human.Helpers.Context.Registries.Pooled
public import Human.Helpers.Decoder.Program
public import Human.Circuits.JumpBranchSlt.Decoder
public import Human.Circuits.MulDiv.Decoder
public import Human.Circuits.ShiftBinop.Decoder
public import Human.Circuits.SubwordMemory.Decoder

@[expose] public section

namespace Airbender.Trace

def pooledArithmeticFamily : Family → PooledFamily
  | .addSub => .addSub
  | .wordMemory => .wordMemory

end Airbender.Trace
