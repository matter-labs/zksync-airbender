import Human.Helpers.Decoder.Program
import Human.Helpers.Memory.ROM
import Human.Helpers.Memory.Values

namespace Airbender.Trace

/-- Select unchanged Sail semantics or the explicitly documented LW-to-x0
    Airbender deviation. The selected profile is visible in the execution claim. -/
inductive ISAProfile where
  | sail
  | airbender

end Airbender.Trace
