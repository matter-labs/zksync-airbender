module
public import Human.Helpers.Decoder.Program
public import Human.Helpers.Memory.ROM
public import Human.Helpers.Memory.Values

@[expose] public section

namespace Airbender.Trace

/-- Select unchanged Sail semantics or the explicitly documented LW-to-x0
    Airbender deviation. The selected profile is visible in the execution claim. -/
inductive ISAProfile where
  | sail
  | airbender

end Airbender.Trace
