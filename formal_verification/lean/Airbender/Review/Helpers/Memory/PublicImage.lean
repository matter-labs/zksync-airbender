import Airbender.Review.Helpers.Memory.InitialImage

namespace Airbender.Trace

/-- Public state/domain constructors bind native seed values and initial PC.
    Reads come from the original Sail interpreter; failures reject construction.
    The initial native clock is four and every seed clock is zero. This is a
    logical boundary; physical boot/profile and decoder enforcement are separate. -/
structure ImageBoundary {p : Nat} [Fact p.Prime] (trace : Data p)
    (before : Reference.RiscV.Sail.State) (cells : List Cell) : Prop where
  /-- The public tracked-cell domain has no duplicate register/RAM cells. -/
  domain : cells.Nodup
  /-- Native seed tokens are extracted from actual Sail reads of that domain. -/
  image : initialImage before cells = some trace.initialMemory
  /-- Native starting PC comes from Sail's architectural PC; native clock is four. -/
  initial : initialState before (4, 0) = some trace.initial

end Airbender.Trace
