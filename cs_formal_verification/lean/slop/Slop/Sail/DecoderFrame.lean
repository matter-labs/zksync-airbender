import Slop.Sail.MisaWalk
import Slop.Sail.MisaDecoder

namespace Airbender.Reference.Sail
open Reference.RiscV.Sail _root_.Sail.ArchSem

set_option maxRecDepth 65536 in
/-- Successful original Sail decoding changes no state. Its result is unchanged in any state that agrees
    on the registers a program never writes (`ConfigSame`; any two `Configured` states do, by
    `configured_same`), including native GPR/PC updates. The full model's decoder reads more than `misa`
    (`vtype`, `mstatus`, the privilege level, …), all of them in that set. -/
theorem decoded_misa_frame (bits : BitVec 32) {before after : State}
    {instruction : SailRV32.instruction}
    (decoded : run (SailRV32.Functions.encdec_backwards bits) before = .ok instruction after) :
    after = before ∧ ∀ state, ConfigSame before state →
      run (SailRV32.Functions.encdec_backwards bits) state = .ok instruction state := by
  have checked : MisaOnly (SailRV32.Functions.encdec_backwards bits) := by
    unfold SailRV32.Functions.encdec_backwards
    misa_walk
  unfold MisaOnly at checked
  exact checked before instruction after decoded

end Airbender.Reference.Sail
