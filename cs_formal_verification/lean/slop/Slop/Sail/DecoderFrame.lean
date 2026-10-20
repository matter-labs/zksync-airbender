import Slop.Sail.MisaWalk

namespace Airbender.Reference.Sail
open Reference.RiscV.Sail _root_.Sail.ArchSem

/-- Successful original Sail decoding changes no state. Its result is unchanged
    in any state with the same `misa` image, including native GPR/PC updates. -/
theorem decoded_misa_frame (bits : BitVec 32) {before after : State}
    {instruction : SailRV32.instruction}
    (decoded : run (SailRV32.Functions.encdec_backwards bits) before = .ok instruction after) :
    after = before ∧ ∀ state, state.regs.get? .misa = before.regs.get? .misa →
      run (SailRV32.Functions.encdec_backwards bits) state = .ok instruction state := by
  have checked : MisaOnly (SailRV32.Functions.encdec_backwards bits) := by
    unfold SailRV32.Functions.encdec_backwards
    misa_walk
  unfold MisaOnly at checked
  exact checked before instruction after decoded

end Airbender.Reference.Sail
