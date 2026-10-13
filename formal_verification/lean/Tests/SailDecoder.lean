import Airbender.Review.Helpers.Sail
import Airbender.Proofs.Sail.PC

namespace Tests.SailDecoder
open SailRV32
open Airbender.Reference.Sail

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option warningAsError true

-- These check the emitted upstream decoder, including the encoded immediates.
-- They are kernel reduction proofs, not evaluation-based proof shortcuts.
theorem add (state : Airbender.Reference.RiscV.Sail.State) :
    run (Functions.encdec_backwards 0x002081b3) state =
      .ok (.RTYPE (.Regidx 2, .Regidx 1, .Regidx 3, .ADD)) state := by rfl

theorem addi (state : Airbender.Reference.RiscV.Sail.State) :
    run (Functions.encdec_backwards 0xfff08113) state =
      .ok (.ITYPE (0xfff, .Regidx 1, .Regidx 2, .ADDI)) state := by rfl

theorem sub (state : Airbender.Reference.RiscV.Sail.State) :
    run (Functions.encdec_backwards 0x402081b3) state =
      .ok (.RTYPE (.Regidx 2, .Regidx 1, .Regidx 3, .SUB)) state := by rfl

theorem lui (state : Airbender.Reference.RiscV.Sail.State) :
    run (Functions.encdec_backwards 0x12345137) state =
      .ok (.UTYPE (0x12345, .Regidx 2, .LUI)) state := by rfl

theorem auipc (state : Airbender.Reference.RiscV.Sail.State) :
    run (Functions.encdec_backwards 0x12345117) state =
      .ok (.UTYPE (0x12345, .Regidx 2, .AUIPC)) state := by rfl

theorem lw (state : Airbender.Reference.RiscV.Sail.State) :
    run (Functions.encdec_backwards 0x0040a103) state =
      .ok (.LOAD (4, .Regidx 1, .Regidx 2, false, 4)) state := by rfl

theorem sw (state : Airbender.Reference.RiscV.Sail.State) :
    run (Functions.encdec_backwards 0x0020a223) state =
      .ok (.STORE (4, .Regidx 2, .Regidx 1, 4)) state := by rfl

/-- Original Zbb decoding uses the original Zba `Ext_B` enablement clause and
    the public ISA configuration. Generation supplies no replacement clause. -/
theorem rev8 {state : Airbender.Reference.RiscV.Sail.State}
    (configured : state.regs.get? .misa = some (0x40000002 : BitVec 32)) :
    run (Functions.encdec_backwards 0x6980d193) state =
      .ok (.REV8 (.Regidx 1, .Regidx 3)) state := by
  have isa := Airbender.Reference.RiscV.Sail.read_register configured
  repeat' first
    | (with_unfolding_all rfl)
    | (with_unfolding_all conv_lhs => arg 1; whnf
       rw [@run_read_cont (inferInstance : _root_.Sail.ArchSem.Arch)
         _ _ Register.misa _ _ _ isa])

end Tests.SailDecoder
