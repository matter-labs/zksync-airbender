import Human.Helpers.Core.Sail
import Slop.Sail.PC
import Slop.Sail.ResetRun

namespace Tests.SailDecoder
open SailRV32
open Airbender.Reference.Sail Airbender.Reference.RiscV.Sail

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option warningAsError true

-- These check the emitted upstream decoder, including the encoded immediates, on every `Configured` state:
-- the decoder only reads configuration registers (`ConfigReads`) and decodes on the reset state; both are
-- kernel reduction proofs (`kernel_rfl`), not evaluation-based proof shortcuts.
theorem add {state : Airbender.Reference.RiscV.Sail.State} (configured : Configured state) :
    run (Functions.encdec_backwards 0x002081b3) state =
      .ok (.RTYPE (.Regidx 2, .Regidx 1, .Regidx 3, .ADD)) state :=
  decode_configured configured (by kernel_rfl) (after := Configuration.resetState) (by kernel_rfl)

theorem addi {state : Airbender.Reference.RiscV.Sail.State} (configured : Configured state) :
    run (Functions.encdec_backwards 0xfff08113) state =
      .ok (.ITYPE (0xfff, .Regidx 1, .Regidx 2, .ADDI)) state :=
  decode_configured configured (by kernel_rfl) (after := Configuration.resetState) (by kernel_rfl)

theorem sub {state : Airbender.Reference.RiscV.Sail.State} (configured : Configured state) :
    run (Functions.encdec_backwards 0x402081b3) state =
      .ok (.RTYPE (.Regidx 2, .Regidx 1, .Regidx 3, .SUB)) state :=
  decode_configured configured (by kernel_rfl) (after := Configuration.resetState) (by kernel_rfl)

theorem lui {state : Airbender.Reference.RiscV.Sail.State} (configured : Configured state) :
    run (Functions.encdec_backwards 0x12345137) state =
      .ok (.UTYPE (0x12345, .Regidx 2, .LUI)) state :=
  decode_configured configured (by kernel_rfl) (after := Configuration.resetState) (by kernel_rfl)

theorem auipc {state : Airbender.Reference.RiscV.Sail.State} (configured : Configured state) :
    run (Functions.encdec_backwards 0x12345117) state =
      .ok (.UTYPE (0x12345, .Regidx 2, .AUIPC)) state :=
  decode_configured configured (by kernel_rfl) (after := Configuration.resetState) (by kernel_rfl)

theorem lw {state : Airbender.Reference.RiscV.Sail.State} (configured : Configured state) :
    run (Functions.encdec_backwards 0x0040a103) state =
      .ok (.LOAD (4, .Regidx 1, .Regidx 2, false, 4)) state :=
  decode_configured configured (by kernel_rfl) (after := Configuration.resetState) (by kernel_rfl)

theorem sw {state : Airbender.Reference.RiscV.Sail.State} (configured : Configured state) :
    run (Functions.encdec_backwards 0x0020a223) state =
      .ok (.STORE (4, .Regidx 2, .Regidx 1, 4)) state :=
  decode_configured configured (by kernel_rfl) (after := Configuration.resetState) (by kernel_rfl)

/-- REV8 decodes although misa (RV32 I + M) does not enable B: the configuration supports Zbkb, which also
    provides REV8. -/
theorem rev8 {state : Airbender.Reference.RiscV.Sail.State} (configured : Configured state) :
    run (Functions.encdec_backwards 0x6980d193) state =
      .ok (.REV8 (.Regidx 1, .Regidx 3)) state :=
  decode_configured configured (by kernel_rfl) (after := Configuration.resetState) (by kernel_rfl)

end Tests.SailDecoder
