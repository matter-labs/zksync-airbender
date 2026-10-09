import Airbender.Review.Sail

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

/-- Current generation gap: Zbb calls the `Ext_B` enablement clause defined
    in upstream Zba, which the selected slice has not loaded yet. -/
theorem rev8_missing_dependency (state : Airbender.Reference.RiscV.Sail.State) :
    ∃ error, run (Functions.encdec_backwards 0x6980d193) state = .error error state := by
  refine ⟨_root_.Sail.Error.Assertion
    "Pattern match failure at /private/tmp/airbender-sail-integration/model/model/extensions/Zicsr/zicsr_insts.sail:12.0-12.69", ?_⟩
  with_unfolding_all rfl

end Tests.SailDecoder
