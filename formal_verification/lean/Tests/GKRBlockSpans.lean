import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Foundation

namespace Tests.GKRBlockSpans
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def actualSource : Setup.Block := Airbender.Compiler.UnifiedPrefixNative.Column1.original.get ⟨14, by decide +kernel⟩

column_blocks_part actualTargetParts from (UnifiedReduced.Setup.nativeRotate16Data.columns[(1 : Nat)]) start 2 stop 3

noncomputable def actualTarget : Setup.Block := actualTargetParts.get ⟨0, by decide +kernel⟩

theorem actual_boundary_matches : finiteBlockSpanRangeCheck actualSource actualTarget 65280 0 1 = true := by decide +kernel

theorem changed_phase_rejected : finiteBlockSpanRangeCheck actualSource actualTarget 65281 0 1 = false := by decide +kernel

theorem target_overrun_rejected : finiteBlockSpanRangeCheck actualSource actualTarget 65280 250 6 = false := by decide +kernel

theorem oversized_certificate_rejected : finiteBlockSpanRangeCheck actualSource actualTarget 65280 0 33 = false := by decide +kernel

end Tests.GKRBlockSpans
