import Airbender.Proofs.GKRProtocol.DecoderTail.Unified.Rows
import Airbender.Proofs.GKRProtocol.DecoderTail.AddSub.Rows

namespace Tests.GKRDecoderSetup
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem constant_seam_recoded :
    normalizeTinyBlock (.dense #[0, 0, 0]) = .affine 3 0 0 := by decide +kernel

theorem nonconstant_seam_retained :
    normalizeTinyBlock (.dense #[0, 1, 0]) = .dense #[0, 1, 0] := by decide +kernel

theorem changed_constant_rejected :
    finiteBlockSpanRangeCheck (.dense #[0, 0, 0]) (.affine 3 1 0) 0 0 3 = false := by decide +kernel

theorem unified_padding_starts_at_actual_boundary :
    DecoderTail.Unified.Rows.dataTail 1048576 = Vector.replicate 10 0 := by decide +kernel

theorem unified_last_committed_row :
    DecoderTail.Unified.Rows.nativeSetup.imported.data.columns[9].get? 8388607 = some 0 := by
  have actual := DecoderTail.Unified.Column9.decoder_tail_value 6291070
  exact actual

theorem addsub_padding_retains_sentinel :
    (DecoderTail.AddSub.Rows.dataTail 1048576)[0] = babyBearModulus - 1 := by decide +kernel

end Tests.GKRDecoderSetup
