import Airbender.Proofs.GKRProtocol.UnifiedFixedSpans.Column3.Certificate

set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072

namespace Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0
open Airbender Airbender.Compiler

theorem follows0 : blockTargetsFollow source0 0 target0 :=
  (PackedSetupSpans.check_sound_bound_at Airbender.Compiler.UnifiedFixedSpans.Column3.requests Airbender.Compiler.UnifiedFixedSpans.Column3.checked ⟨0, by decide +kernel⟩ source0 target0 Airbender.Compiler.UnifiedFixedSpans.Column3.source0_binding Airbender.Compiler.UnifiedFixedSpans.Column3.targets0_binding).2

theorem length0 : (target0.map Setup.Block.length).sum = source0.length :=
  (PackedSetupSpans.check_sound_bound_at Airbender.Compiler.UnifiedFixedSpans.Column3.requests Airbender.Compiler.UnifiedFixedSpans.Column3.checked ⟨0, by decide +kernel⟩ source0 target0 Airbender.Compiler.UnifiedFixedSpans.Column3.source0_binding Airbender.Compiler.UnifiedFixedSpans.Column3.targets0_binding).1

end Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0
