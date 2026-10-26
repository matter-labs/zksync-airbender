import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column5.Chunk191.Part2
import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column5.Chunk191.Part3

namespace Airbender.Compiler.UnifiedSpecialLengths.Column5.Chunk191
open Airbender
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

open Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk191

noncomputable def part1 : List Setup.Block := [source24464, source24465, source24466, source24467, source24468, source24469, source24470, source24471, source24472, source24473, source24474, source24475, source24476, source24477, source24478, source24479]

theorem sourceLength24464 : source24464.length = 2 := length24464.symm.trans (by rfl)

theorem sourceLength24465 : source24465.length = 6 := length24465.symm.trans (by rfl)

theorem sourceLength24466 : source24466.length = 2 := length24466.symm.trans (by rfl)

theorem sourceLength24467 : source24467.length = 6 := length24467.symm.trans (by rfl)

theorem sourceLength24468 : source24468.length = 2 := length24468.symm.trans (by rfl)

theorem sourceLength24469 : source24469.length = 6 := length24469.symm.trans (by rfl)

theorem sourceLength24470 : source24470.length = 2 := length24470.symm.trans (by rfl)

theorem sourceLength24471 : source24471.length = 6 := length24471.symm.trans (by rfl)

theorem sourceLength24472 : source24472.length = 2 := length24472.symm.trans (by rfl)

theorem sourceLength24473 : source24473.length = 6 := length24473.symm.trans (by rfl)

theorem sourceLength24474 : source24474.length = 2 := length24474.symm.trans (by rfl)

theorem sourceLength24475 : source24475.length = 6 := length24475.symm.trans (by rfl)

theorem sourceLength24476 : source24476.length = 2 := length24476.symm.trans (by rfl)

theorem sourceLength24477 : source24477.length = 6 := length24477.symm.trans (by rfl)

theorem sourceLength24478 : source24478.length = 2 := length24478.symm.trans (by rfl)

theorem sourceLength24479 : source24479.length = 6 := length24479.symm.trans (by rfl)

theorem partLength1 : (part1.map Setup.Block.length).sum = 64 := by
  simp only [part1, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, sourceLength24464, sourceLength24465, sourceLength24466, sourceLength24467, sourceLength24468, sourceLength24469, sourceLength24470, sourceLength24471, sourceLength24472, sourceLength24473, sourceLength24474, sourceLength24475, sourceLength24476, sourceLength24477, sourceLength24478, sourceLength24479]; rfl

end Airbender.Compiler.UnifiedSpecialLengths.Column5.Chunk191
