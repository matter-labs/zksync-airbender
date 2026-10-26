import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column5.Chunk191.Part8
import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column5.Chunk191.Part9

namespace Airbender.Compiler.UnifiedSpecialLengths.Column5.Chunk191
open Airbender
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

open Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk191

noncomputable def part4 : List Setup.Block := [source24512, source24513, source24514, source24515, source24516, source24517, source24518, source24519, source24520, source24521, source24522, source24523, source24524, source24525, source24526, source24527]

theorem sourceLength24512 : source24512.length = 2 := length24512.symm.trans (by rfl)

theorem sourceLength24513 : source24513.length = 6 := length24513.symm.trans (by rfl)

theorem sourceLength24514 : source24514.length = 2 := length24514.symm.trans (by rfl)

theorem sourceLength24515 : source24515.length = 6 := length24515.symm.trans (by rfl)

theorem sourceLength24516 : source24516.length = 2 := length24516.symm.trans (by rfl)

theorem sourceLength24517 : source24517.length = 6 := length24517.symm.trans (by rfl)

theorem sourceLength24518 : source24518.length = 2 := length24518.symm.trans (by rfl)

theorem sourceLength24519 : source24519.length = 6 := length24519.symm.trans (by rfl)

theorem sourceLength24520 : source24520.length = 2 := length24520.symm.trans (by rfl)

theorem sourceLength24521 : source24521.length = 6 := length24521.symm.trans (by rfl)

theorem sourceLength24522 : source24522.length = 2 := length24522.symm.trans (by rfl)

theorem sourceLength24523 : source24523.length = 6 := length24523.symm.trans (by rfl)

theorem sourceLength24524 : source24524.length = 2 := length24524.symm.trans (by rfl)

theorem sourceLength24525 : source24525.length = 6 := length24525.symm.trans (by rfl)

theorem sourceLength24526 : source24526.length = 2 := length24526.symm.trans (by rfl)

theorem sourceLength24527 : source24527.length = 6 := length24527.symm.trans (by rfl)

theorem partLength4 : (part4.map Setup.Block.length).sum = 64 := by
  simp only [part4, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, sourceLength24512, sourceLength24513, sourceLength24514, sourceLength24515, sourceLength24516, sourceLength24517, sourceLength24518, sourceLength24519, sourceLength24520, sourceLength24521, sourceLength24522, sourceLength24523, sourceLength24524, sourceLength24525, sourceLength24526, sourceLength24527]; rfl

end Airbender.Compiler.UnifiedSpecialLengths.Column5.Chunk191
