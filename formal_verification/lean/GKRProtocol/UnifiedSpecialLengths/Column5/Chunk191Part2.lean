import GKRProtocol.UnifiedSpecialParts.Column5.Chunk191.Part4
import GKRProtocol.UnifiedSpecialParts.Column5.Chunk191.Part5

namespace Airbender.Compiler.UnifiedSpecialLengths.Column5.Chunk191
open Airbender
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

open Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk191

noncomputable def part2 : List Setup.Block := [source24480, source24481, source24482, source24483, source24484, source24485, source24486, source24487, source24488, source24489, source24490, source24491, source24492, source24493, source24494, source24495]

theorem sourceLength24480 : source24480.length = 1 := length24480.symm.trans (by rfl)

theorem sourceLength24481 : source24481.length = 72 := length24481.symm.trans (by rfl)

theorem sourceLength24482 : source24482.length = 79 := length24482.symm.trans (by rfl)

theorem sourceLength24483 : source24483.length = 2 := length24483.symm.trans (by rfl)

theorem sourceLength24484 : source24484.length = 6 := length24484.symm.trans (by rfl)

theorem sourceLength24485 : source24485.length = 2 := length24485.symm.trans (by rfl)

theorem sourceLength24486 : source24486.length = 6 := length24486.symm.trans (by rfl)

theorem sourceLength24487 : source24487.length = 2 := length24487.symm.trans (by rfl)

theorem sourceLength24488 : source24488.length = 6 := length24488.symm.trans (by rfl)

theorem sourceLength24489 : source24489.length = 2 := length24489.symm.trans (by rfl)

theorem sourceLength24490 : source24490.length = 6 := length24490.symm.trans (by rfl)

theorem sourceLength24491 : source24491.length = 2 := length24491.symm.trans (by rfl)

theorem sourceLength24492 : source24492.length = 6 := length24492.symm.trans (by rfl)

theorem sourceLength24493 : source24493.length = 2 := length24493.symm.trans (by rfl)

theorem sourceLength24494 : source24494.length = 6 := length24494.symm.trans (by rfl)

theorem sourceLength24495 : source24495.length = 2 := length24495.symm.trans (by rfl)

theorem partLength2 : (part2.map Setup.Block.length).sum = 202 := by
  simp only [part2, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, sourceLength24480, sourceLength24481, sourceLength24482, sourceLength24483, sourceLength24484, sourceLength24485, sourceLength24486, sourceLength24487, sourceLength24488, sourceLength24489, sourceLength24490, sourceLength24491, sourceLength24492, sourceLength24493, sourceLength24494, sourceLength24495]; rfl

end Airbender.Compiler.UnifiedSpecialLengths.Column5.Chunk191
