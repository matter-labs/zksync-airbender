import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column2.Chunk0.Part4
import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column2.Chunk0.Part5

namespace Airbender.Compiler.UnifiedSpecialLengths.Column2.Chunk0
open Airbender
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

open Airbender.Compiler.UnifiedSpecialChunks.Column2.Chunk0

noncomputable def part2 : List Setup.Block := [source32, source33, source34, source35, source36, source37, source38, source39, source40, source41, source42, source43, source44, source45, source46, source47]

theorem sourceLength32 : source32.length = 256 := length32.symm.trans (by rfl)

theorem sourceLength33 : source33.length = 256 := length33.symm.trans (by rfl)

theorem sourceLength34 : source34.length = 256 := length34.symm.trans (by rfl)

theorem sourceLength35 : source35.length = 256 := length35.symm.trans (by rfl)

theorem sourceLength36 : source36.length = 256 := length36.symm.trans (by rfl)

theorem sourceLength37 : source37.length = 256 := length37.symm.trans (by rfl)

theorem sourceLength38 : source38.length = 256 := length38.symm.trans (by rfl)

theorem sourceLength39 : source39.length = 256 := length39.symm.trans (by rfl)

theorem sourceLength40 : source40.length = 256 := length40.symm.trans (by rfl)

theorem sourceLength41 : source41.length = 256 := length41.symm.trans (by rfl)

theorem sourceLength42 : source42.length = 256 := length42.symm.trans (by rfl)

theorem sourceLength43 : source43.length = 256 := length43.symm.trans (by rfl)

theorem sourceLength44 : source44.length = 256 := length44.symm.trans (by rfl)

theorem sourceLength45 : source45.length = 256 := length45.symm.trans (by rfl)

theorem sourceLength46 : source46.length = 256 := length46.symm.trans (by rfl)

theorem sourceLength47 : source47.length = 256 := length47.symm.trans (by rfl)

theorem partLength2 : (part2.map Setup.Block.length).sum = 4096 := by
  simp only [part2, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, sourceLength32, sourceLength33, sourceLength34, sourceLength35, sourceLength36, sourceLength37, sourceLength38, sourceLength39, sourceLength40, sourceLength41, sourceLength42, sourceLength43, sourceLength44, sourceLength45, sourceLength46, sourceLength47]; rfl

end Airbender.Compiler.UnifiedSpecialLengths.Column2.Chunk0
