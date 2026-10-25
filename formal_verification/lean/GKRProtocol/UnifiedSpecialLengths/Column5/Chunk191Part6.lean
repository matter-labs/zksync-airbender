import GKRProtocol.UnifiedSpecialParts.Column5.Chunk191.Part12
import GKRProtocol.UnifiedSpecialParts.Column5.Chunk191.Part13

namespace Airbender.Compiler.UnifiedSpecialLengths.Column5.Chunk191
open Airbender
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

open Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk191

noncomputable def part6 : List Setup.Block := [source24544, source24545, source24546, source24547, source24548, source24549, source24550, source24551, source24552, source24553, source24554, source24555, source24556, source24557, source24558, source24559]

theorem sourceLength24544 : source24544.length = 240 := length24544.symm.trans (by rfl)

theorem sourceLength24545 : source24545.length = 4096 := length24545.symm.trans (by rfl)

theorem sourceLength24546 : source24546.length = 4096 := length24546.symm.trans (by rfl)

theorem sourceLength24547 : source24547.length = 4096 := length24547.symm.trans (by rfl)

theorem sourceLength24548 : source24548.length = 4096 := length24548.symm.trans (by rfl)

theorem sourceLength24549 : source24549.length = 4096 := length24549.symm.trans (by rfl)

theorem sourceLength24550 : source24550.length = 4096 := length24550.symm.trans (by rfl)

theorem sourceLength24551 : source24551.length = 4096 := length24551.symm.trans (by rfl)

theorem sourceLength24552 : source24552.length = 4096 := length24552.symm.trans (by rfl)

theorem sourceLength24553 : source24553.length = 4096 := length24553.symm.trans (by rfl)

theorem sourceLength24554 : source24554.length = 4096 := length24554.symm.trans (by rfl)

theorem sourceLength24555 : source24555.length = 4096 := length24555.symm.trans (by rfl)

theorem sourceLength24556 : source24556.length = 4096 := length24556.symm.trans (by rfl)

theorem sourceLength24557 : source24557.length = 4096 := length24557.symm.trans (by rfl)

theorem sourceLength24558 : source24558.length = 4096 := length24558.symm.trans (by rfl)

theorem sourceLength24559 : source24559.length = 4096 := length24559.symm.trans (by rfl)

theorem partLength6 : (part6.map Setup.Block.length).sum = 61680 := by
  simp only [part6, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, sourceLength24544, sourceLength24545, sourceLength24546, sourceLength24547, sourceLength24548, sourceLength24549, sourceLength24550, sourceLength24551, sourceLength24552, sourceLength24553, sourceLength24554, sourceLength24555, sourceLength24556, sourceLength24557, sourceLength24558, sourceLength24559]; rfl

end Airbender.Compiler.UnifiedSpecialLengths.Column5.Chunk191
