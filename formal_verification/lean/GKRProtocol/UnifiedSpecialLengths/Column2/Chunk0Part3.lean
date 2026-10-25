import GKRProtocol.UnifiedSpecialParts.Column2.Chunk0.Part6
import GKRProtocol.UnifiedSpecialParts.Column2.Chunk0.Part7

namespace Airbender.Compiler.UnifiedSpecialLengths.Column2.Chunk0
open Airbender
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

open Airbender.Compiler.UnifiedSpecialChunks.Column2.Chunk0

noncomputable def part3 : List Setup.Block := [source48, source49, source50, source51, source52, source53, source54, source55, source56, source57, source58, source59, source60, source61, source62, source63]

theorem sourceLength48 : source48.length = 256 := length48.symm.trans (by rfl)

theorem sourceLength49 : source49.length = 256 := length49.symm.trans (by rfl)

theorem sourceLength50 : source50.length = 256 := length50.symm.trans (by rfl)

theorem sourceLength51 : source51.length = 256 := length51.symm.trans (by rfl)

theorem sourceLength52 : source52.length = 256 := length52.symm.trans (by rfl)

theorem sourceLength53 : source53.length = 256 := length53.symm.trans (by rfl)

theorem sourceLength54 : source54.length = 256 := length54.symm.trans (by rfl)

theorem sourceLength55 : source55.length = 256 := length55.symm.trans (by rfl)

theorem sourceLength56 : source56.length = 256 := length56.symm.trans (by rfl)

theorem sourceLength57 : source57.length = 256 := length57.symm.trans (by rfl)

theorem sourceLength58 : source58.length = 256 := length58.symm.trans (by rfl)

theorem sourceLength59 : source59.length = 256 := length59.symm.trans (by rfl)

theorem sourceLength60 : source60.length = 256 := length60.symm.trans (by rfl)

theorem sourceLength61 : source61.length = 256 := length61.symm.trans (by rfl)

theorem sourceLength62 : source62.length = 256 := length62.symm.trans (by rfl)

theorem sourceLength63 : source63.length = 256 := length63.symm.trans (by rfl)

theorem partLength3 : (part3.map Setup.Block.length).sum = 4096 := by
  simp only [part3, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, sourceLength48, sourceLength49, sourceLength50, sourceLength51, sourceLength52, sourceLength53, sourceLength54, sourceLength55, sourceLength56, sourceLength57, sourceLength58, sourceLength59, sourceLength60, sourceLength61, sourceLength62, sourceLength63]; rfl

end Airbender.Compiler.UnifiedSpecialLengths.Column2.Chunk0
