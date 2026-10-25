import GKRProtocol.UnifiedSpecialParts.Column2.Chunk0.Part2
import GKRProtocol.UnifiedSpecialParts.Column2.Chunk0.Part3

namespace Airbender.Compiler.UnifiedSpecialLengths.Column2.Chunk0
open Airbender
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

open Airbender.Compiler.UnifiedSpecialChunks.Column2.Chunk0

noncomputable def part1 : List Setup.Block := [source16, source17, source18, source19, source20, source21, source22, source23, source24, source25, source26, source27, source28, source29, source30, source31]

theorem sourceLength16 : source16.length = 32512 := length16.symm.trans (by rfl)

theorem sourceLength17 : source17.length = 257 := length17.symm.trans (by rfl)

theorem sourceLength18 : source18.length = 255 := length18.symm.trans (by rfl)

theorem sourceLength19 : source19.length = 256 := length19.symm.trans (by rfl)

theorem sourceLength20 : source20.length = 256 := length20.symm.trans (by rfl)

theorem sourceLength21 : source21.length = 256 := length21.symm.trans (by rfl)

theorem sourceLength22 : source22.length = 256 := length22.symm.trans (by rfl)

theorem sourceLength23 : source23.length = 256 := length23.symm.trans (by rfl)

theorem sourceLength24 : source24.length = 256 := length24.symm.trans (by rfl)

theorem sourceLength25 : source25.length = 256 := length25.symm.trans (by rfl)

theorem sourceLength26 : source26.length = 256 := length26.symm.trans (by rfl)

theorem sourceLength27 : source27.length = 256 := length27.symm.trans (by rfl)

theorem sourceLength28 : source28.length = 256 := length28.symm.trans (by rfl)

theorem sourceLength29 : source29.length = 256 := length29.symm.trans (by rfl)

theorem sourceLength30 : source30.length = 256 := length30.symm.trans (by rfl)

theorem sourceLength31 : source31.length = 256 := length31.symm.trans (by rfl)

theorem partLength1 : (part1.map Setup.Block.length).sum = 36352 := by
  simp only [part1, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, sourceLength16, sourceLength17, sourceLength18, sourceLength19, sourceLength20, sourceLength21, sourceLength22, sourceLength23, sourceLength24, sourceLength25, sourceLength26, sourceLength27, sourceLength28, sourceLength29, sourceLength30, sourceLength31]; rfl

end Airbender.Compiler.UnifiedSpecialLengths.Column2.Chunk0
