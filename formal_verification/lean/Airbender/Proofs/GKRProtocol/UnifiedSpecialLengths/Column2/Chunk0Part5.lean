import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column2.Chunk0.Part10
import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column2.Chunk0.Part11

namespace Airbender.Compiler.UnifiedSpecialLengths.Column2.Chunk0
open Airbender
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

open Airbender.Compiler.UnifiedSpecialChunks.Column2.Chunk0

noncomputable def part5 : List Setup.Block := [source80, source81, source82, source83, source84, source85, source86, source87, source88, source89, source90, source91, source92, source93, source94, source95]

theorem sourceLength80 : source80.length = 256 := length80.symm.trans (by rfl)

theorem sourceLength81 : source81.length = 256 := length81.symm.trans (by rfl)

theorem sourceLength82 : source82.length = 64 := length82.symm.trans (by rfl)

theorem sourceLength83 : source83.length = 64 := length83.symm.trans (by rfl)

theorem sourceLength84 : source84.length = 64 := length84.symm.trans (by rfl)

theorem sourceLength85 : source85.length = 64 := length85.symm.trans (by rfl)

theorem sourceLength86 : source86.length = 64 := length86.symm.trans (by rfl)

theorem sourceLength87 : source87.length = 64 := length87.symm.trans (by rfl)

theorem sourceLength88 : source88.length = 64 := length88.symm.trans (by rfl)

theorem sourceLength89 : source89.length = 64 := length89.symm.trans (by rfl)

theorem sourceLength90 : source90.length = 64 := length90.symm.trans (by rfl)

theorem sourceLength91 : source91.length = 64 := length91.symm.trans (by rfl)

theorem sourceLength92 : source92.length = 64 := length92.symm.trans (by rfl)

theorem sourceLength93 : source93.length = 64 := length93.symm.trans (by rfl)

theorem sourceLength94 : source94.length = 64 := length94.symm.trans (by rfl)

theorem sourceLength95 : source95.length = 64 := length95.symm.trans (by rfl)

theorem partLength5 : (part5.map Setup.Block.length).sum = 1408 := by
  simp only [part5, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, sourceLength80, sourceLength81, sourceLength82, sourceLength83, sourceLength84, sourceLength85, sourceLength86, sourceLength87, sourceLength88, sourceLength89, sourceLength90, sourceLength91, sourceLength92, sourceLength93, sourceLength94, sourceLength95]; rfl

end Airbender.Compiler.UnifiedSpecialLengths.Column2.Chunk0
