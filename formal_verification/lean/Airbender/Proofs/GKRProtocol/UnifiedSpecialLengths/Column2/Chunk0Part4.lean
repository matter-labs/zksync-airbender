import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column2.Chunk0.Part8
import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column2.Chunk0.Part9

namespace Airbender.Compiler.UnifiedSpecialLengths.Column2.Chunk0
open Airbender
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

open Airbender.Compiler.UnifiedSpecialChunks.Column2.Chunk0

noncomputable def part4 : List Setup.Block := [source64, source65, source66, source67, source68, source69, source70, source71, source72, source73, source74, source75, source76, source77, source78, source79]

theorem sourceLength64 : source64.length = 256 := length64.symm.trans (by rfl)

theorem sourceLength65 : source65.length = 256 := length65.symm.trans (by rfl)

theorem sourceLength66 : source66.length = 256 := length66.symm.trans (by rfl)

theorem sourceLength67 : source67.length = 256 := length67.symm.trans (by rfl)

theorem sourceLength68 : source68.length = 256 := length68.symm.trans (by rfl)

theorem sourceLength69 : source69.length = 256 := length69.symm.trans (by rfl)

theorem sourceLength70 : source70.length = 256 := length70.symm.trans (by rfl)

theorem sourceLength71 : source71.length = 256 := length71.symm.trans (by rfl)

theorem sourceLength72 : source72.length = 256 := length72.symm.trans (by rfl)

theorem sourceLength73 : source73.length = 256 := length73.symm.trans (by rfl)

theorem sourceLength74 : source74.length = 256 := length74.symm.trans (by rfl)

theorem sourceLength75 : source75.length = 256 := length75.symm.trans (by rfl)

theorem sourceLength76 : source76.length = 256 := length76.symm.trans (by rfl)

theorem sourceLength77 : source77.length = 256 := length77.symm.trans (by rfl)

theorem sourceLength78 : source78.length = 256 := length78.symm.trans (by rfl)

theorem sourceLength79 : source79.length = 256 := length79.symm.trans (by rfl)

theorem partLength4 : (part4.map Setup.Block.length).sum = 4096 := by
  simp only [part4, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, sourceLength64, sourceLength65, sourceLength66, sourceLength67, sourceLength68, sourceLength69, sourceLength70, sourceLength71, sourceLength72, sourceLength73, sourceLength74, sourceLength75, sourceLength76, sourceLength77, sourceLength78, sourceLength79]; rfl

end Airbender.Compiler.UnifiedSpecialLengths.Column2.Chunk0
