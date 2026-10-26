import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column2.Chunk0.Part14
import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column2.Chunk0.Part15

namespace Airbender.Compiler.UnifiedSpecialLengths.Column2.Chunk0
open Airbender
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

open Airbender.Compiler.UnifiedSpecialChunks.Column2.Chunk0

noncomputable def part7 : List Setup.Block := [source112, source113, source114, source115, source116, source117, source118, source119, source120, source121, source122, source123, source124, source125, source126, source127]

theorem sourceLength112 : source112.length = 64 := length112.symm.trans (by rfl)

theorem sourceLength113 : source113.length = 64 := length113.symm.trans (by rfl)

theorem sourceLength114 : source114.length = 64 := length114.symm.trans (by rfl)

theorem sourceLength115 : source115.length = 64 := length115.symm.trans (by rfl)

theorem sourceLength116 : source116.length = 64 := length116.symm.trans (by rfl)

theorem sourceLength117 : source117.length = 64 := length117.symm.trans (by rfl)

theorem sourceLength118 : source118.length = 64 := length118.symm.trans (by rfl)

theorem sourceLength119 : source119.length = 64 := length119.symm.trans (by rfl)

theorem sourceLength120 : source120.length = 64 := length120.symm.trans (by rfl)

theorem sourceLength121 : source121.length = 64 := length121.symm.trans (by rfl)

theorem sourceLength122 : source122.length = 64 := length122.symm.trans (by rfl)

theorem sourceLength123 : source123.length = 64 := length123.symm.trans (by rfl)

theorem sourceLength124 : source124.length = 64 := length124.symm.trans (by rfl)

theorem sourceLength125 : source125.length = 64 := length125.symm.trans (by rfl)

theorem sourceLength126 : source126.length = 64 := length126.symm.trans (by rfl)

theorem sourceLength127 : source127.length = 64 := length127.symm.trans (by rfl)

theorem partLength7 : (part7.map Setup.Block.length).sum = 1024 := by
  simp only [part7, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, sourceLength112, sourceLength113, sourceLength114, sourceLength115, sourceLength116, sourceLength117, sourceLength118, sourceLength119, sourceLength120, sourceLength121, sourceLength122, sourceLength123, sourceLength124, sourceLength125, sourceLength126, sourceLength127]; rfl

end Airbender.Compiler.UnifiedSpecialLengths.Column2.Chunk0
