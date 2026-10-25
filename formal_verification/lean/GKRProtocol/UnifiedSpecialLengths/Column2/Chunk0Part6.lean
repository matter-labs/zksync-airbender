import GKRProtocol.UnifiedSpecialParts.Column2.Chunk0.Part12
import GKRProtocol.UnifiedSpecialParts.Column2.Chunk0.Part13

namespace Airbender.Compiler.UnifiedSpecialLengths.Column2.Chunk0
open Airbender
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

open Airbender.Compiler.UnifiedSpecialChunks.Column2.Chunk0

noncomputable def part6 : List Setup.Block := [source96, source97, source98, source99, source100, source101, source102, source103, source104, source105, source106, source107, source108, source109, source110, source111]

theorem sourceLength96 : source96.length = 64 := length96.symm.trans (by rfl)

theorem sourceLength97 : source97.length = 64 := length97.symm.trans (by rfl)

theorem sourceLength98 : source98.length = 64 := length98.symm.trans (by rfl)

theorem sourceLength99 : source99.length = 64 := length99.symm.trans (by rfl)

theorem sourceLength100 : source100.length = 64 := length100.symm.trans (by rfl)

theorem sourceLength101 : source101.length = 64 := length101.symm.trans (by rfl)

theorem sourceLength102 : source102.length = 64 := length102.symm.trans (by rfl)

theorem sourceLength103 : source103.length = 64 := length103.symm.trans (by rfl)

theorem sourceLength104 : source104.length = 64 := length104.symm.trans (by rfl)

theorem sourceLength105 : source105.length = 64 := length105.symm.trans (by rfl)

theorem sourceLength106 : source106.length = 64 := length106.symm.trans (by rfl)

theorem sourceLength107 : source107.length = 64 := length107.symm.trans (by rfl)

theorem sourceLength108 : source108.length = 64 := length108.symm.trans (by rfl)

theorem sourceLength109 : source109.length = 64 := length109.symm.trans (by rfl)

theorem sourceLength110 : source110.length = 64 := length110.symm.trans (by rfl)

theorem sourceLength111 : source111.length = 64 := length111.symm.trans (by rfl)

theorem partLength6 : (part6.map Setup.Block.length).sum = 1024 := by
  simp only [part6, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, sourceLength96, sourceLength97, sourceLength98, sourceLength99, sourceLength100, sourceLength101, sourceLength102, sourceLength103, sourceLength104, sourceLength105, sourceLength106, sourceLength107, sourceLength108, sourceLength109, sourceLength110, sourceLength111]; rfl

end Airbender.Compiler.UnifiedSpecialLengths.Column2.Chunk0
