import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column2.Chunk0.Part0
import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column2.Chunk0.Part1

namespace Airbender.Compiler.UnifiedSpecialLengths.Column2.Chunk0
open Airbender
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

open Airbender.Compiler.UnifiedSpecialChunks.Column2.Chunk0

noncomputable def part0 : List Setup.Block := [source0, source1, source2, source3, source4, source5, source6, source7, source8, source9, source10, source11, source12, source13, source14, source15]

theorem sourceLength0 : source0.length = 131077 := length0.symm.trans (by rfl)

theorem sourceLength1 : source1.length = 65532 := length1.symm.trans (by rfl)

theorem sourceLength2 : source2.length = 66048 := length2.symm.trans (by rfl)

theorem sourceLength3 : source3.length = 7936 := length3.symm.trans (by rfl)

theorem sourceLength4 : source4.length = 8192 := length4.symm.trans (by rfl)

theorem sourceLength5 : source5.length = 8192 := length5.symm.trans (by rfl)

theorem sourceLength6 : source6.length = 8192 := length6.symm.trans (by rfl)

theorem sourceLength7 : source7.length = 8192 := length7.symm.trans (by rfl)

theorem sourceLength8 : source8.length = 8192 := length8.symm.trans (by rfl)

theorem sourceLength9 : source9.length = 8192 := length9.symm.trans (by rfl)

theorem sourceLength10 : source10.length = 8192 := length10.symm.trans (by rfl)

theorem sourceLength11 : source11.length = 262144 := length11.symm.trans (by rfl)

theorem sourceLength12 : source12.length = 4 := length12.symm.trans (by rfl)

theorem sourceLength13 : source13.length = 1245308 := length13.symm.trans (by rfl)

theorem sourceLength14 : source14.length = 32512 := length14.symm.trans (by rfl)

theorem sourceLength15 : source15.length = 256 := length15.symm.trans (by rfl)

theorem partLength0 : (part0.map Setup.Block.length).sum = 1868161 := by
  simp only [part0, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, sourceLength0, sourceLength1, sourceLength2, sourceLength3, sourceLength4, sourceLength5, sourceLength6, sourceLength7, sourceLength8, sourceLength9, sourceLength10, sourceLength11, sourceLength12, sourceLength13, sourceLength14, sourceLength15]; rfl

end Airbender.Compiler.UnifiedSpecialLengths.Column2.Chunk0
