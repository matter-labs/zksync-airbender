import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column5.Chunk191.Part10
import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column5.Chunk191.Part11

namespace Airbender.Compiler.UnifiedSpecialLengths.Column5.Chunk191
open Airbender
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

open Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk191

noncomputable def part5 : List Setup.Block := [source24528, source24529, source24530, source24531, source24532, source24533, source24534, source24535, source24536, source24537, source24538, source24539, source24540, source24541, source24542, source24543]

theorem sourceLength24528 : source24528.length = 2 := length24528.symm.trans (by rfl)

theorem sourceLength24529 : source24529.length = 6 := length24529.symm.trans (by rfl)

theorem sourceLength24530 : source24530.length = 2 := length24530.symm.trans (by rfl)

theorem sourceLength24531 : source24531.length = 6 := length24531.symm.trans (by rfl)

theorem sourceLength24532 : source24532.length = 2 := length24532.symm.trans (by rfl)

theorem sourceLength24533 : source24533.length = 6 := length24533.symm.trans (by rfl)

theorem sourceLength24534 : source24534.length = 2 := length24534.symm.trans (by rfl)

theorem sourceLength24535 : source24535.length = 6 := length24535.symm.trans (by rfl)

theorem sourceLength24536 : source24536.length = 2 := length24536.symm.trans (by rfl)

theorem sourceLength24537 : source24537.length = 6 := length24537.symm.trans (by rfl)

theorem sourceLength24538 : source24538.length = 2 := length24538.symm.trans (by rfl)

theorem sourceLength24539 : source24539.length = 6 := length24539.symm.trans (by rfl)

theorem sourceLength24540 : source24540.length = 1 := length24540.symm.trans (by rfl)

theorem sourceLength24541 : source24541.length = 72 := length24541.symm.trans (by rfl)

theorem sourceLength24542 : source24542.length = 1114125 := length24542.symm.trans (by rfl)

theorem sourceLength24543 : source24543.length = 3840 := length24543.symm.trans (by rfl)

theorem partLength5 : (part5.map Setup.Block.length).sum = 1118086 := by
  simp only [part5, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, sourceLength24528, sourceLength24529, sourceLength24530, sourceLength24531, sourceLength24532, sourceLength24533, sourceLength24534, sourceLength24535, sourceLength24536, sourceLength24537, sourceLength24538, sourceLength24539, sourceLength24540, sourceLength24541, sourceLength24542, sourceLength24543]; rfl

end Airbender.Compiler.UnifiedSpecialLengths.Column5.Chunk191
