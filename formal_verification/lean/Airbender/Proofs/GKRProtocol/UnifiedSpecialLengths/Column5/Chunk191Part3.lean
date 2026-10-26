import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column5.Chunk191.Part6
import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column5.Chunk191.Part7

namespace Airbender.Compiler.UnifiedSpecialLengths.Column5.Chunk191
open Airbender
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

open Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk191

noncomputable def part3 : List Setup.Block := [source24496, source24497, source24498, source24499, source24500, source24501, source24502, source24503, source24504, source24505, source24506, source24507, source24508, source24509, source24510, source24511]

theorem sourceLength24496 : source24496.length = 6 := length24496.symm.trans (by rfl)

theorem sourceLength24497 : source24497.length = 2 := length24497.symm.trans (by rfl)

theorem sourceLength24498 : source24498.length = 6 := length24498.symm.trans (by rfl)

theorem sourceLength24499 : source24499.length = 2 := length24499.symm.trans (by rfl)

theorem sourceLength24500 : source24500.length = 6 := length24500.symm.trans (by rfl)

theorem sourceLength24501 : source24501.length = 2 := length24501.symm.trans (by rfl)

theorem sourceLength24502 : source24502.length = 6 := length24502.symm.trans (by rfl)

theorem sourceLength24503 : source24503.length = 2 := length24503.symm.trans (by rfl)

theorem sourceLength24504 : source24504.length = 6 := length24504.symm.trans (by rfl)

theorem sourceLength24505 : source24505.length = 2 := length24505.symm.trans (by rfl)

theorem sourceLength24506 : source24506.length = 6 := length24506.symm.trans (by rfl)

theorem sourceLength24507 : source24507.length = 2 := length24507.symm.trans (by rfl)

theorem sourceLength24508 : source24508.length = 6 := length24508.symm.trans (by rfl)

theorem sourceLength24509 : source24509.length = 1 := length24509.symm.trans (by rfl)

theorem sourceLength24510 : source24510.length = 72 := length24510.symm.trans (by rfl)

theorem sourceLength24511 : source24511.length = 71 := length24511.symm.trans (by rfl)

theorem partLength3 : (part3.map Setup.Block.length).sum = 198 := by
  simp only [part3, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, sourceLength24496, sourceLength24497, sourceLength24498, sourceLength24499, sourceLength24500, sourceLength24501, sourceLength24502, sourceLength24503, sourceLength24504, sourceLength24505, sourceLength24506, sourceLength24507, sourceLength24508, sourceLength24509, sourceLength24510, sourceLength24511]; rfl

end Airbender.Compiler.UnifiedSpecialLengths.Column5.Chunk191
