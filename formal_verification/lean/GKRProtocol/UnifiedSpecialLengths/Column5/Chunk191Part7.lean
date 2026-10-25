import GKRProtocol.UnifiedSpecialParts.Column5.Chunk191.Part14
import GKRProtocol.UnifiedSpecialParts.Column5.Chunk191.Part15

namespace Airbender.Compiler.UnifiedSpecialLengths.Column5.Chunk191
open Airbender
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

open Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk191

noncomputable def part7 : List Setup.Block := [source24560, source24561, source24562, source24563, source24564, source24565, source24566, source24567, source24568, source24569, source24570, source24571, source24572, source24573, source24574, source24575]

theorem sourceLength24560 : source24560.length = 256 := length24560.symm.trans (by rfl)

theorem sourceLength24561 : source24561.length = 256 := length24561.symm.trans (by rfl)

theorem sourceLength24562 : source24562.length = 256 := length24562.symm.trans (by rfl)

theorem sourceLength24563 : source24563.length = 256 := length24563.symm.trans (by rfl)

theorem sourceLength24564 : source24564.length = 256 := length24564.symm.trans (by rfl)

theorem sourceLength24565 : source24565.length = 256 := length24565.symm.trans (by rfl)

theorem sourceLength24566 : source24566.length = 256 := length24566.symm.trans (by rfl)

theorem sourceLength24567 : source24567.length = 256 := length24567.symm.trans (by rfl)

theorem sourceLength24568 : source24568.length = 256 := length24568.symm.trans (by rfl)

theorem sourceLength24569 : source24569.length = 256 := length24569.symm.trans (by rfl)

theorem sourceLength24570 : source24570.length = 256 := length24570.symm.trans (by rfl)

theorem sourceLength24571 : source24571.length = 256 := length24571.symm.trans (by rfl)

theorem sourceLength24572 : source24572.length = 256 := length24572.symm.trans (by rfl)

theorem sourceLength24573 : source24573.length = 256 := length24573.symm.trans (by rfl)

theorem sourceLength24574 : source24574.length = 256 := length24574.symm.trans (by rfl)

theorem sourceLength24575 : source24575.length = 256 := length24575.symm.trans (by rfl)

theorem partLength7 : (part7.map Setup.Block.length).sum = 4096 := by
  simp only [part7, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, sourceLength24560, sourceLength24561, sourceLength24562, sourceLength24563, sourceLength24564, sourceLength24565, sourceLength24566, sourceLength24567, sourceLength24568, sourceLength24569, sourceLength24570, sourceLength24571, sourceLength24572, sourceLength24573, sourceLength24574, sourceLength24575]; rfl

end Airbender.Compiler.UnifiedSpecialLengths.Column5.Chunk191
