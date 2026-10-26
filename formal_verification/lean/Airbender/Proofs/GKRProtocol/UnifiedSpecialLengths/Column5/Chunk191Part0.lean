import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column5.Chunk191.Part0
import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column5.Chunk191.Part1

namespace Airbender.Compiler.UnifiedSpecialLengths.Column5.Chunk191
open Airbender
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

open Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk191

noncomputable def part0 : List Setup.Block := [source24448, source24449, source24450, source24451, source24452, source24453, source24454, source24455, source24456, source24457, source24458, source24459, source24460, source24461, source24462, source24463]

theorem sourceLength24448 : source24448.length = 6 := length24448.symm.trans (by rfl)

theorem sourceLength24449 : source24449.length = 1 := length24449.symm.trans (by rfl)

theorem sourceLength24450 : source24450.length = 72 := length24450.symm.trans (by rfl)

theorem sourceLength24451 : source24451.length = 71 := length24451.symm.trans (by rfl)

theorem sourceLength24452 : source24452.length = 2 := length24452.symm.trans (by rfl)

theorem sourceLength24453 : source24453.length = 6 := length24453.symm.trans (by rfl)

theorem sourceLength24454 : source24454.length = 2 := length24454.symm.trans (by rfl)

theorem sourceLength24455 : source24455.length = 6 := length24455.symm.trans (by rfl)

theorem sourceLength24456 : source24456.length = 2 := length24456.symm.trans (by rfl)

theorem sourceLength24457 : source24457.length = 6 := length24457.symm.trans (by rfl)

theorem sourceLength24458 : source24458.length = 2 := length24458.symm.trans (by rfl)

theorem sourceLength24459 : source24459.length = 6 := length24459.symm.trans (by rfl)

theorem sourceLength24460 : source24460.length = 2 := length24460.symm.trans (by rfl)

theorem sourceLength24461 : source24461.length = 6 := length24461.symm.trans (by rfl)

theorem sourceLength24462 : source24462.length = 2 := length24462.symm.trans (by rfl)

theorem sourceLength24463 : source24463.length = 6 := length24463.symm.trans (by rfl)

theorem partLength0 : (part0.map Setup.Block.length).sum = 198 := by
  simp only [part0, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, sourceLength24448, sourceLength24449, sourceLength24450, sourceLength24451, sourceLength24452, sourceLength24453, sourceLength24454, sourceLength24455, sourceLength24456, sourceLength24457, sourceLength24458, sourceLength24459, sourceLength24460, sourceLength24461, sourceLength24462, sourceLength24463]; rfl

end Airbender.Compiler.UnifiedSpecialLengths.Column5.Chunk191
