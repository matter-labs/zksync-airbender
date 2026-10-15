import Airbender.Review.Circuits.Blake2Round.Call
import Airbender.Proofs.Arithmetic.Word

namespace Airbender.Blake2Round.Call.Proofs
open Arithmetic Trace Reference.RiscV.Sail
set_option warningAsError true

theorem successful_controller {before after : State} (execution : Executes before after) :
    ∃ control : BitVec 32, (Cell.register 12).read before = .ok control before ∧
      8 * 65536 ≤ control.toNat := by
  obtain ⟨input, _, abi, bounded, _, reads, _⟩ := execution
  refine ⟨input.controller.toBitVec, ?_, ?_⟩
  · simpa [cells, Call.reads, values, Fin.getElem_fin] using reads 42
  · have positive : 0 < 2 ^ input.round.val := pow_pos (by decide : 0 < (2 : Nat)) _
    rw [Word.toBitVec_toNat bounded.1, abi.controller]
    dsimp [Word.value, limbBase]
    omega

end Airbender.Blake2Round.Call.Proofs
