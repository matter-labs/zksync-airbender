import Human.Helpers.Memory.InitialImageRV
import Slop.Trace.RVHistory

/-! RV-route writable-store law (piece E1, row level). A changing write (a port with `writeValue = some _`) whose
    address is a RAM cell lies in RV ROM-free RAM: only the word and subword store ports write RAM (their address tag
    is the store flag `w 10`), and `rom_selection` (the circuit rejects stores into ROM) gives `ROM_END ≤ index`.
    Register ports write register cells (tag 0), so they never meet a RAM address. -/

namespace Airbender.Trace.RVWritable
open Arithmetic Trace.Proofs

/-- A RAM cell's address code: tag 1 with the canonical limbs of `index`. -/
theorem ram_code_limbs {p : Nat} (index : BitVec 32) (tag : Nat) (lo hi : ZMod p)
    (same : Nat.pair tag (Nat.pair lo.val hi.val) = (Cell.ram index).addressCode) :
    tag = 1 ∧ lo.val = (Word.ofBitVec index).lo ∧ hi.val = (Word.ofBitVec index).hi := by
  change Nat.pair tag (Nat.pair lo.val hi.val) = Nat.pair 1 (Nat.pair (Word.ofBitVec index).lo (Word.ofBitVec index).hi) at same
  obtain ⟨tagEq, rest⟩ := Nat.pair_eq_pair.mp same
  obtain ⟨loEq, hiEq⟩ := Nat.pair_eq_pair.mp rest
  exact ⟨tagEq, loEq, hiEq⟩

/-- The RAM index's limbs are bounded, and its high limb is the Word high limb of the index. -/
theorem ram_index_rom_bound (index : BitVec 32) (high : 64 ≤ (Word.ofBitVec index).hi) :
    RV.ROM_END ≤ index.toNat := by
  unfold RV.ROM_END
  have small := index.isLt
  dsimp [Word.ofBitVec, limbBase] at high
  omega

end Airbender.Trace.RVWritable
