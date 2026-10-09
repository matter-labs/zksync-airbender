import Airbender.Proofs.Trace.MemoryPorts
import Airbender.Proofs.Trace.SailHistory

namespace Airbender.Trace.Proofs
open Arithmetic

/-- Lookup-bounded native bytes are the bytes of the word read through the
    existing memory history. No separate source-word interpretation is assumed. -/
theorem byte_port_bytes {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    {w : Nat → ZMod p} (columns : Vector Nat 4)
    (bounds : ∀ i : Fin 4, (w columns[i]).val < 256) :
    ∀ i : Fin 4, w columns[i] =
      ((memoryWord ((WordColumns.u8 columns).code w)).extractLsb' (8 * i.val) 8).toNat := by
  rw [byte_port_code hp columns bounds]
  have b0 : (w columns[0]).val < 256 := bounds 0
  have b1 : (w columns[1]).val < 256 := bounds 1
  have b2 : (w columns[2]).val < 256 := bounds 2
  have b3 : (w columns[3]).val < 256 := bounds 3
  intro i
  have value : ((memoryWord (Nat.pair
      ((w columns[0]).val + 256 * (w columns[1]).val)
      ((w columns[2]).val + 256 * (w columns[3]).val))).extractLsb' (8 * i.val) 8).toNat =
      (w columns[i]).val := by
    fin_cases i
    all_goals
      first
        | change _ = (w columns[0]).val
        | change _ = (w columns[1]).val
        | change _ = (w columns[2]).val
        | change _ = (w columns[3]).val
      simp only [memoryWord, Nat.unpair_pair, Word.toBitVec, Word.value,
        BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      norm_num only [limbBase, Nat.reducePow, Nat.div_one]
      omega
  rw [value]
  simp

end Airbender.Trace.Proofs
