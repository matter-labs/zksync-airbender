import Slop.KeccakSplit.RowCommon
import Slop.Arithmetic.Word
import Mathlib.Tactic.FinCases
import Slop.Arithmetic.Bytes
import Slop.KernelRfl
import Slop.Trace.InitialImage

/- Sail-level steps shared by the three split-worker `executes` proofs (ported from
   PR #585's *_call_control_binding, *_call_pointer_binding, *_lane_port_half and
   *_call_executes). -/

namespace Airbender.Keccak.Split.RowProofs
open Airbender.Trace Airbender.Trace.Proofs Airbender.Arithmetic
set_option warningAsError true

/-- Two bounded words split a lane into its halves. -/
theorem half_words {lo hi : Word} (bl : lo.Bounded) (bh : hi.Bounded) (high : Bool) :
    Call.half (lo.value + 2 ^ 32 * hi.value) high = (if high then hi else lo).toBitVec := by
  have l := Word.value_lt bl
  have h := Word.value_lt bh
  simp only [wordModulus] at l h
  cases high <;> simp only [Call.half, Bool.false_eq_true, ↓reduceIte, Word.toBitVec]
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    omega
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    rw [show (lo.value + 2 ^ 32 * hi.value) / 2 ^ 32 = hi.value by omega]

theorem lane_words_bound {lo hi : Word} (bl : lo.Bounded) (bh : hi.Bounded) :
    lo.value + 2 ^ 32 * hi.value < 2 ^ 64 := by
  have l := Word.value_lt bl
  have h := Word.value_lt bh
  simp only [wordModulus] at l h
  omega

end Airbender.Keccak.Split.RowProofs
