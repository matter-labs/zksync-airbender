import Airbender.Proofs.UnifiedReduced.Tables.ImportedWideColumns
import Airbender.Proofs.Tables.PeriodicColumns
import Mathlib.Tactic.FinCases

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

private def keyHead (kind : Fin 3) : Block :=
  if kind.val = 0 then .affine 1 0 0 else .dense (Array.replicate 1 0)
private def cyclicValues : Array Nat := Array.ofFn (fun i : Fin 256 => (1 + i.val) % 256)
private def finalValues : Array Nat := Array.ofFn (fun i : Fin 255 => 1 + i.val)

private theorem head_length (kind : Fin 3) : (keyHead kind).length = 1 := by
  fin_cases kind <;> rfl
private theorem head_value (kind : Fin 3) : (keyHead kind).get? 0 = some 0 := by
  fin_cases kind <;> decide +kernel
private theorem key_shape (kind : Fin 3) : (wideData kind).columns[1] = Column.mk
    #[keyHead kind, .periodic 255 0 cyclicValues, .dense finalValues] := by
  fin_cases kind <;> rfl

private theorem cyclic_get (count n : Nat) (bound : n < count * 256) :
    Block.get? (.periodic count 0 cyclicValues) n = some ((1 + n % 256) % 256) := by
  have row := periodic_get cyclicValues count 0 n (by simp [cyclicValues])
    (by simpa only [cyclicValues, Array.size_ofFn] using bound)
  simpa [cyclicValues] using row

/-- The native concatenation changes compression at region boundaries, not byte keys. -/
theorem wide_second_key (kind : Fin 3) (n : Nat) (bound : n < 65536) :
    (wideData kind).columns[1].get? n = some (n % 256) := by
  rw [key_shape]
  by_cases zero : n = 0
  · subst n
    simp only [Column.get?, getFromBlocks, head_length, Nat.zero_lt_one,
      if_true, Nat.zero_mod]
    exact head_value kind
  · have outside : ¬ n < 1 := by omega
    by_cases middle : n - 1 < 65280
    · simp only [Column.get?, getFromBlocks, head_length, if_neg outside]
      simp only [Block.length, cyclicValues, Array.size_ofFn, Nat.reduceMul, if_pos middle]
      have value : (1 + (n - 1) % 256) % 256 = n % 256 := by omega
      exact (cyclic_get 255 (n - 1) middle).trans (congrArg some value)
    · have last : n - 1 - 65280 < 255 := by omega
      have value : 1 + (n - 1 - 65280) = n % 256 := by omega
      simp only [Column.get?, getFromBlocks, head_length, if_neg outside]
      simp only [Block.length, cyclicValues, finalValues, Array.size_ofFn, Nat.reduceMul,
        if_neg middle, if_pos last, Block.get?, Array.getElem?_ofFn, value, dif_pos last]

end Airbender.UnifiedReduced.Setup.Proofs
