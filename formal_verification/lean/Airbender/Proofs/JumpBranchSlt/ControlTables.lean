import Airbender.Review.Circuits.JumpBranchSlt.Tables.NativeData
import Airbender.Review.Circuits.JumpBranchSlt.Tables.Control
import Airbender.Proofs.Tables.PeriodicColumns
import Airbender.Proofs.Mersenne31
import Mathlib.Tactic.IntervalCases

namespace Airbender.JumpBranchSlt.Proofs
open Setup Verification

-- Copied unchanged from the checked v2 scalar certificate.
private theorem affine_get (length first step n : Nat) (bound : n < length) :
    Block.get? (.affine length first (step : Int)) n = some (first + step * n) := by
  simp only [Block.get?, Block.length, if_pos bound]
  have casts : (first : Int) + (step : Int) * n = ((first + step * n : Nat) : Int) := by simp
  rw [casts, if_pos (Int.natCast_nonneg _), Int.toNat_natCast]

private theorem single_get (block : Block) (n : Nat) (bound : n < block.length) :
    (⟨#[block]⟩ : Column).get? n = block.get? n := by
  change getFromBlocks [block] n = _
  rw [getFromBlocks, if_pos bound]

/-- Every exported native cleanup value, including its table ID. The 65k domain
    is symbolic: only the four stored periodic template entries are inspected. -/
theorem native_cleanup_rows (i : Fin 65536) :
    Native.controlCleanup.rowNat i = (jumpCleanupRow i).push 17 := by
  have key : Native.controlCleanup.columns[0].get? i.val = some i.val := by
    change (⟨#[.affine 65536 0 1]⟩ : Column).get? i.val = _
    rw [single_get _ _ i.isLt]
    simpa using affine_get 65536 0 1 i.val i.isLt
  have bit : Native.controlCleanup.columns[1].get? i.val = some (i.val / 2 % 2) := by
    change (⟨#[.periodic 16384 0 #[0, 0, 1, 1]]⟩ : Column).get? i.val = _
    rw [single_get _ _ i.isLt]
    have read := Setup.Proofs.periodic_get #[0, 0, 1, 1] 16384 0 i.val (by decide) i.isLt
    change Block.get? (.periodic 16384 0 #[0, 0, 1, 1]) i.val = _ at read
    rw [read]
    simp only [Nat.zero_mul, Nat.add_zero]
    have cases : i.val % 4 = 0 ∨ i.val % 4 = 1 ∨ i.val % 4 = 2 ∨ i.val % 4 = 3 := by omega
    rcases cases with h | h | h | h <;> simp [h] <;> omega
  have cleaned : Native.controlCleanup.columns[2].get? i.val = some (4 * (i.val / 4)) := by
    change (⟨#[.periodic 16384 4 (Array.replicate 4 0)]⟩ : Column).get? i.val = _
    rw [single_get _ _ i.isLt]
    have read := Setup.Proofs.periodic_get (Array.replicate 4 0) 16384 4 i.val (by decide) i.isLt
    change Block.get? (.periodic 16384 4 (Array.replicate 4 0)) i.val = _ at read
    rw [read]
    simp
  have tag : Native.controlCleanup.columns[3].get? i.val = some 17 := by
    change (⟨#[.affine 65536 17 0]⟩ : Column).get? i.val = _
    rw [single_get _ _ i.isLt]
    simpa using affine_get 65536 17 0 i.val i.isLt
  apply Vector.ext
  intro lane bound
  interval_cases lane <;> simp [TableData.rowNat, key, bit, cleaned, tag, jumpCleanupRow]

/-- All 128 actual native conditional rows retain separate flags and funct3
    keys. This finite kernel certificate includes every four-bit input, not
    merely flag combinations expected from valid instructions. -/
theorem native_conditional_rows : ∀ i : Fin 128,
    Native.controlConditional.rowNat i = (conditionalControlRow i).push 43 := by
  decide +kernel

/-- Original Clean table meanings now have a checked native data connection. -/
theorem cleanup_lookup (query : Vector (ZMod mersenne31Modulus) 3) :
    jumpCleanupTable.Contains #[] query ↔ ∃ i : Fin 65536,
      query.push 17 = Native.controlCleanup.row i := by
  change (∃ i : Fin 65536, query = (jumpCleanupRow i).map Nat.cast) ↔ _
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, by simp [TableData.row, native_cleanup_rows, Vector.map_push]⟩
  · rintro ⟨i, same⟩
    refine ⟨i, ?_⟩
    apply Vector.ext
    intro lane bound
    have selected := congrArg (fun v : Vector (ZMod mersenne31Modulus) 4 => v[lane]) same
    simpa [TableData.row, native_cleanup_rows, Vector.map_push,
      Vector.getElem_push, bound] using selected

theorem conditional_lookup (query : Vector (ZMod mersenne31Modulus) 3) :
    conditionalControlTable.Contains #[] query ↔ ∃ i : Fin 128,
      query.push 43 = Native.controlConditional.row i := by
  change (∃ i : Fin 128, query = (conditionalControlRow i).map Nat.cast) ↔ _
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, by simp [TableData.row, native_conditional_rows, Vector.map_push]⟩
  · rintro ⟨i, same⟩
    refine ⟨i, ?_⟩
    apply Vector.ext
    intro lane bound
    have selected := congrArg (fun v : Vector (ZMod mersenne31Modulus) 4 => v[lane]) same
    simpa [TableData.row, native_conditional_rows, Vector.map_push,
      Vector.getElem_push, bound] using selected

/-- Cleanup membership derives a canonical key and its exact retained/cleared bits. -/
theorem cleanup_values {key bit cleaned : ZMod mersenne31Modulus}
    (holds : jumpCleanupTable.Contains #[] #v[key, bit, cleaned]) :
    key.val < 65536 ∧ bit = (key.val / 2 % 2 : Nat) ∧ cleaned = (4 * (key.val / 4) : Nat) := by
  change ∃ i : Fin 65536, #v[key, bit, cleaned] = (jumpCleanupRow i).map Nat.cast at holds
  obtain ⟨i, same⟩ := holds
  have head : key = (i.val : ZMod mersenne31Modulus) := by
    simpa [jumpCleanupRow] using congrArg (fun v : Vector (ZMod mersenne31Modulus) 3 => v[0]) same
  have value : key.val = i.val := by
    rw [head, ZMod.val_natCast_of_lt (by have := i.isLt; unfold mersenne31Modulus; omega)]
  refine ⟨by rw [value]; exact i.isLt, ?_, ?_⟩
  · rw [value]
    simpa [jumpCleanupRow] using congrArg (fun v : Vector (ZMod mersenne31Modulus) 3 => v[1]) same
  · rw [value]
    simpa [jumpCleanupRow] using congrArg (fun v : Vector (ZMod mersenne31Modulus) 3 => v[2]) same

/-- The separate four-bit and funct3 keys determine the exact control result. -/
theorem conditional_values {bits funct3 result : ZMod mersenne31Modulus}
    (holds : conditionalControlTable.Contains #[] #v[bits, funct3, result]) :
    bits.val < 16 ∧ funct3.val < 8 ∧
      result = if controlFlag bits.val funct3.val then 1 else 0 := by
  change ∃ i : Fin 128, #v[bits, funct3, result] = (conditionalControlRow i).map Nat.cast at holds
  obtain ⟨i, same⟩ := holds
  have flags : bits = (i.val / 8 : Nat) := by
    simpa [conditionalControlRow] using congrArg (fun v : Vector (ZMod mersenne31Modulus) 3 => v[0]) same
  have tag : funct3 = (i.val % 8 : Nat) := by
    simpa [conditionalControlRow] using congrArg (fun v : Vector (ZMod mersenne31Modulus) 3 => v[1]) same
  have flagsValue : bits.val = i.val / 8 := by
    rw [flags, ZMod.val_natCast_of_lt (by have := i.isLt; unfold mersenne31Modulus; omega)]
  have tagValue : funct3.val = i.val % 8 := by
    rw [tag, ZMod.val_natCast_of_lt (by unfold mersenne31Modulus; omega)]
  refine ⟨by rw [flagsValue]; have := i.isLt; omega, by rw [tagValue]; omega, ?_⟩
  rw [flagsValue, tagValue]
  have out := congrArg (fun v : Vector (ZMod mersenne31Modulus) 3 => v[2]) same
  simpa [conditionalControlRow] using out

end Airbender.JumpBranchSlt.Proofs
