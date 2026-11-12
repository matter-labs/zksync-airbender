module
public import Slop.Deleg.BlakeRun
public import Slop.Deleg.BlakeG
public import Slop.Deleg.KeccakRun
public import Slop.Deleg.KeccakF1600Run
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! The runs of delegation calls (`Human/ISA/DelegationRuns.lean`). -/

namespace RV

/-- `CallsRun`; its assumptions are met by seven Blake2s round calls (`csrrw x0, 0x7c7, x0`) on the layout of
    `BlakeHashRun`'s witness. -/
theorem calls_run : CallsRun := by
  refine ⟨fun ks s t ⟨a, b, c, d⟩ => Deleg.calls_run_curried ks s t a b c d, ?_⟩
  obtain ⟨t, ht, -⟩ := Deleg.blake_hash_run.1 _ _ _ false (Deleg.NonVacuous.hash_assumptions _ 0x7c701073#32)
  refine ⟨.replicate 7 .blakeRound, _, t, by simp, by decide, by decide, ?_, ht⟩
  intro i hi
  simp only [List.length_replicate] at hi
  simp only [List.getElem_replicate]
  interval_cases i <;> rfl
theorem blake_compress_run : BlakeCompressRun := Deleg.blake_compress_run
theorem blake_hash_run : BlakeHashRun := Deleg.blake_hash_run
theorem blake_compress_run10 : BlakeCompressRun10 := Deleg.blake_compress_run10
theorem blake_hash_run10 : BlakeHashRun10 := Deleg.blake_hash_run10
theorem blake_g_run : BlakeGRun := Deleg.blake_g_run
theorem blake_g_run10 : BlakeGRun10 := Deleg.blake_g_run10
theorem keccak_special5_run : KeccakSpecial5Run := Deleg.keccak_special5_run
theorem keccak_f1600_run : KeccakF1600Run := Deleg.keccak_f1600_run

end RV
