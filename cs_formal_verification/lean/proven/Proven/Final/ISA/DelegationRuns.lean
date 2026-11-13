module
public import Proven.Deleg.BlakeRun
public import Proven.Deleg.BlakeG
public import Proven.Deleg.KeccakRun
public import Proven.Deleg.KeccakF1600Run
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! The runs of delegation calls (`Human/ISA/DelegationRuns.lean`). -/

namespace RV

/-- `CallsRun`; its assumptions are met by seven Blake2s round calls (`csrrw x0, 0x7c7, x0`) on the layout of
    `BlakeHashRun`'s witness. -/
private theorem calls_run_pair : CallsRun ∧ CallsRunSatisfiableClaim := by
  refine ⟨fun ks s t ⟨a, b, c, d⟩ => Deleg.calls_run_curried ks s t a b c d, ?_⟩
  obtain ⟨t, ht, -⟩ := Deleg.blake_hash_run.1 _ _ _ false (Deleg.NonVacuous.hash_assumptions _ 0x7c701073#32)
  refine ⟨.replicate 7 .blakeRound, _, t, by simp, by decide, by decide, ?_, ht⟩
  intro i hi
  simp only [List.length_replicate] at hi
  simp only [List.getElem_replicate]
  interval_cases i <;> rfl
theorem calls_run : CallsRun := calls_run_pair.1
theorem calls_run_satisfiable : CallsRunSatisfiableClaim := calls_run_pair.2
theorem blake_compress_run : BlakeCompressRun := Deleg.blake_compress_run.1
theorem blake_compress_run_satisfiable : BlakeCompressRunSatisfiableClaim := Deleg.blake_compress_run.2
theorem blake_hash_run : BlakeHashRun := Deleg.blake_hash_run.1
theorem blake_hash_run_satisfiable : BlakeHashRunSatisfiableClaim := Deleg.blake_hash_run.2
theorem blake_compress_run10 : BlakeCompressRun10 := Deleg.blake_compress_run10.1
theorem blake_compress_run10_satisfiable : BlakeCompressRun10SatisfiableClaim := Deleg.blake_compress_run10.2
theorem blake_hash_run10 : BlakeHashRun10 := Deleg.blake_hash_run10.1
theorem blake_hash_run10_satisfiable : BlakeHashRun10SatisfiableClaim := Deleg.blake_hash_run10.2
theorem blake_g_run : BlakeGRun := Deleg.blake_g_run.1
theorem blake_g_run_satisfiable : BlakeGRunSatisfiableClaim := Deleg.blake_g_run.2
theorem blake_g_run10 : BlakeGRun10 := Deleg.blake_g_run10.1
theorem blake_g_run10_satisfiable : BlakeGRun10SatisfiableClaim := Deleg.blake_g_run10.2
theorem keccak_special5_run : KeccakSpecial5Run := Deleg.keccak_special5_run.1
theorem keccak_special5_run_satisfiable : KeccakSpecial5RunSatisfiableClaim := Deleg.keccak_special5_run.2
theorem keccak_f1600_run : KeccakF1600Run := Deleg.keccak_f1600_run.1
theorem keccak_f1600_run_satisfiable : KeccakF1600RunSatisfiableClaim := Deleg.keccak_f1600_run.2

end RV
