import Slop.Blake2Round.ColumnG

set_option warningAsError true
-- one call's goals may not use every lemma of the shared simp set
set_option linter.unusedSimpArgs false

namespace Airbender.Blake2Round.Proofs

set_option maxRecDepth 16384

set_option maxHeartbeats 16000000 in
/-- The sixteen table rows and the carry flags of column G call 2. -/
theorem column_rows_2 {p : Nat} [Fact p.Prime] (hp : 262144 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    (columnTrace 2 w).Rows := by
  have hp512 : 512 ≤ p := by omega
  have field := Blake2G.Proofs.serialized_field compatible
  subst field
  unfold babyBearModulus at *
  have r0 := Verification.lookup_of_holds h ⟨34, by rw [lookup_count]; omega⟩
  op_index at r0
  replace r0 := lookup_facts hp512 r0 (t := 55) (by simp [tags]) (by eval_entry)
  eval_entry at r0
  obtain ⟨q0, ka0⟩ := rows_of_55 r0 (a' := (columnTrace 2 w).d0) (b' := (columnTrace 2 w).a1b0) (c' := (columnTrace 2 w).ka0) (d' := (columnTrace 2 w).r0) (by column_eq) (by column_eq) (by column_eq) (by column_eq)
  have r1 := Verification.lookup_of_holds h ⟨35, by rw [lookup_count]; omega⟩
  op_index at r1
  replace r1 := lookup_facts hp512 r1 (t := 4) (by simp [tags]) (by eval_entry)
  eval_entry at r1
  have q1 := rows_of_4 r1 (a' := (columnTrace 2 w).d1) (b' := (columnTrace 2 w).a1b1) (c' := (columnTrace 2 w).r1) (by column_eq) (by column_eq) (by column_eq)
  have r2 := Verification.lookup_of_holds h ⟨36, by rw [lookup_count]; omega⟩
  op_index at r2
  replace r2 := lookup_facts hp512 r2 (t := 55) (by simp [tags]) (by eval_entry)
  eval_entry at r2
  obtain ⟨q2, ka1⟩ := rows_of_55 r2 (a' := (columnTrace 2 w).d2) (b' := (columnTrace 2 w).a1b2) (c' := (columnTrace 2 w).ka1) (d' := (columnTrace 2 w).r2) (by column_eq) (by column_eq) (by column_eq) (by column_eq)
  have r3 := Verification.lookup_of_holds h ⟨37, by rw [lookup_count]; omega⟩
  op_index at r3
  replace r3 := lookup_facts hp512 r3 (t := 4) (by simp [tags]) (by eval_entry)
  eval_entry at r3
  have q3 := rows_of_4 r3 (a' := (columnTrace 2 w).d3) (b' := (columnTrace 2 w).a1b3) (c' := (columnTrace 2 w).r3) (by column_eq) (by column_eq) (by column_eq)
  have r4 := Verification.lookup_of_holds h ⟨38, by rw [lookup_count]; omega⟩
  op_index at r4
  replace r4 := lookup_facts hp512 r4 (t := 20) (by simp [tags]) (by eval_entry)
  eval_entry at r4
  have q4 := rows_of_20 r4 (a' := (columnTrace 2 w).b9lo) (b' := (columnTrace 2 w).c9lo) (c' := (columnTrace 2 w).x9lo) (by column_eq) (by column_eq) (by column_eq)
  have r5 := Verification.lookup_of_holds h ⟨39, by rw [lookup_count]; omega⟩
  op_index at r5
  replace r5 := lookup_facts hp512 r5 (t := 20) (by simp [tags]) (by eval_entry)
  eval_entry at r5
  have q5 := rows_of_20 r5 (a' := (columnTrace 2 w).b9hi) (b' := (columnTrace 2 w).c9hi) (c' := (columnTrace 2 w).x9hi) (by column_eq) (by column_eq) (by column_eq)
  have r6 := Verification.lookup_of_holds h ⟨40, by rw [lookup_count]; omega⟩
  op_index at r6
  replace r6 := lookup_facts hp512 r6 (t := 57) (by simp [tags]) (by eval_entry)
  eval_entry at r6
  have q6 := rows_of_57 r6 (a' := (columnTrace 2 w).b4lo) (b' := (columnTrace 2 w).b3hi) (c' := (columnTrace 2 w).c4lo) (d' := (columnTrace 2 w).c3hi) (e' := (columnTrace 2 w).x7lo) (by column_eq) (by column_eq) (by column_eq) (by column_eq) (by column_eq)
  have r7 := Verification.lookup_of_holds h ⟨41, by rw [lookup_count]; omega⟩
  op_index at r7
  replace r7 := lookup_facts hp512 r7 (t := 57) (by simp [tags]) (by eval_entry)
  eval_entry at r7
  have q7 := rows_of_57 r7 (a' := (columnTrace 2 w).b4hi) (b' := (columnTrace 2 w).b3lo) (c' := (columnTrace 2 w).c4hi) (d' := (columnTrace 2 w).c3lo) (e' := (columnTrace 2 w).x7hi) (by column_eq) (by column_eq) (by column_eq) (by column_eq) (by column_eq)
  have r8 := Verification.lookup_of_holds h ⟨42, by rw [lookup_count]; omega⟩
  op_index at r8
  replace r8 := lookup_facts hp512 r8 (t := 4) (by simp [tags]) (by eval_entry)
  eval_entry at r8
  have q8 := rows_of_4 r8 (a' := (columnTrace 2 w).r3) (b' := (columnTrace 2 w).a2b1) (c' := (columnTrace 2 w).s0) (by column_eq) (by column_eq) (by column_eq)
  have r9 := Verification.lookup_of_holds h ⟨43, by rw [lookup_count]; omega⟩
  op_index at r9
  replace r9 := lookup_facts hp512 r9 (t := 4) (by simp [tags]) (by eval_entry)
  eval_entry at r9
  have q9 := rows_of_4 r9 (a' := (columnTrace 2 w).r1) (b' := (columnTrace 2 w).a2b3) (c' := (columnTrace 2 w).s1) (by column_eq) (by column_eq) (by column_eq)
  have r10 := Verification.lookup_of_holds h ⟨44, by rw [lookup_count]; omega⟩
  op_index at r10
  replace r10 := lookup_facts hp512 r10 (t := 55) (by simp [tags]) (by eval_entry)
  eval_entry at r10
  obtain ⟨q10, kb0⟩ := rows_of_55 r10 (a' := (columnTrace 2 w).r2) (b' := (columnTrace 2 w).a2b0) (c' := (columnTrace 2 w).kb0) (d' := (columnTrace 2 w).s2) (by column_eq) (by column_eq) (by column_eq) (by column_eq)
  have r11 := Verification.lookup_of_holds h ⟨45, by rw [lookup_count]; omega⟩
  op_index at r11
  replace r11 := lookup_facts hp512 r11 (t := 55) (by simp [tags]) (by eval_entry)
  eval_entry at r11
  obtain ⟨q11, kb1⟩ := rows_of_55 r11 (a' := (columnTrace 2 w).r0) (b' := (columnTrace 2 w).a2b2) (c' := (columnTrace 2 w).kb1) (d' := (columnTrace 2 w).s3) (by column_eq) (by column_eq) (by column_eq) (by column_eq)
  have r12 := Verification.lookup_of_holds h ⟨46, by rw [lookup_count]; omega⟩
  op_index at r12
  replace r12 := lookup_facts hp512 r12 (t := 20) (by simp [tags]) (by eval_entry)
  eval_entry at r12
  have q12 := rows_of_20 r12 (a' := (columnTrace 2 w).x9hi) (b' := (columnTrace 2 w).c2h0) (c' := (columnTrace 2 w).t0) (by column_eq) (by column_eq) (by column_eq)
  have r13 := Verification.lookup_of_holds h ⟨47, by rw [lookup_count]; omega⟩
  op_index at r13
  replace r13 := lookup_facts hp512 r13 (t := 20) (by simp [tags]) (by eval_entry)
  eval_entry at r13
  have q13 := rows_of_20 r13 (a' := (columnTrace 2 w).x9lo) (b' := (columnTrace 2 w).c2h1) (c' := (columnTrace 2 w).t1) (by column_eq) (by column_eq) (by column_eq)
  have r14 := Verification.lookup_of_holds h ⟨48, by rw [lookup_count]; omega⟩
  op_index at r14
  replace r14 := lookup_facts hp512 r14 (t := 19) (by simp [tags]) (by eval_entry)
  eval_entry at r14
  have q14 := rows_of_19 r14 (a' := (columnTrace 2 w).x7lo) (b' := (columnTrace 2 w).c2l0) (c' := (columnTrace 2 w).t2) (by column_eq) (by column_eq) (by column_eq)
  have r15 := Verification.lookup_of_holds h ⟨49, by rw [lookup_count]; omega⟩
  op_index at r15
  replace r15 := lookup_facts hp512 r15 (t := 19) (by simp [tags]) (by eval_entry)
  eval_entry at r15
  have q15 := rows_of_19 r15 (a' := (columnTrace 2 w).x7hi) (b' := (columnTrace 2 w).c2l1) (c' := (columnTrace 2 w).t3) (by column_eq) (by column_eq) (by column_eq)
  have fkc0 := Verification.assertion_of_holds h ⟨145, by rw [constraint_count]; omega⟩
  op_index at fkc0
  eval_entry at fkc0
  have kc0 := carry_of_flag fkc0 (x' := (columnTrace 2 w).kc0) (by column_eq)
  have fkc1 := Verification.assertion_of_holds h ⟨146, by rw [constraint_count]; omega⟩
  op_index at fkc1
  eval_entry at fkc1
  have kc1 := carry_of_flag fkc1 (x' := (columnTrace 2 w).kc1) (by column_eq)
  have fkd0 := Verification.assertion_of_holds h ⟨147, by rw [constraint_count]; omega⟩
  op_index at fkd0
  eval_entry at fkd0
  have kd0 := carry_of_flag fkd0 (x' := (columnTrace 2 w).kd0) (by column_eq)
  have fkd1 := Verification.assertion_of_holds h ⟨148, by rw [constraint_count]; omega⟩
  op_index at fkd1
  eval_entry at fkd1
  have kd1 := carry_of_flag fkd1 (x' := (columnTrace 2 w).kd1) (by column_eq)
  exact { q0 := q0, q1 := q1, q2 := q2, q3 := q3, ka0 := ka0, ka1 := ka1, q4 := q4, q5 := q5, q6 := q6, q7 := q7, kc0 := kc0, kc1 := kc1, q8 := q8, q9 := q9, q10 := q10, q11 := q11, kb0 := kb0, kb1 := kb1, q12 := q12, q13 := q13, q14 := q14, q15 := q15, kd0 := kd0, kd1 := kd1 }

end Airbender.Blake2Round.Proofs
