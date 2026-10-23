import Tests.PathGLoopCPU.CoreProjection

namespace Tests.PathGLoopNative
open Airbender Trace Arithmetic Reference.RiscV.Sail Reference.Sail PathGLoopProgram
set_option warningAsError true
set_option Elab.async false

/-- Closed checks use only the proved core-coordinate projection. The actual
native predecessor clocks remain in every family theorem's conclusion. -/
def gCpuProjectedLoopBatchCheck {n : Nat} (row : Fin n → Fin 228) (first count : Nat)
    (expressions : List (Expression (ZMod babyBearModulus))) : Bool :=
  ([.baseline, .scratch, .protectedMessage] : List Variant).all fun variant =>
    (((List.finRange n).drop first).take count).all fun index =>
      gCpuEquationsCheck (gCpuCoreAssignment (machineAssignment variant (row index))) expressions

theorem g_cpu_projected_loop_batch_at {n : Nat} (row : Fin n → Fin 228) (first count : Nat)
    (expressions : List (Expression (ZMod babyBearModulus)))
    (checked : gCpuProjectedLoopBatchCheck row first count expressions = true)
    (variant : Variant) (index : Fin n)
    (start : first ≤ index.val) (stop : index.val < first + count) :
    gCpuEquationsCheck (gCpuCoreAssignment (machineAssignment variant (row index))) expressions = true := by
  have variantMember : variant ∈ ([.baseline, .scratch, .protectedMessage] : List Variant) := by
    cases variant <;> simp
  let indices := ((List.finRange n).drop first).take count
  have inside : index.val - first < indices.length := by
    simp only [indices, List.length_take, List.length_drop, List.length_finRange]
    have bound := index.isLt
    omega
  have selected : indices[index.val - first]'inside = index := by
    apply Fin.ext
    simp only [indices, List.getElem_take, List.getElem_drop, List.getElem_finRange, Fin.val_cast]
    omega
  have indexMember : index ∈ indices := by
    rw [← selected]
    exact List.getElem_mem inside
  have byVariant := List.all_eq_true.mp checked variant variantMember
  exact List.all_eq_true.mp byVariant index indexMember

theorem g_cpu_projected_loop_equation_of_batch {n : Nat} (row : Fin n → Fin 228)
    (variant : Variant) (index : Fin n)
    (setup : Table (ZMod babyBearModulus) (fields 10))
    (indexFirst indexCount first count equation : Nat)
    (indexStart : indexFirst ≤ index.val) (indexStop : index.val < indexFirst + indexCount)
    (start : first ≤ equation) (stop : equation < first + count) (actual : equation < 129)
    (checked : gCpuProjectedLoopBatchCheck row indexFirst indexCount
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop first).take count) = true)
    (ordinary : machineAssignment variant (row index) 18 = 0) :
    ((gCpuPolynomials setup)[equation]'(by
      rw [g_cpu_polynomial_count]; exact actual)).eval
        (Verification.environment (machineAssignment variant (row index))) = 0 := by
  exact g_cpu_core_equations_of_check (machineAssignment variant (row index))
    setup first count equation start stop actual ordinary
    (g_cpu_projected_loop_batch_at row indexFirst indexCount _ checked variant index indexStart indexStop)

/-- Actual ADDI decoder fields at loop phase2 derive the zero caller selector. -/
theorem g_cpu_decrement_ordinary (variant : Variant) (index : Fin 55) :
    machineAssignment variant (gapRow index 2) 18 = 0 := by
  have caller : isCaller (gapRow index 2) = false := gap_caller index 2
  have code : rowCodeIndex (gapRow index 2) = (8 : Fin 12) := loop_row_index index 2
  change (if (metadata variant (gapRow index 2)).mask.testBit 7 then 1 else 0) = 0
  unfold metadata
  rw [caller, code]
  cases variant <;> rfl

/-- Actual BNE decoder fields at loop phase3 derive the zero caller selector. -/
theorem g_cpu_branch_ordinary (variant : Variant) (index : Fin 55) :
    machineAssignment variant (gapRow index 3) 18 = 0 := by
  have caller : isCaller (gapRow index 3) = false := gap_caller index 3
  have code : rowCodeIndex (gapRow index 3) = (9 : Fin 12) := loop_row_index index 3
  change (if (metadata variant (gapRow index 3)).mask.testBit 7 then 1 else 0) = 0
  unfold metadata
  rw [caller, code]
  cases variant <;> rfl

end Tests.PathGLoopNative
