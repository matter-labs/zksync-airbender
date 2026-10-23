import Tests.PathGLoopCPU.Shared

namespace Tests.PathGLoopNative
open Airbender Trace Arithmetic Reference.RiscV.Sail Reference.Sail PathGLoopProgram

/- Generic test-only retrieval from a closed grid of actual variants and
finite native rows. Every family supplies its actual row-index function. -/

def gCpuLoopBatchCheck {n : Nat} (row : Fin n → Fin 228) (first count : Nat)
    (expressions : List (Expression (ZMod babyBearModulus))) : Bool :=
  ([.baseline, .scratch, .protectedMessage] : List Variant).all fun variant =>
    (((List.finRange n).drop first).take count).all fun index =>
      gCpuEquationsCheck (machineAssignment variant (row index)) expressions

theorem g_cpu_loop_batch_at {n : Nat} (row : Fin n → Fin 228) (first count : Nat)
    (expressions : List (Expression (ZMod babyBearModulus)))
    (checked : gCpuLoopBatchCheck row first count expressions = true)
    (variant : Variant) (index : Fin n)
    (start : first ≤ index.val) (stop : index.val < first + count) :
    gCpuEquationsCheck (machineAssignment variant (row index)) expressions = true := by
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

theorem g_cpu_loop_equation_of_batch {n : Nat} (row : Fin n → Fin 228)
    (variant : Variant) (index : Fin n)
    (setup : Table (ZMod babyBearModulus) (fields 10))
    (indexFirst indexCount first count equation : Nat)
    (indexStart : indexFirst ≤ index.val) (indexStop : index.val < indexFirst + indexCount)
    (start : first ≤ equation) (stop : equation < first + count) (actual : equation < 129)
    (checked : gCpuLoopBatchCheck row indexFirst indexCount
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop first).take count) = true) :
    ((gCpuPolynomials setup)[equation]'(by
      rw [g_cpu_polynomial_count]; exact actual)).eval
        (Verification.environment (machineAssignment variant (row index))) = 0 := by
  exact g_cpu_equations_of_check (machineAssignment variant (row index))
    setup first count equation start stop actual
    (g_cpu_loop_batch_at row indexFirst indexCount _ checked variant index indexStart indexStop)

end Tests.PathGLoopNative
