import Tests.PathGLoopCPU.Boot0
import Tests.PathGLoopCPU.Boot1
import Tests.PathGLoopCPU.Boot2
import Tests.PathGLoopCPU.Boot3
import Tests.PathGLoopCPU.Boot4
import Tests.PathGLoopCPU.Boot5
import Tests.PathGLoopCPU.Caller
import Tests.PathGLoopCPU.Jal
import Tests.PathGLoopCPU.Decrement
import Tests.PathGLoopCPU.BranchTaken
import Tests.PathGLoopCPU.BranchFallthrough
import Tests.PathGLoopCPU.FinalBaseline
import Tests.PathGLoopCPU.FinalScratch
import Tests.PathGLoopCPU.FinalProtectedMessage
import Tests.PathGLoopCPU.FinalCSR

namespace Tests.PathGLoopNative
open Airbender Trace Arithmetic Reference.RiscV.Sail Reference.Sail PathGLoopProgram
set_option warningAsError true
set_option Elab.async false

private theorem boot_cpu_equations (variant : Variant) (index : Fin 6)
    (setup : Table (ZMod babyBearModulus) (fields 10)) :
    ∀ expression ∈ FlatOperation.constraints (UnifiedReduced.importedConstraints setup),
      expression.eval (Verification.environment
        (machineAssignment variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)) = 0 := by
  rw [List.forall_mem_iff_forall_getElem]
  intro equation bound
  have short : equation < 129 := by simpa only [UnifiedReduced.constraint_count] using bound
  change ((gCpuPolynomials setup)[equation]'bound).eval _ = 0
  fin_cases index
  · exact cpu_boot_row0_equation variant setup equation short
  · exact cpu_boot_row1_equation variant setup equation short
  · exact cpu_boot_row2_equation variant setup equation short
  · exact cpu_boot_row3_equation variant setup equation short
  · exact cpu_boot_row4_equation variant setup equation short
  · exact cpu_boot_row5_equation variant setup equation short

private theorem loop_cpu_equations (variant : Variant) (index : Fin 55) (phase : Fin 4)
    (setup : Table (ZMod babyBearModulus) (fields 10)) :
    ∀ expression ∈ FlatOperation.constraints (UnifiedReduced.importedConstraints setup),
      expression.eval (Verification.environment (machineAssignment variant (gapRow index phase))) = 0 := by
  rw [List.forall_mem_iff_forall_getElem]
  intro equation bound
  have short : equation < 129 := by simpa only [UnifiedReduced.constraint_count] using bound
  change ((gCpuPolynomials setup)[equation]'bound).eval _ = 0
  fin_cases phase
  · exact cpu_loop_caller_equation variant index setup equation short
  · exact cpu_loop_jal_equation variant index setup equation short
  · exact cpu_loop_decrement_equation variant index setup equation short
  · by_cases taken : index.val < 54
    · exact cpu_loop_branch_taken_equation variant ⟨index.val, taken⟩ setup equation short
    · have finalIndex : index = (54 : Fin 55) := by
        apply Fin.ext
        have := index.isLt
        omega
      subst index
      exact cpu_loop_branch_fallthrough_equation variant setup equation short

private theorem final_cpu_equations (variant : Variant) (last : Fin 2)
    (setup : Table (ZMod babyBearModulus) (fields 10)) :
    ∀ expression ∈ FlatOperation.constraints (UnifiedReduced.importedConstraints setup),
      expression.eval (Verification.environment
        (machineAssignment variant ⟨226 + last.val, by have := last.isLt; omega⟩)) = 0 := by
  rw [List.forall_mem_iff_forall_getElem]
  intro equation bound
  have short : equation < 129 := by simpa only [UnifiedReduced.constraint_count] using bound
  change ((gCpuPolynomials setup)[equation]'bound).eval _ = 0
  fin_cases last
  · cases variant
    · exact cpu_final_baseline_equation setup equation short
    · exact cpu_final_scratch_equation setup equation short
    · exact cpu_final_protectedMessage_equation setup equation short
  · exact cpu_final_csr_equation variant setup equation short

/-- All129 actual CPU equations for all228 rows and all3variants. The branch
case is derived from the real iteration index used by machineAssignment. -/

theorem machine_equations (variant : Variant) (index : Fin 228)
    (setup : Table (ZMod babyBearModulus) (fields 10)) :
    ∀ expression ∈ FlatOperation.constraints (UnifiedReduced.importedConstraints setup),
      expression.eval (Verification.environment (machineAssignment variant index)) = 0 := by
  by_cases early : index.val < 6
  · exact boot_cpu_equations variant ⟨index.val, early⟩ setup
  · by_cases loop : index.val < 226
    · let iterationIndex : Fin 55 := ⟨(index.val - 6) / 4, by omega⟩
      let phase : Fin 4 := ⟨(index.val - 6) % 4, Nat.mod_lt _ (by decide)⟩
      have same : index = gapRow iterationIndex phase := by
        apply Fin.ext
        dsimp [gapRow, iterationIndex, phase]
        omega
      rw [same]
      exact loop_cpu_equations variant iterationIndex phase setup
    · let last : Fin 2 := ⟨index.val - 226, by have := index.isLt; omega⟩
      have same : index = (⟨226 + last.val, by have := last.isLt; omega⟩ : Fin 228) := by
        apply Fin.ext
        dsimp [last]
        omega
      rw [same]
      exact final_cpu_equations variant last setup

end Tests.PathGLoopNative
