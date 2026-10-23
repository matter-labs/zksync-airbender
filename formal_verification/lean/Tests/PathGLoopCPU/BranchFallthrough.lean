import Tests.PathGLoopCPU.LoopShared
set_option Elab.async false

namespace Tests.PathGLoopNative
open Airbender Trace Arithmetic Reference.RiscV.Sail Reference.Sail PathGLoopProgram

/- All actual BranchFallthrough certificates, elaborated serially without changing their assertions. -/

theorem cpu_loop_branchfallthrough_checked_i000_000_e000_015 :
    gCpuLoopBatchCheck (fun _index : Fin 1 => gapRow 54 3) 0 1
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 0).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchfallthrough_checked_i000_000_e016_031 :
    gCpuLoopBatchCheck (fun _index : Fin 1 => gapRow 54 3) 0 1
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 16).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchfallthrough_checked_i000_000_e032_047 :
    gCpuLoopBatchCheck (fun _index : Fin 1 => gapRow 54 3) 0 1
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 32).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchfallthrough_checked_i000_000_e048_063 :
    gCpuLoopBatchCheck (fun _index : Fin 1 => gapRow 54 3) 0 1
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 48).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchfallthrough_checked_i000_000_e064_079 :
    gCpuLoopBatchCheck (fun _index : Fin 1 => gapRow 54 3) 0 1
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 64).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchfallthrough_checked_i000_000_e080_095 :
    gCpuLoopBatchCheck (fun _index : Fin 1 => gapRow 54 3) 0 1
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 80).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchfallthrough_checked_i000_000_e096_111 :
    gCpuLoopBatchCheck (fun _index : Fin 1 => gapRow 54 3) 0 1
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 96).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchfallthrough_checked_i000_000_e112_127 :
    gCpuLoopBatchCheck (fun _index : Fin 1 => gapRow 54 3) 0 1
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 112).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchfallthrough_checked_i000_000_e128_128 :
    gCpuLoopBatchCheck (fun _index : Fin 1 => gapRow 54 3) 0 1
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 128).take 1) = true := by
  decide +kernel

private theorem cpu_loop_branchfallthrough_indices_000_000 (variant : Variant) (index : Fin 1)
    (setup : Table (ZMod babyBearModulus) (fields 10)) (equation : Nat)
    (indexStart : 0 ≤ index.val) (indexStop : index.val < 1) (bound : equation < 129) :
    ((gCpuPolynomials setup)[equation]'(by
      rw [g_cpu_polynomial_count]; exact bound)).eval
        (Verification.environment (machineAssignment variant (gapRow 54 3))) = 0 := by
  by_cases piece0 : equation < 16
  · exact g_cpu_loop_equation_of_batch (fun _index : Fin 1 => gapRow 54 3) variant index setup 0 1 0 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchfallthrough_checked_i000_000_e000_015
  by_cases piece16 : equation < 32
  · exact g_cpu_loop_equation_of_batch (fun _index : Fin 1 => gapRow 54 3) variant index setup 0 1 16 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchfallthrough_checked_i000_000_e016_031
  by_cases piece32 : equation < 48
  · exact g_cpu_loop_equation_of_batch (fun _index : Fin 1 => gapRow 54 3) variant index setup 0 1 32 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchfallthrough_checked_i000_000_e032_047
  by_cases piece48 : equation < 64
  · exact g_cpu_loop_equation_of_batch (fun _index : Fin 1 => gapRow 54 3) variant index setup 0 1 48 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchfallthrough_checked_i000_000_e048_063
  by_cases piece64 : equation < 80
  · exact g_cpu_loop_equation_of_batch (fun _index : Fin 1 => gapRow 54 3) variant index setup 0 1 64 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchfallthrough_checked_i000_000_e064_079
  by_cases piece80 : equation < 96
  · exact g_cpu_loop_equation_of_batch (fun _index : Fin 1 => gapRow 54 3) variant index setup 0 1 80 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchfallthrough_checked_i000_000_e080_095
  by_cases piece96 : equation < 112
  · exact g_cpu_loop_equation_of_batch (fun _index : Fin 1 => gapRow 54 3) variant index setup 0 1 96 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchfallthrough_checked_i000_000_e096_111
  by_cases piece112 : equation < 128
  · exact g_cpu_loop_equation_of_batch (fun _index : Fin 1 => gapRow 54 3) variant index setup 0 1 112 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchfallthrough_checked_i000_000_e112_127
  exact g_cpu_loop_equation_of_batch (fun _index : Fin 1 => gapRow 54 3) variant index setup 0 1 128 1 equation
    indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchfallthrough_checked_i000_000_e128_128

theorem cpu_loop_branch_fallthrough_equation (variant : Variant)
    (setup : Table (ZMod babyBearModulus) (fields 10)) (equation : Nat) (bound : equation < 129) :
    ((gCpuPolynomials setup)[equation]'(by
      rw [g_cpu_polynomial_count]; exact bound)).eval
        (Verification.environment (machineAssignment variant (gapRow 54 3))) = 0 := by
  exact cpu_loop_branchfallthrough_indices_000_000 variant 0 setup equation (by decide) (by decide) bound

end Tests.PathGLoopNative
