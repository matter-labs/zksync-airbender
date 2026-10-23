import Tests.PathGLoopCPU.ProjectionLoopShared
set_option Elab.async false

namespace Tests.PathGLoopNative
open Airbender Trace Arithmetic Reference.RiscV.Sail Reference.Sail PathGLoopProgram

/- All actual Decrement certificates, elaborated serially without changing their assertions. -/

theorem cpu_loop_decrement_checked_i000_007_e000_015 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 0 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 0).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i000_007_e016_031 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 0 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 16).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i000_007_e032_047 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 0 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 32).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i000_007_e048_063 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 0 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 48).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i000_007_e064_079 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 0 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 64).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i000_007_e080_095 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 0 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 80).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i000_007_e096_111 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 0 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 96).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i000_007_e112_127 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 0 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 112).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i000_007_e128_128 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 0 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 128).take 1) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i008_015_e000_015 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 8 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 0).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i008_015_e016_031 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 8 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 16).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i008_015_e032_047 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 8 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 32).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i008_015_e048_063 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 8 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 48).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i008_015_e064_079 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 8 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 64).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i008_015_e080_095 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 8 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 80).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i008_015_e096_111 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 8 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 96).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i008_015_e112_127 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 8 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 112).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i008_015_e128_128 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 8 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 128).take 1) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i016_023_e000_015 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 16 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 0).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i016_023_e016_031 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 16 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 16).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i016_023_e032_047 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 16 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 32).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i016_023_e048_063 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 16 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 48).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i016_023_e064_079 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 16 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 64).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i016_023_e080_095 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 16 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 80).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i016_023_e096_111 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 16 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 96).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i016_023_e112_127 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 16 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 112).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i016_023_e128_128 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 16 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 128).take 1) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i024_031_e000_015 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 24 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 0).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i024_031_e016_031 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 24 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 16).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i024_031_e032_047 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 24 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 32).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i024_031_e048_063 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 24 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 48).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i024_031_e064_079 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 24 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 64).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i024_031_e080_095 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 24 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 80).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i024_031_e096_111 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 24 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 96).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i024_031_e112_127 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 24 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 112).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i024_031_e128_128 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 24 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 128).take 1) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i032_039_e000_015 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 32 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 0).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i032_039_e016_031 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 32 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 16).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i032_039_e032_047 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 32 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 32).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i032_039_e048_063 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 32 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 48).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i032_039_e064_079 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 32 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 64).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i032_039_e080_095 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 32 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 80).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i032_039_e096_111 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 32 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 96).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i032_039_e112_127 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 32 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 112).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i032_039_e128_128 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 32 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 128).take 1) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i040_047_e000_015 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 40 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 0).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i040_047_e016_031 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 40 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 16).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i040_047_e032_047 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 40 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 32).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i040_047_e048_063 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 40 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 48).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i040_047_e064_079 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 40 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 64).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i040_047_e080_095 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 40 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 80).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i040_047_e096_111 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 40 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 96).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i040_047_e112_127 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 40 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 112).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i040_047_e128_128 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 40 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 128).take 1) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i048_054_e000_015 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 48 7
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 0).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i048_054_e016_031 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 48 7
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 16).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i048_054_e032_047 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 48 7
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 32).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i048_054_e048_063 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 48 7
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 48).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i048_054_e064_079 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 48 7
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 64).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i048_054_e080_095 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 48 7
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 80).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i048_054_e096_111 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 48 7
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 96).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i048_054_e112_127 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 48 7
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 112).take 16) = true := by
  decide +kernel

theorem cpu_loop_decrement_checked_i048_054_e128_128 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 55 => gapRow index 2) 48 7
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 128).take 1) = true := by
  decide +kernel

private theorem cpu_loop_decrement_indices_000_007 (variant : Variant) (index : Fin 55)
    (setup : Table (ZMod babyBearModulus) (fields 10)) (equation : Nat)
    (indexStart : 0 ≤ index.val) (indexStop : index.val < 8) (bound : equation < 129) :
    ((gCpuPolynomials setup)[equation]'(by
      rw [g_cpu_polynomial_count]; exact bound)).eval
        (Verification.environment (machineAssignment variant (gapRow index 2))) = 0 := by
  by_cases piece0 : equation < 16
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 0 8 0 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i000_007_e000_015 (g_cpu_decrement_ordinary variant index)
  by_cases piece16 : equation < 32
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 0 8 16 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i000_007_e016_031 (g_cpu_decrement_ordinary variant index)
  by_cases piece32 : equation < 48
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 0 8 32 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i000_007_e032_047 (g_cpu_decrement_ordinary variant index)
  by_cases piece48 : equation < 64
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 0 8 48 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i000_007_e048_063 (g_cpu_decrement_ordinary variant index)
  by_cases piece64 : equation < 80
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 0 8 64 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i000_007_e064_079 (g_cpu_decrement_ordinary variant index)
  by_cases piece80 : equation < 96
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 0 8 80 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i000_007_e080_095 (g_cpu_decrement_ordinary variant index)
  by_cases piece96 : equation < 112
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 0 8 96 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i000_007_e096_111 (g_cpu_decrement_ordinary variant index)
  by_cases piece112 : equation < 128
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 0 8 112 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i000_007_e112_127 (g_cpu_decrement_ordinary variant index)
  exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 0 8 128 1 equation
    indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i000_007_e128_128 (g_cpu_decrement_ordinary variant index)

private theorem cpu_loop_decrement_indices_008_015 (variant : Variant) (index : Fin 55)
    (setup : Table (ZMod babyBearModulus) (fields 10)) (equation : Nat)
    (indexStart : 8 ≤ index.val) (indexStop : index.val < 16) (bound : equation < 129) :
    ((gCpuPolynomials setup)[equation]'(by
      rw [g_cpu_polynomial_count]; exact bound)).eval
        (Verification.environment (machineAssignment variant (gapRow index 2))) = 0 := by
  by_cases piece0 : equation < 16
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 8 8 0 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i008_015_e000_015 (g_cpu_decrement_ordinary variant index)
  by_cases piece16 : equation < 32
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 8 8 16 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i008_015_e016_031 (g_cpu_decrement_ordinary variant index)
  by_cases piece32 : equation < 48
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 8 8 32 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i008_015_e032_047 (g_cpu_decrement_ordinary variant index)
  by_cases piece48 : equation < 64
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 8 8 48 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i008_015_e048_063 (g_cpu_decrement_ordinary variant index)
  by_cases piece64 : equation < 80
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 8 8 64 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i008_015_e064_079 (g_cpu_decrement_ordinary variant index)
  by_cases piece80 : equation < 96
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 8 8 80 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i008_015_e080_095 (g_cpu_decrement_ordinary variant index)
  by_cases piece96 : equation < 112
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 8 8 96 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i008_015_e096_111 (g_cpu_decrement_ordinary variant index)
  by_cases piece112 : equation < 128
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 8 8 112 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i008_015_e112_127 (g_cpu_decrement_ordinary variant index)
  exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 8 8 128 1 equation
    indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i008_015_e128_128 (g_cpu_decrement_ordinary variant index)

private theorem cpu_loop_decrement_indices_016_023 (variant : Variant) (index : Fin 55)
    (setup : Table (ZMod babyBearModulus) (fields 10)) (equation : Nat)
    (indexStart : 16 ≤ index.val) (indexStop : index.val < 24) (bound : equation < 129) :
    ((gCpuPolynomials setup)[equation]'(by
      rw [g_cpu_polynomial_count]; exact bound)).eval
        (Verification.environment (machineAssignment variant (gapRow index 2))) = 0 := by
  by_cases piece0 : equation < 16
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 16 8 0 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i016_023_e000_015 (g_cpu_decrement_ordinary variant index)
  by_cases piece16 : equation < 32
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 16 8 16 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i016_023_e016_031 (g_cpu_decrement_ordinary variant index)
  by_cases piece32 : equation < 48
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 16 8 32 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i016_023_e032_047 (g_cpu_decrement_ordinary variant index)
  by_cases piece48 : equation < 64
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 16 8 48 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i016_023_e048_063 (g_cpu_decrement_ordinary variant index)
  by_cases piece64 : equation < 80
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 16 8 64 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i016_023_e064_079 (g_cpu_decrement_ordinary variant index)
  by_cases piece80 : equation < 96
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 16 8 80 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i016_023_e080_095 (g_cpu_decrement_ordinary variant index)
  by_cases piece96 : equation < 112
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 16 8 96 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i016_023_e096_111 (g_cpu_decrement_ordinary variant index)
  by_cases piece112 : equation < 128
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 16 8 112 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i016_023_e112_127 (g_cpu_decrement_ordinary variant index)
  exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 16 8 128 1 equation
    indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i016_023_e128_128 (g_cpu_decrement_ordinary variant index)

private theorem cpu_loop_decrement_indices_024_031 (variant : Variant) (index : Fin 55)
    (setup : Table (ZMod babyBearModulus) (fields 10)) (equation : Nat)
    (indexStart : 24 ≤ index.val) (indexStop : index.val < 32) (bound : equation < 129) :
    ((gCpuPolynomials setup)[equation]'(by
      rw [g_cpu_polynomial_count]; exact bound)).eval
        (Verification.environment (machineAssignment variant (gapRow index 2))) = 0 := by
  by_cases piece0 : equation < 16
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 24 8 0 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i024_031_e000_015 (g_cpu_decrement_ordinary variant index)
  by_cases piece16 : equation < 32
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 24 8 16 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i024_031_e016_031 (g_cpu_decrement_ordinary variant index)
  by_cases piece32 : equation < 48
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 24 8 32 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i024_031_e032_047 (g_cpu_decrement_ordinary variant index)
  by_cases piece48 : equation < 64
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 24 8 48 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i024_031_e048_063 (g_cpu_decrement_ordinary variant index)
  by_cases piece64 : equation < 80
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 24 8 64 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i024_031_e064_079 (g_cpu_decrement_ordinary variant index)
  by_cases piece80 : equation < 96
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 24 8 80 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i024_031_e080_095 (g_cpu_decrement_ordinary variant index)
  by_cases piece96 : equation < 112
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 24 8 96 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i024_031_e096_111 (g_cpu_decrement_ordinary variant index)
  by_cases piece112 : equation < 128
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 24 8 112 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i024_031_e112_127 (g_cpu_decrement_ordinary variant index)
  exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 24 8 128 1 equation
    indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i024_031_e128_128 (g_cpu_decrement_ordinary variant index)

private theorem cpu_loop_decrement_indices_032_039 (variant : Variant) (index : Fin 55)
    (setup : Table (ZMod babyBearModulus) (fields 10)) (equation : Nat)
    (indexStart : 32 ≤ index.val) (indexStop : index.val < 40) (bound : equation < 129) :
    ((gCpuPolynomials setup)[equation]'(by
      rw [g_cpu_polynomial_count]; exact bound)).eval
        (Verification.environment (machineAssignment variant (gapRow index 2))) = 0 := by
  by_cases piece0 : equation < 16
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 32 8 0 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i032_039_e000_015 (g_cpu_decrement_ordinary variant index)
  by_cases piece16 : equation < 32
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 32 8 16 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i032_039_e016_031 (g_cpu_decrement_ordinary variant index)
  by_cases piece32 : equation < 48
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 32 8 32 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i032_039_e032_047 (g_cpu_decrement_ordinary variant index)
  by_cases piece48 : equation < 64
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 32 8 48 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i032_039_e048_063 (g_cpu_decrement_ordinary variant index)
  by_cases piece64 : equation < 80
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 32 8 64 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i032_039_e064_079 (g_cpu_decrement_ordinary variant index)
  by_cases piece80 : equation < 96
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 32 8 80 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i032_039_e080_095 (g_cpu_decrement_ordinary variant index)
  by_cases piece96 : equation < 112
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 32 8 96 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i032_039_e096_111 (g_cpu_decrement_ordinary variant index)
  by_cases piece112 : equation < 128
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 32 8 112 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i032_039_e112_127 (g_cpu_decrement_ordinary variant index)
  exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 32 8 128 1 equation
    indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i032_039_e128_128 (g_cpu_decrement_ordinary variant index)

private theorem cpu_loop_decrement_indices_040_047 (variant : Variant) (index : Fin 55)
    (setup : Table (ZMod babyBearModulus) (fields 10)) (equation : Nat)
    (indexStart : 40 ≤ index.val) (indexStop : index.val < 48) (bound : equation < 129) :
    ((gCpuPolynomials setup)[equation]'(by
      rw [g_cpu_polynomial_count]; exact bound)).eval
        (Verification.environment (machineAssignment variant (gapRow index 2))) = 0 := by
  by_cases piece0 : equation < 16
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 40 8 0 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i040_047_e000_015 (g_cpu_decrement_ordinary variant index)
  by_cases piece16 : equation < 32
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 40 8 16 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i040_047_e016_031 (g_cpu_decrement_ordinary variant index)
  by_cases piece32 : equation < 48
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 40 8 32 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i040_047_e032_047 (g_cpu_decrement_ordinary variant index)
  by_cases piece48 : equation < 64
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 40 8 48 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i040_047_e048_063 (g_cpu_decrement_ordinary variant index)
  by_cases piece64 : equation < 80
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 40 8 64 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i040_047_e064_079 (g_cpu_decrement_ordinary variant index)
  by_cases piece80 : equation < 96
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 40 8 80 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i040_047_e080_095 (g_cpu_decrement_ordinary variant index)
  by_cases piece96 : equation < 112
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 40 8 96 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i040_047_e096_111 (g_cpu_decrement_ordinary variant index)
  by_cases piece112 : equation < 128
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 40 8 112 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i040_047_e112_127 (g_cpu_decrement_ordinary variant index)
  exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 40 8 128 1 equation
    indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i040_047_e128_128 (g_cpu_decrement_ordinary variant index)

private theorem cpu_loop_decrement_indices_048_054 (variant : Variant) (index : Fin 55)
    (setup : Table (ZMod babyBearModulus) (fields 10)) (equation : Nat)
    (indexStart : 48 ≤ index.val) (indexStop : index.val < 55) (bound : equation < 129) :
    ((gCpuPolynomials setup)[equation]'(by
      rw [g_cpu_polynomial_count]; exact bound)).eval
        (Verification.environment (machineAssignment variant (gapRow index 2))) = 0 := by
  by_cases piece0 : equation < 16
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 48 7 0 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i048_054_e000_015 (g_cpu_decrement_ordinary variant index)
  by_cases piece16 : equation < 32
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 48 7 16 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i048_054_e016_031 (g_cpu_decrement_ordinary variant index)
  by_cases piece32 : equation < 48
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 48 7 32 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i048_054_e032_047 (g_cpu_decrement_ordinary variant index)
  by_cases piece48 : equation < 64
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 48 7 48 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i048_054_e048_063 (g_cpu_decrement_ordinary variant index)
  by_cases piece64 : equation < 80
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 48 7 64 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i048_054_e064_079 (g_cpu_decrement_ordinary variant index)
  by_cases piece80 : equation < 96
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 48 7 80 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i048_054_e080_095 (g_cpu_decrement_ordinary variant index)
  by_cases piece96 : equation < 112
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 48 7 96 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i048_054_e096_111 (g_cpu_decrement_ordinary variant index)
  by_cases piece112 : equation < 128
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 48 7 112 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i048_054_e112_127 (g_cpu_decrement_ordinary variant index)
  exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 55 => gapRow index 2) variant index setup 48 7 128 1 equation
    indexStart (by omega) (by omega) (by omega) bound cpu_loop_decrement_checked_i048_054_e128_128 (g_cpu_decrement_ordinary variant index)

theorem cpu_loop_decrement_equation (variant : Variant) (index : Fin 55)
    (setup : Table (ZMod babyBearModulus) (fields 10)) (equation : Nat) (bound : equation < 129) :
    ((gCpuPolynomials setup)[equation]'(by
      rw [g_cpu_polynomial_count]; exact bound)).eval
        (Verification.environment (machineAssignment variant (gapRow index 2))) = 0 := by
  by_cases chunk0 : index.val < 8
  · exact cpu_loop_decrement_indices_000_007 variant index setup equation (by omega) chunk0 bound
  by_cases chunk8 : index.val < 16
  · exact cpu_loop_decrement_indices_008_015 variant index setup equation (by omega) chunk8 bound
  by_cases chunk16 : index.val < 24
  · exact cpu_loop_decrement_indices_016_023 variant index setup equation (by omega) chunk16 bound
  by_cases chunk24 : index.val < 32
  · exact cpu_loop_decrement_indices_024_031 variant index setup equation (by omega) chunk24 bound
  by_cases chunk32 : index.val < 40
  · exact cpu_loop_decrement_indices_032_039 variant index setup equation (by omega) chunk32 bound
  by_cases chunk40 : index.val < 48
  · exact cpu_loop_decrement_indices_040_047 variant index setup equation (by omega) chunk40 bound
  exact cpu_loop_decrement_indices_048_054 variant index setup equation (by omega) index.isLt bound

end Tests.PathGLoopNative
