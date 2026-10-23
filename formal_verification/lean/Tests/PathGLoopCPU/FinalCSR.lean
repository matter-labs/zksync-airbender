import Tests.PathGLoopCPU.Shared

namespace Tests.PathGLoopNative
open Airbender Trace Arithmetic Reference.RiscV.Sail Reference.Sail PathGLoopProgram
set_option warningAsError true
set_option Elab.async false

/- All129 actual final-CSR assertions for each of the three variants.
   Each closed certificate checks at most16 equations of one actual assignment.
   Earlier store variants retain their own previous timestamps; no assignment
   equality across variants is used. -/

private theorem cpu_final_csr_checked_baseline_000_015 :
    gCpuEquationsCheck (machineAssignment .baseline 227)
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 0).take 16) = true := by
  decide +kernel

private theorem cpu_final_csr_checked_scratch_000_015 :
    gCpuEquationsCheck (machineAssignment .scratch 227)
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 0).take 16) = true := by
  decide +kernel

private theorem cpu_final_csr_checked_protectedMessage_000_015 :
    gCpuEquationsCheck (machineAssignment .protectedMessage 227)
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 0).take 16) = true := by
  decide +kernel

private theorem cpu_final_csr_000_015 (variant : Variant)
    (setup : Table (ZMod babyBearModulus) (fields 10)) (equation : Nat)
    (start : 0 ≤ equation) (stop : equation < 16) :
    ((gCpuPolynomials setup)[equation]'(by
      rw [g_cpu_polynomial_count]; omega)).eval
        (Verification.environment (machineAssignment variant 227)) = 0 := by
  apply g_cpu_equations_of_check (machineAssignment variant 227) setup
    0 16 equation start (by omega) (by omega)
  cases variant with
  | baseline => exact cpu_final_csr_checked_baseline_000_015
  | scratch => exact cpu_final_csr_checked_scratch_000_015
  | protectedMessage => exact cpu_final_csr_checked_protectedMessage_000_015

private theorem cpu_final_csr_checked_baseline_016_031 :
    gCpuEquationsCheck (machineAssignment .baseline 227)
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 16).take 16) = true := by
  decide +kernel

private theorem cpu_final_csr_checked_scratch_016_031 :
    gCpuEquationsCheck (machineAssignment .scratch 227)
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 16).take 16) = true := by
  decide +kernel

private theorem cpu_final_csr_checked_protectedMessage_016_031 :
    gCpuEquationsCheck (machineAssignment .protectedMessage 227)
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 16).take 16) = true := by
  decide +kernel

private theorem cpu_final_csr_016_031 (variant : Variant)
    (setup : Table (ZMod babyBearModulus) (fields 10)) (equation : Nat)
    (start : 16 ≤ equation) (stop : equation < 32) :
    ((gCpuPolynomials setup)[equation]'(by
      rw [g_cpu_polynomial_count]; omega)).eval
        (Verification.environment (machineAssignment variant 227)) = 0 := by
  apply g_cpu_equations_of_check (machineAssignment variant 227) setup
    16 16 equation start (by omega) (by omega)
  cases variant with
  | baseline => exact cpu_final_csr_checked_baseline_016_031
  | scratch => exact cpu_final_csr_checked_scratch_016_031
  | protectedMessage => exact cpu_final_csr_checked_protectedMessage_016_031

private theorem cpu_final_csr_checked_baseline_032_047 :
    gCpuEquationsCheck (machineAssignment .baseline 227)
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 32).take 16) = true := by
  decide +kernel

private theorem cpu_final_csr_checked_scratch_032_047 :
    gCpuEquationsCheck (machineAssignment .scratch 227)
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 32).take 16) = true := by
  decide +kernel

private theorem cpu_final_csr_checked_protectedMessage_032_047 :
    gCpuEquationsCheck (machineAssignment .protectedMessage 227)
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 32).take 16) = true := by
  decide +kernel

private theorem cpu_final_csr_032_047 (variant : Variant)
    (setup : Table (ZMod babyBearModulus) (fields 10)) (equation : Nat)
    (start : 32 ≤ equation) (stop : equation < 48) :
    ((gCpuPolynomials setup)[equation]'(by
      rw [g_cpu_polynomial_count]; omega)).eval
        (Verification.environment (machineAssignment variant 227)) = 0 := by
  apply g_cpu_equations_of_check (machineAssignment variant 227) setup
    32 16 equation start (by omega) (by omega)
  cases variant with
  | baseline => exact cpu_final_csr_checked_baseline_032_047
  | scratch => exact cpu_final_csr_checked_scratch_032_047
  | protectedMessage => exact cpu_final_csr_checked_protectedMessage_032_047

private theorem cpu_final_csr_checked_baseline_048_063 :
    gCpuEquationsCheck (machineAssignment .baseline 227)
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 48).take 16) = true := by
  decide +kernel

private theorem cpu_final_csr_checked_scratch_048_063 :
    gCpuEquationsCheck (machineAssignment .scratch 227)
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 48).take 16) = true := by
  decide +kernel

private theorem cpu_final_csr_checked_protectedMessage_048_063 :
    gCpuEquationsCheck (machineAssignment .protectedMessage 227)
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 48).take 16) = true := by
  decide +kernel

private theorem cpu_final_csr_048_063 (variant : Variant)
    (setup : Table (ZMod babyBearModulus) (fields 10)) (equation : Nat)
    (start : 48 ≤ equation) (stop : equation < 64) :
    ((gCpuPolynomials setup)[equation]'(by
      rw [g_cpu_polynomial_count]; omega)).eval
        (Verification.environment (machineAssignment variant 227)) = 0 := by
  apply g_cpu_equations_of_check (machineAssignment variant 227) setup
    48 16 equation start (by omega) (by omega)
  cases variant with
  | baseline => exact cpu_final_csr_checked_baseline_048_063
  | scratch => exact cpu_final_csr_checked_scratch_048_063
  | protectedMessage => exact cpu_final_csr_checked_protectedMessage_048_063

private theorem cpu_final_csr_checked_baseline_064_079 :
    gCpuEquationsCheck (machineAssignment .baseline 227)
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 64).take 16) = true := by
  decide +kernel

private theorem cpu_final_csr_checked_scratch_064_079 :
    gCpuEquationsCheck (machineAssignment .scratch 227)
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 64).take 16) = true := by
  decide +kernel

private theorem cpu_final_csr_checked_protectedMessage_064_079 :
    gCpuEquationsCheck (machineAssignment .protectedMessage 227)
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 64).take 16) = true := by
  decide +kernel

private theorem cpu_final_csr_064_079 (variant : Variant)
    (setup : Table (ZMod babyBearModulus) (fields 10)) (equation : Nat)
    (start : 64 ≤ equation) (stop : equation < 80) :
    ((gCpuPolynomials setup)[equation]'(by
      rw [g_cpu_polynomial_count]; omega)).eval
        (Verification.environment (machineAssignment variant 227)) = 0 := by
  apply g_cpu_equations_of_check (machineAssignment variant 227) setup
    64 16 equation start (by omega) (by omega)
  cases variant with
  | baseline => exact cpu_final_csr_checked_baseline_064_079
  | scratch => exact cpu_final_csr_checked_scratch_064_079
  | protectedMessage => exact cpu_final_csr_checked_protectedMessage_064_079

private theorem cpu_final_csr_checked_baseline_080_095 :
    gCpuEquationsCheck (machineAssignment .baseline 227)
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 80).take 16) = true := by
  decide +kernel

private theorem cpu_final_csr_checked_scratch_080_095 :
    gCpuEquationsCheck (machineAssignment .scratch 227)
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 80).take 16) = true := by
  decide +kernel

private theorem cpu_final_csr_checked_protectedMessage_080_095 :
    gCpuEquationsCheck (machineAssignment .protectedMessage 227)
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 80).take 16) = true := by
  decide +kernel

private theorem cpu_final_csr_080_095 (variant : Variant)
    (setup : Table (ZMod babyBearModulus) (fields 10)) (equation : Nat)
    (start : 80 ≤ equation) (stop : equation < 96) :
    ((gCpuPolynomials setup)[equation]'(by
      rw [g_cpu_polynomial_count]; omega)).eval
        (Verification.environment (machineAssignment variant 227)) = 0 := by
  apply g_cpu_equations_of_check (machineAssignment variant 227) setup
    80 16 equation start (by omega) (by omega)
  cases variant with
  | baseline => exact cpu_final_csr_checked_baseline_080_095
  | scratch => exact cpu_final_csr_checked_scratch_080_095
  | protectedMessage => exact cpu_final_csr_checked_protectedMessage_080_095

private theorem cpu_final_csr_checked_baseline_096_111 :
    gCpuEquationsCheck (machineAssignment .baseline 227)
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 96).take 16) = true := by
  decide +kernel

private theorem cpu_final_csr_checked_scratch_096_111 :
    gCpuEquationsCheck (machineAssignment .scratch 227)
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 96).take 16) = true := by
  decide +kernel

private theorem cpu_final_csr_checked_protectedMessage_096_111 :
    gCpuEquationsCheck (machineAssignment .protectedMessage 227)
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 96).take 16) = true := by
  decide +kernel

private theorem cpu_final_csr_096_111 (variant : Variant)
    (setup : Table (ZMod babyBearModulus) (fields 10)) (equation : Nat)
    (start : 96 ≤ equation) (stop : equation < 112) :
    ((gCpuPolynomials setup)[equation]'(by
      rw [g_cpu_polynomial_count]; omega)).eval
        (Verification.environment (machineAssignment variant 227)) = 0 := by
  apply g_cpu_equations_of_check (machineAssignment variant 227) setup
    96 16 equation start (by omega) (by omega)
  cases variant with
  | baseline => exact cpu_final_csr_checked_baseline_096_111
  | scratch => exact cpu_final_csr_checked_scratch_096_111
  | protectedMessage => exact cpu_final_csr_checked_protectedMessage_096_111

private theorem cpu_final_csr_checked_baseline_112_127 :
    gCpuEquationsCheck (machineAssignment .baseline 227)
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 112).take 16) = true := by
  decide +kernel

private theorem cpu_final_csr_checked_scratch_112_127 :
    gCpuEquationsCheck (machineAssignment .scratch 227)
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 112).take 16) = true := by
  decide +kernel

private theorem cpu_final_csr_checked_protectedMessage_112_127 :
    gCpuEquationsCheck (machineAssignment .protectedMessage 227)
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 112).take 16) = true := by
  decide +kernel

private theorem cpu_final_csr_112_127 (variant : Variant)
    (setup : Table (ZMod babyBearModulus) (fields 10)) (equation : Nat)
    (start : 112 ≤ equation) (stop : equation < 128) :
    ((gCpuPolynomials setup)[equation]'(by
      rw [g_cpu_polynomial_count]; omega)).eval
        (Verification.environment (machineAssignment variant 227)) = 0 := by
  apply g_cpu_equations_of_check (machineAssignment variant 227) setup
    112 16 equation start (by omega) (by omega)
  cases variant with
  | baseline => exact cpu_final_csr_checked_baseline_112_127
  | scratch => exact cpu_final_csr_checked_scratch_112_127
  | protectedMessage => exact cpu_final_csr_checked_protectedMessage_112_127

private theorem cpu_final_csr_checked_baseline_128_128 :
    gCpuEquationsCheck (machineAssignment .baseline 227)
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 128).take 1) = true := by
  decide +kernel

private theorem cpu_final_csr_checked_scratch_128_128 :
    gCpuEquationsCheck (machineAssignment .scratch 227)
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 128).take 1) = true := by
  decide +kernel

private theorem cpu_final_csr_checked_protectedMessage_128_128 :
    gCpuEquationsCheck (machineAssignment .protectedMessage 227)
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 128).take 1) = true := by
  decide +kernel

private theorem cpu_final_csr_128_128 (variant : Variant)
    (setup : Table (ZMod babyBearModulus) (fields 10)) (equation : Nat)
    (start : 128 ≤ equation) (stop : equation < 129) :
    ((gCpuPolynomials setup)[equation]'(by
      rw [g_cpu_polynomial_count]; omega)).eval
        (Verification.environment (machineAssignment variant 227)) = 0 := by
  apply g_cpu_equations_of_check (machineAssignment variant 227) setup
    128 1 equation start (by omega) (by omega)
  cases variant with
  | baseline => exact cpu_final_csr_checked_baseline_128_128
  | scratch => exact cpu_final_csr_checked_scratch_128_128
  | protectedMessage => exact cpu_final_csr_checked_protectedMessage_128_128

theorem cpu_final_csr_equation (variant : Variant)
    (setup : Table (ZMod babyBearModulus) (fields 10)) (equation : Nat)
    (bound : equation < 129) :
    ((gCpuPolynomials setup)[equation]'(by
      rw [g_cpu_polynomial_count]; omega)).eval
        (Verification.environment (machineAssignment variant 227)) = 0 := by
  by_cases piece0 : equation < 16
  · exact cpu_final_csr_000_015 variant setup equation (by omega) piece0
  by_cases piece16 : equation < 32
  · exact cpu_final_csr_016_031 variant setup equation (by omega) piece16
  by_cases piece32 : equation < 48
  · exact cpu_final_csr_032_047 variant setup equation (by omega) piece32
  by_cases piece48 : equation < 64
  · exact cpu_final_csr_048_063 variant setup equation (by omega) piece48
  by_cases piece64 : equation < 80
  · exact cpu_final_csr_064_079 variant setup equation (by omega) piece64
  by_cases piece80 : equation < 96
  · exact cpu_final_csr_080_095 variant setup equation (by omega) piece80
  by_cases piece96 : equation < 112
  · exact cpu_final_csr_096_111 variant setup equation (by omega) piece96
  by_cases piece112 : equation < 128
  · exact cpu_final_csr_112_127 variant setup equation (by omega) piece112
  exact cpu_final_csr_128_128 variant setup equation (by omega) bound

end Tests.PathGLoopNative
