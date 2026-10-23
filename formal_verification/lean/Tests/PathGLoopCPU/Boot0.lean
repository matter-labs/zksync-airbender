import Tests.PathGLoopCPU.Shared

namespace Tests.PathGLoopNative
open Airbender Trace Arithmetic Reference.RiscV.Sail Reference.Sail PathGLoopProgram
set_option warningAsError true
set_option Elab.async false

/- All129 actual boot-row0 assertions, certified in nine closed chunks.
   Setup queries remain a separate obligation; each transport below is proved. -/

private def cpu_boot0_equations_check (assignment : Nat → ZMod babyBearModulus)
    (expressions : List (Expression (ZMod babyBearModulus))) : Bool :=
  expressions.all fun expression =>
    decide (expression.eval (Verification.environment assignment) = 0)

private theorem cpu_boot0_assignment (variant : Variant) :
    machineAssignment variant 0 = machineAssignment .baseline 0 := by
  cases variant <;> rfl

private theorem cpu_boot0_equations_of_check (variant : Variant)
    (setup : Table (ZMod babyBearModulus) (fields 10)) (first count equation : Nat)
    (start : first ≤ equation) (stop : equation < first + count) (actual : equation < 129)
    (projection : ((gCpuPolynomials setup).drop first).take count =
      ((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop first).take count)
    (checked : cpu_boot0_equations_check (machineAssignment .baseline 0)
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop first).take count) = true) :
    ((gCpuPolynomials setup)[equation]'(by
      rw [g_cpu_polynomial_count]; exact actual)).eval
        (Verification.environment (machineAssignment variant 0)) = 0 := by
  have checkedAll : (((gCpuPolynomials setup).drop first).take count).all
      (fun expression => decide
        (expression.eval (Verification.environment (machineAssignment variant 0)) = 0)) = true := by
    change cpu_boot0_equations_check (machineAssignment variant 0)
      (((gCpuPolynomials setup).drop first).take count) = true
    rw [projection, cpu_boot0_assignment variant]
    exact checked
  have inside : equation - first < (((gCpuPolynomials setup).drop first).take count).length := by
    simp only [List.length_take, List.length_drop, g_cpu_polynomial_count]
    omega
  have member := List.getElem_mem inside
  have evaluated := of_decide_eq_true (List.all_eq_true.mp checkedAll _ member)
  have selected : first + (equation - first) = equation := by omega
  simpa only [List.getElem_take, List.getElem_drop, selected] using evaluated

private theorem cpu_boot0_projection_000_015
    (setup : Table (ZMod babyBearModulus) (fields 10)) :
    ((gCpuPolynomials setup).drop 0).take 16 =
      ((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 0).take 16 := by
  rfl

private theorem cpu_boot0_checked_000_015 :
    cpu_boot0_equations_check (machineAssignment .baseline 0)
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 0).take 16) = true := by
  decide +kernel

private theorem cpu_boot_row0_000_015 (variant : Variant)
    (setup : Table (ZMod babyBearModulus) (fields 10)) (equation : Nat)
    (start : 0 ≤ equation) (stop : equation < 16) :
    ((gCpuPolynomials setup)[equation]'(by
      rw [g_cpu_polynomial_count]; omega)).eval
        (Verification.environment (machineAssignment variant 0)) = 0 := by
  exact cpu_boot0_equations_of_check variant setup 0 16 equation start (by omega) (by omega)
    (cpu_boot0_projection_000_015 setup) cpu_boot0_checked_000_015

private theorem cpu_boot0_projection_016_031
    (setup : Table (ZMod babyBearModulus) (fields 10)) :
    ((gCpuPolynomials setup).drop 16).take 16 =
      ((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 16).take 16 := by
  rfl

private theorem cpu_boot0_checked_016_031 :
    cpu_boot0_equations_check (machineAssignment .baseline 0)
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 16).take 16) = true := by
  decide +kernel

private theorem cpu_boot_row0_016_031 (variant : Variant)
    (setup : Table (ZMod babyBearModulus) (fields 10)) (equation : Nat)
    (start : 16 ≤ equation) (stop : equation < 32) :
    ((gCpuPolynomials setup)[equation]'(by
      rw [g_cpu_polynomial_count]; omega)).eval
        (Verification.environment (machineAssignment variant 0)) = 0 := by
  exact cpu_boot0_equations_of_check variant setup 16 16 equation start (by omega) (by omega)
    (cpu_boot0_projection_016_031 setup) cpu_boot0_checked_016_031

private theorem cpu_boot0_projection_032_047
    (setup : Table (ZMod babyBearModulus) (fields 10)) :
    ((gCpuPolynomials setup).drop 32).take 16 =
      ((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 32).take 16 := by
  rfl

private theorem cpu_boot0_checked_032_047 :
    cpu_boot0_equations_check (machineAssignment .baseline 0)
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 32).take 16) = true := by
  decide +kernel

private theorem cpu_boot_row0_032_047 (variant : Variant)
    (setup : Table (ZMod babyBearModulus) (fields 10)) (equation : Nat)
    (start : 32 ≤ equation) (stop : equation < 48) :
    ((gCpuPolynomials setup)[equation]'(by
      rw [g_cpu_polynomial_count]; omega)).eval
        (Verification.environment (machineAssignment variant 0)) = 0 := by
  exact cpu_boot0_equations_of_check variant setup 32 16 equation start (by omega) (by omega)
    (cpu_boot0_projection_032_047 setup) cpu_boot0_checked_032_047

private theorem cpu_boot0_projection_048_063
    (setup : Table (ZMod babyBearModulus) (fields 10)) :
    ((gCpuPolynomials setup).drop 48).take 16 =
      ((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 48).take 16 := by
  rfl

private theorem cpu_boot0_checked_048_063 :
    cpu_boot0_equations_check (machineAssignment .baseline 0)
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 48).take 16) = true := by
  decide +kernel

private theorem cpu_boot_row0_048_063 (variant : Variant)
    (setup : Table (ZMod babyBearModulus) (fields 10)) (equation : Nat)
    (start : 48 ≤ equation) (stop : equation < 64) :
    ((gCpuPolynomials setup)[equation]'(by
      rw [g_cpu_polynomial_count]; omega)).eval
        (Verification.environment (machineAssignment variant 0)) = 0 := by
  exact cpu_boot0_equations_of_check variant setup 48 16 equation start (by omega) (by omega)
    (cpu_boot0_projection_048_063 setup) cpu_boot0_checked_048_063

private theorem cpu_boot0_projection_064_079
    (setup : Table (ZMod babyBearModulus) (fields 10)) :
    ((gCpuPolynomials setup).drop 64).take 16 =
      ((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 64).take 16 := by
  rfl

private theorem cpu_boot0_checked_064_079 :
    cpu_boot0_equations_check (machineAssignment .baseline 0)
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 64).take 16) = true := by
  decide +kernel

private theorem cpu_boot_row0_064_079 (variant : Variant)
    (setup : Table (ZMod babyBearModulus) (fields 10)) (equation : Nat)
    (start : 64 ≤ equation) (stop : equation < 80) :
    ((gCpuPolynomials setup)[equation]'(by
      rw [g_cpu_polynomial_count]; omega)).eval
        (Verification.environment (machineAssignment variant 0)) = 0 := by
  exact cpu_boot0_equations_of_check variant setup 64 16 equation start (by omega) (by omega)
    (cpu_boot0_projection_064_079 setup) cpu_boot0_checked_064_079

private theorem cpu_boot0_projection_080_095
    (setup : Table (ZMod babyBearModulus) (fields 10)) :
    ((gCpuPolynomials setup).drop 80).take 16 =
      ((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 80).take 16 := by
  rfl

private theorem cpu_boot0_checked_080_095 :
    cpu_boot0_equations_check (machineAssignment .baseline 0)
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 80).take 16) = true := by
  decide +kernel

private theorem cpu_boot_row0_080_095 (variant : Variant)
    (setup : Table (ZMod babyBearModulus) (fields 10)) (equation : Nat)
    (start : 80 ≤ equation) (stop : equation < 96) :
    ((gCpuPolynomials setup)[equation]'(by
      rw [g_cpu_polynomial_count]; omega)).eval
        (Verification.environment (machineAssignment variant 0)) = 0 := by
  exact cpu_boot0_equations_of_check variant setup 80 16 equation start (by omega) (by omega)
    (cpu_boot0_projection_080_095 setup) cpu_boot0_checked_080_095

private theorem cpu_boot0_projection_096_111
    (setup : Table (ZMod babyBearModulus) (fields 10)) :
    ((gCpuPolynomials setup).drop 96).take 16 =
      ((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 96).take 16 := by
  rfl

private theorem cpu_boot0_checked_096_111 :
    cpu_boot0_equations_check (machineAssignment .baseline 0)
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 96).take 16) = true := by
  decide +kernel

private theorem cpu_boot_row0_096_111 (variant : Variant)
    (setup : Table (ZMod babyBearModulus) (fields 10)) (equation : Nat)
    (start : 96 ≤ equation) (stop : equation < 112) :
    ((gCpuPolynomials setup)[equation]'(by
      rw [g_cpu_polynomial_count]; omega)).eval
        (Verification.environment (machineAssignment variant 0)) = 0 := by
  exact cpu_boot0_equations_of_check variant setup 96 16 equation start (by omega) (by omega)
    (cpu_boot0_projection_096_111 setup) cpu_boot0_checked_096_111

private theorem cpu_boot0_projection_112_127
    (setup : Table (ZMod babyBearModulus) (fields 10)) :
    ((gCpuPolynomials setup).drop 112).take 16 =
      ((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 112).take 16 := by
  rfl

private theorem cpu_boot0_checked_112_127 :
    cpu_boot0_equations_check (machineAssignment .baseline 0)
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 112).take 16) = true := by
  decide +kernel

private theorem cpu_boot_row0_112_127 (variant : Variant)
    (setup : Table (ZMod babyBearModulus) (fields 10)) (equation : Nat)
    (start : 112 ≤ equation) (stop : equation < 128) :
    ((gCpuPolynomials setup)[equation]'(by
      rw [g_cpu_polynomial_count]; omega)).eval
        (Verification.environment (machineAssignment variant 0)) = 0 := by
  exact cpu_boot0_equations_of_check variant setup 112 16 equation start (by omega) (by omega)
    (cpu_boot0_projection_112_127 setup) cpu_boot0_checked_112_127

private theorem cpu_boot0_projection_128_128
    (setup : Table (ZMod babyBearModulus) (fields 10)) :
    ((gCpuPolynomials setup).drop 128).take 1 =
      ((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 128).take 1 := by
  rfl

private theorem cpu_boot0_checked_128_128 :
    cpu_boot0_equations_check (machineAssignment .baseline 0)
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 128).take 1) = true := by
  decide +kernel

private theorem cpu_boot_row0_128_128 (variant : Variant)
    (setup : Table (ZMod babyBearModulus) (fields 10)) (equation : Nat)
    (start : 128 ≤ equation) (stop : equation < 129) :
    ((gCpuPolynomials setup)[equation]'(by
      rw [g_cpu_polynomial_count]; omega)).eval
        (Verification.environment (machineAssignment variant 0)) = 0 := by
  exact cpu_boot0_equations_of_check variant setup 128 1 equation start (by omega) (by omega)
    (cpu_boot0_projection_128_128 setup) cpu_boot0_checked_128_128

theorem cpu_boot_row0_equation (variant : Variant)
    (setup : Table (ZMod babyBearModulus) (fields 10)) (equation : Nat)
    (bound : equation < 129) :
    ((gCpuPolynomials setup)[equation]'(by
      rw [g_cpu_polynomial_count]; omega)).eval
        (Verification.environment (machineAssignment variant 0)) = 0 := by
  by_cases piece0 : equation < 16
  · exact cpu_boot_row0_000_015 variant setup equation (by omega) piece0
  by_cases piece16 : equation < 32
  · exact cpu_boot_row0_016_031 variant setup equation (by omega) piece16
  by_cases piece32 : equation < 48
  · exact cpu_boot_row0_032_047 variant setup equation (by omega) piece32
  by_cases piece48 : equation < 64
  · exact cpu_boot_row0_048_063 variant setup equation (by omega) piece48
  by_cases piece64 : equation < 80
  · exact cpu_boot_row0_064_079 variant setup equation (by omega) piece64
  by_cases piece80 : equation < 96
  · exact cpu_boot_row0_080_095 variant setup equation (by omega) piece80
  by_cases piece96 : equation < 112
  · exact cpu_boot_row0_096_111 variant setup equation (by omega) piece96
  by_cases piece112 : equation < 128
  · exact cpu_boot_row0_112_127 variant setup equation (by omega) piece112
  exact cpu_boot_row0_128_128 variant setup equation (by omega) bound

end Tests.PathGLoopNative
