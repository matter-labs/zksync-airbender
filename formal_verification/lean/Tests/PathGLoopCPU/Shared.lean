import Tests.PathGLoopNativeBase

namespace Tests.PathGLoopNative
open Airbender Trace Arithmetic Reference.RiscV.Sail Reference.Sail PathGLoopProgram
set_option warningAsError true
set_option Elab.async false

def gCpuPolynomials (setup : Table (ZMod babyBearModulus) (fields 10)) :
    List (Expression (ZMod babyBearModulus)) :=
  FlatOperation.constraints (UnifiedReduced.importedConstraints setup)

theorem g_cpu_polynomial_count (setup : Table (ZMod babyBearModulus) (fields 10)) :
    (gCpuPolynomials setup).length = 129 := by rfl

/-- Caller port1 is excluded by the actual previous definition. These two
projection facts prevent evaluation of an irrelevant full prefix ledger. -/

theorem cpu_loop_caller_previous (variant : Variant) (index : Fin 55) :
    previous variant (gapRow index 0) 1 = 0 := by
  simp [previous, gap_caller]

theorem cpu_final_caller_previous (variant : Variant) :
    previous variant 227 1 = 0 := by rfl

/-- Kernel-computed checks of actual imported expressions. Membership and
indexed access are recovered below without expanding those expressions in tactics. -/
def gCpuEquationsCheck (assignment : Nat → ZMod babyBearModulus)
    (expressions : List (Expression (ZMod babyBearModulus))) : Bool :=
  expressions.all fun expression =>
    decide (expression.eval (Verification.environment assignment) = 0)

/-- Removing lookup operations leaves the same actual129 polynomial list for
all modeled setups. This is a proved definitional equality, not a setup premise. -/
theorem g_cpu_polynomials_setup_independent
    (setup : Table (ZMod babyBearModulus) (fields 10)) :
    gCpuPolynomials setup =
      gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline)) := by
  rfl

/-- A checked finite chunk of that actual list gives each indexed equation.
The Boolean evidence is supplied by closed certificates in the fixture modules. -/
theorem g_cpu_equations_of_check (assignment : Nat → ZMod babyBearModulus)
    (setup : Table (ZMod babyBearModulus) (fields 10)) (first count equation : Nat)
    (start : first ≤ equation) (stop : equation < first + count) (actual : equation < 129)
    (checked : gCpuEquationsCheck assignment
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop first).take count) = true) :
    ((gCpuPolynomials setup)[equation]'(by
      rw [g_cpu_polynomial_count]; exact actual)).eval
        (Verification.environment assignment) = 0 := by
  have checkedAll : (((gCpuPolynomials setup).drop first).take count).all
      (fun expression => decide (expression.eval (Verification.environment assignment) = 0)) = true := by
    change gCpuEquationsCheck assignment (((gCpuPolynomials setup).drop first).take count) = true
    rw [g_cpu_polynomials_setup_independent setup]
    exact checked
  have inside : equation - first < (((gCpuPolynomials setup).drop first).take count).length := by
    simp only [List.length_take, List.length_drop, g_cpu_polynomial_count]
    omega
  have member := List.getElem_mem inside
  have evaluated := of_decide_eq_true (List.all_eq_true.mp checkedAll _ member)
  have selected : first + (equation - first) = equation := by omega
  simpa only [List.getElem_take, List.getElem_drop, selected] using evaluated

end Tests.PathGLoopNative
