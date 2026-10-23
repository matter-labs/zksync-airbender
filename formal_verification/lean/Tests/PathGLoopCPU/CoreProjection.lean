import Tests.PathGLoopCPU.LoopShared

namespace Tests.PathGLoopNative
open Airbender Trace Arithmetic Reference.RiscV.Sail Reference.Sail PathGLoopProgram
set_option warningAsError true
set_option Elab.async false

/-- Test-only projection: clocks remain in the actual rows and timestamp
checks; this assignment is used only through the proved core-evaluation bridge. -/
def gCpuCoreAssignment (assignment : Nat → ZMod babyBearModulus) (column : Nat) :
    ZMod babyBearModulus :=
  if column = 34 ∨ column = 40 ∨ column = 46 then 0 else assignment column

def gCpuHistoryFree : Expression (ZMod babyBearModulus) → Bool
  | .var wire => decide (wire.index ≠ 34 ∧ wire.index ≠ 40 ∧ wire.index ≠ 46)
  | .const _ => true
  | .add left right | .mul left right => gCpuHistoryFree left && gCpuHistoryFree right

/-- Structural evaluation congruence checks exactly which variables an
expression uses; it supplies no native-coordinate equality premise. -/
theorem g_cpu_history_free_eval (expression : Expression (ZMod babyBearModulus))
    (assignment : Nat → ZMod babyBearModulus) (free : gCpuHistoryFree expression = true) :
    expression.eval (Verification.environment (gCpuCoreAssignment assignment)) =
      expression.eval (Verification.environment assignment) := by
  induction expression with
  | var wire =>
    have different : wire.index ≠ 34 ∧ wire.index ≠ 40 ∧ wire.index ≠ 46 :=
      of_decide_eq_true free
    change (if wire.index = 34 ∨ wire.index = 40 ∨ wire.index = 46 then 0
      else assignment wire.index) = assignment wire.index
    apply if_neg
    intro selected
    rcases selected with selected | selected | selected
    · exact different.1 selected
    · exact different.2.1 selected
    · exact different.2.2 selected
  | const _ => rfl
  | add left right leftIH rightIH =>
    obtain ⟨leftFree, rightFree⟩ := Bool.and_eq_true_iff.mp free
    change left.eval _ + right.eval _ = left.eval _ + right.eval _
    rw [leftIH leftFree, rightIH rightFree]
  | mul left right leftIH rightIH =>
    obtain ⟨leftFree, rightFree⟩ := Bool.and_eq_true_iff.mp free
    change left.eval _ * right.eval _ = left.eval _ * right.eval _
    rw [leftIH leftFree, rightIH rightFree]

/-- Kernel certificates inspect the actual imported expression AST. The only
core use of a predecessor clock is assertion8, handled separately below. -/
private theorem g_cpu_history_free_prefix :
    ((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).take 8).all
      gCpuHistoryFree = true := by
  decide +kernel

private theorem g_cpu_history_free_suffix :
    ((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 9).all
      gCpuHistoryFree = true := by
  decide +kernel

theorem g_cpu_history_free_at (setup : Table (ZMod babyBearModulus) (fields 10))
    (equation : Nat) (bound : equation < 129) (different : equation ≠ 8) :
    gCpuHistoryFree ((gCpuPolynomials setup)[equation]'(by
      rw [g_cpu_polynomial_count]; exact bound)) = true := by
  change gCpuHistoryFree
    ((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline)))[equation]'(by rw [g_cpu_polynomial_count]; exact bound)) = true
  by_cases early : equation < 8
  · have inside : equation <
        ((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).take 8).length := by
      simp only [List.length_take, g_cpu_polynomial_count]
      omega
    have checked := List.all_eq_true.mp g_cpu_history_free_prefix _ (List.getElem_mem inside)
    simpa only [List.getElem_take] using checked
  · have inside : equation - 9 <
        ((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 9).length := by
      simp only [List.length_drop, g_cpu_polynomial_count]
      omega
    have checked := List.all_eq_true.mp g_cpu_history_free_suffix _ (List.getElem_mem inside)
    have selected : 9 + (equation - 9) = equation := by omega
    simpa only [List.getElem_drop, selected] using checked

/-- This is the exact emitted assertion8, including its product fold's unit. -/
theorem g_cpu_history_gate (assignment : Nat → ZMod babyBearModulus)
    (setup : Table (ZMod babyBearModulus) (fields 10)) :
    ((gCpuPolynomials setup)[8]'(by rw [g_cpu_polynomial_count]; decide)).eval
      (Verification.environment assignment) = (1 * assignment 40) * assignment 18 := by
  rfl

/-- Ordinary rows have zero caller selector, so the sole predecessor-clock
core equation is unchanged by the test-only coordinate projection. -/
theorem g_cpu_core_assignment_eval (assignment : Nat → ZMod babyBearModulus)
    (setup : Table (ZMod babyBearModulus) (fields 10))
    (equation : Nat) (bound : equation < 129) (ordinary : assignment 18 = 0) :
    ((gCpuPolynomials setup)[equation]'(by rw [g_cpu_polynomial_count]; exact bound)).eval
        (Verification.environment (gCpuCoreAssignment assignment)) =
      ((gCpuPolynomials setup)[equation]'(by rw [g_cpu_polynomial_count]; exact bound)).eval
        (Verification.environment assignment) := by
  by_cases eighth : equation = 8
  · subst equation
    rw [g_cpu_history_gate, g_cpu_history_gate]
    change (1 * 0) * assignment 18 = (1 * assignment 40) * assignment 18
    rw [ordinary]
    simp only [mul_zero]
  · exact g_cpu_history_free_eval _ assignment (g_cpu_history_free_at setup equation bound eighth)

theorem g_cpu_core_equations_of_check (assignment : Nat → ZMod babyBearModulus)
    (setup : Table (ZMod babyBearModulus) (fields 10)) (first count equation : Nat)
    (start : first ≤ equation) (stop : equation < first + count) (actual : equation < 129)
    (ordinary : assignment 18 = 0)
    (checked : gCpuEquationsCheck (gCpuCoreAssignment assignment)
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop first).take count) = true) :
    ((gCpuPolynomials setup)[equation]'(by rw [g_cpu_polynomial_count]; exact actual)).eval
      (Verification.environment assignment) = 0 := by
  rw [← g_cpu_core_assignment_eval assignment setup equation actual ordinary]
  exact g_cpu_equations_of_check (gCpuCoreAssignment assignment) setup first count equation
    start stop actual checked

/-- Original decoder fields at the actual loop JAL position give the zero
caller selector for every index and variant. -/
theorem g_cpu_jal_ordinary (variant : Variant) (index : Fin 55) :
    machineAssignment variant (gapRow index 1) 18 = 0 := by
  have caller : isCaller (gapRow index 1) = false := gap_caller index 1
  have code : rowCodeIndex (gapRow index 1) = (7 : Fin 12) := loop_row_index index 1
  change (if (metadata variant (gapRow index 1)).mask.testBit 7 then 1 else 0) = 0
  unfold metadata
  rw [caller, code]
  cases variant <;> rfl

end Tests.PathGLoopNative
