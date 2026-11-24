module
public import Proven.Compiler.CPUWitnesses.Common

@[expose] public section
namespace Airbender.Compiler.CPUWitnesses
open NativeArithmetic
set_option warningAsError true

/-- A disabled first operand drops its tuple. Enabled later operands keep their tuples. -/
theorem requests_of_masked_head {circuit : Circuit} {selectors : List NativeLookups.Selector}
    (physical : GKRAddress → F) (group : Fin 3) (head : NativeLookups.Operand) (rest : List NativeLookups.Operand)
    (binding : (selectors.filter (fun selector => selector.group == group)).mapM
      (NativeLookups.select circuit) = .ok (head :: rest))
    (disabled : head.weight.value physical = 0)
    (enabled : ∀ operand ∈ rest, operand.weight.value physical ≠ 0) :
    NativeLookups.requests circuit selectors physical group = .ok (rest.map fun operand => operand.input.fields physical) := by
  have retained : rest.filter (fun operand => operand.weight.value physical != 0) = rest := by
    apply List.filter_eq_self.mpr
    intro operand member
    exact bne_iff_ne.mpr (enabled operand member)
  have dropped : (head :: rest).filter (fun operand => operand.weight.value physical != 0) = rest := by
    rw [List.filter_cons_of_neg (by simp [disabled]), retained]
  unfold NativeLookups.requests
  rw [binding]
  exact congrArg (fun values => Except.ok (values.map fun operand => operand.input.fields physical)) dropped

end Airbender.Compiler.CPUWitnesses
