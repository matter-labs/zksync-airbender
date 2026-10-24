import GKRProtocol.HelperSource

namespace Airbender.Compiler.Source
set_option warningAsError true

inductive HelperAssertion where
  | zero : HelperField → HelperAssertion
  | boolean : HelperField → HelperAssertion

def HelperAssertion.value (values : HelperValues) : HelperAssertion → BaseField
  | .zero field => field.value values
  | .boolean field => field.value values * (field.value values - 1)

def HelperAssertion.polynomial (placement : HelperPlacement n) : HelperAssertion → Compiler.Polynomial n BaseField
  | .zero field => field.polynomial placement
  | .boolean field => Compiler.multiply (field.polynomial placement)
      (Compiler.add (field.polynomial placement) (Compiler.constant (-1)))

theorem HelperAssertion.polynomial_value (assertion : HelperAssertion) (placement : HelperPlacement n)
    (values : Fin n → BaseField) :
    Compiler.evaluate values (assertion.polynomial placement) = assertion.value (placement.project values) := by
  cases assertion with
  | zero field => exact field.polynomial_value placement values
  | boolean field =>
      simp only [polynomial, value, Compiler.evaluate_multiply, Compiler.evaluate_add,
        Compiler.evaluate_constant, field.polynomial_value, sub_eq_add_neg]

/-- The backend adds executor clock advance and one Boolean subtraction borrow
per ungrouped memory access. These obligations are derived from source clocks
and histories in the helper completeness theorem. -/
def helperAssertions (inputs : SemanticInputs) : Except String (Array HelperAssertion) := do
  let requests ← helperRequests inputs
  let mut assertions : Array HelperAssertion := #[]
  if let some executor := inputs.executor_machine_state then
    let initial := MemoryWord.original executor.cycle_start_state.timestamp
    let final := MemoryWord.original executor.cycle_end_state.timestamp
    let carry : HelperField := .scale ((524288 : BaseField)⁻¹).val
      (.add (.add (.memory initial.low) (.memory (.constant 4))) (.neg (.memory final.low)))
    assertions := #[.boolean carry,
      .zero (.add (.add (.memory final.high) (.neg (.memory initial.high))) (.neg carry))]
  for index in [:requests.comparisons.size] do
    assertions := assertions.push (.boolean (.borrow index))
  return assertions

end Airbender.Compiler.Source
