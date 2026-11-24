module
public import Proven.Compiler.NativeBridge
public import Human.Helpers.Properties

@[expose] public section
namespace Airbender.Compiler.DescriptionBridge
open NativeArithmetic
set_option warningAsError true

/-- Preserve the source variable indices in the reviewed expression type. -/
def toClean : Compiler.Expression n F → Airbender.Expression F
  | .constant value => .const value
  | .atom index => .var ⟨index.val⟩
  | .add left right => .add (toClean left) (toClean right)
  | .mul left right => .mul (toClean left) (toClean right)

/-- Both expression types evaluate the same source columns. -/
theorem value (expression : Compiler.Expression n F) (logical : Nat → F) :
    (toClean expression).eval (Verification.environment logical) =
      expression.value (fun index => logical index.val) := by
  induction expression with
  | constant _ => rfl
  | atom _ => rfl
  | add left right ihLeft ihRight => exact congrArg₂ (· + ·) ihLeft ihRight
  | mul left right ihLeft ihRight => exact congrArg₂ (· * ·) ihLeft ihRight

/-- A typed source equation list supplies the same reviewed flat assertions. -/
theorem assertions (source : List (Compiler.Expression n F)) (logical : Nat → F)
    (holds : ∀ expression ∈ source, expression.value (fun index => logical index.val) = 0) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment logical)
      (source.map (fun expression => FlatOperation.assert (toClean expression))) := by
  induction source with
  | nil => trivial
  | cons head tail ih =>
      refine ⟨(value head logical).trans (holds head List.mem_cons_self), ?_⟩
      exact ih (fun expression member => holds expression (List.mem_cons_of_mem _ member))

end Airbender.Compiler.DescriptionBridge
