import Airbender.Review.Compiler.LookupOperands
import Airbender.Proofs.GKRProtocol.MemoryRequests

namespace Airbender.Compiler.Source
set_option warningAsError true

def HelperField.polynomial (placement : HelperPlacement n) : HelperField → Compiler.Polynomial n BaseField
  | .memory field => field.polynomial placement.memory
  | .borrow index => Compiler.atom (placement.borrow index)
  | .add left right => Compiler.add (left.polynomial placement) (right.polynomial placement)
  | .scale coefficient field => Compiler.multiply (Compiler.constant coefficient) (field.polynomial placement)
  | .neg field => Compiler.negate (field.polynomial placement)

theorem HelperField.polynomial_value (field : HelperField) (placement : HelperPlacement n)
    (values : Fin n → BaseField) :
    Compiler.evaluate values (field.polynomial placement) = field.value (placement.project values) := by
  induction field with
  | memory field => exact field.polynomial_value placement.memory values
  | borrow index => exact Compiler.evaluate_atom _ _
  | add left right leftProof rightProof =>
      simpa only [polynomial, value, Compiler.evaluate_add] using congrArg₂ (· + ·) leftProof rightProof
  | scale coefficient field proof =>
      simpa only [polynomial, value, Compiler.evaluate_multiply, Compiler.evaluate_constant] using
        congrArg ((coefficient : BaseField) * ·) proof
  | neg field proof => simpa only [polynomial, value, Compiler.evaluate_negate] using congrArg Neg.neg proof

def HelperField.referencesValid (originalVariables historySlots teardownSlots borrows : Nat)
    (hasInitialization : Bool) : HelperField → Bool
  | .memory field => field.referencesValid originalVariables historySlots teardownSlots hasInitialization
  | .borrow index => index < borrows
  | .add left right => referencesValid originalVariables historySlots teardownSlots borrows hasInitialization left &&
      referencesValid originalVariables historySlots teardownSlots borrows hasInitialization right
  | .scale _ field | .neg field => referencesValid originalVariables historySlots teardownSlots borrows hasInitialization field

def comparisonFields (previous current : MemoryWord) (borrow : Nat) : HelperField × HelperField :=
  (.add (.add (.memory previous.low) (.neg (.memory current.low))) (.scale 524288 (.borrow borrow)),
   .add (.add (.add (.memory previous.high) (.memory (.constant 524288)))
     (.neg (.memory current.high))) (.neg (.borrow borrow)))

structure HelperRequests where
  comparisons : Array (MemoryWord × MemoryWord)
  timestamps : Array HelperField

/-- Derive clock and alignment range queries from source memory operations.
Current production inputs have no grouped read timestamps. Unsupported groups
are rejected instead of treating their helper equations as source assumptions. -/
def helperRequests (inputs : SemanticInputs) : Except String HelperRequests := do
  unless inputs.read_timestamp_group_distances.entries.isEmpty do
    throw "grouped source timestamps require a separate helper proof"
  for access in inputs.register_and_indirect_accesses do
    unless access.read_timestamp_group.isNone do throw "grouped register timestamp requires a separate helper proof"
    for indirect in access.indirect_accesses do
      let group := match indirect with
        | .Read _ _ _ _ group | .Write _ _ _ _ _ group => group
      unless group.isNone do throw "grouped indirect timestamp requires a separate helper proof"
  let memory ← memoryRequests inputs
  let count := memory.reads.size - 1 -- exclude the PC/delegation marker
  let comparisons := (memory.reads.extract 0 count).zip (memory.writes.extract 0 count)
    |>.map (fun rows => (rows.1.timestamp, rows.2.timestamp))
  let mut timestamps : Array HelperField := #[]
  match inputs.executor_machine_state, inputs.delegation_circuit_state with
  | some executor, none =>
      let final := MemoryWord.original executor.cycle_end_state.timestamp
      timestamps := #[.memory final.low, .memory final.high]
  | none, some delegation =>
      let low := MemoryWord.original delegation.invocation_timestamp
      timestamps := #[.scale ((4 : BaseField)⁻¹).val
        (.add (.memory low.low) (.neg (.memory (.input (.Variable delegation.execute)))))]
  | _, _ => throw "source helper clock profile is ambiguous"
  for index in [:comparisons.size] do
    let some (previous, current) := comparisons[index]? | throw "missing source timestamp comparison"
    let fields := comparisonFields previous current index
    timestamps := timestamps ++ #[fields.1, fields.2]
  for access in inputs.register_and_indirect_accesses do
    let bits := access.indirects_alignment_log2.val
    if bits != 0 then
      unless bits < 16 && !access.indirect_accesses.isEmpty &&
          2 ^ (bits + 19) < babyBearModulus do throw "source alignment exceeds native field capacity"
      let read := match access.register_access with
        | .Read value | .Write value _ => value
      timestamps := timestamps.push (.scale (((2 ^ bits : Nat) : BaseField)⁻¹).val
        (.memory (MemoryWord.original read).low))
  return ⟨comparisons, timestamps⟩

end Airbender.Compiler.Source
