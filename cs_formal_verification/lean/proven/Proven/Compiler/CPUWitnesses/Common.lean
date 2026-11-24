module
public import Human.Compiler.NativePublicSetup
public import Proven.Compiler.LookupWitness
public import Proven.Compiler.Lookups.Bridge
public import Proven.Compiler.WorkerConstraints.Values
public import Mathlib.Tactic.FinCases

@[expose] public section
namespace Airbender.Compiler.CPUWitnesses
open NativeArithmetic Trace
set_option warningAsError true

/-- Read a canonical natural field value from a native tuple. -/
def field (values : List F) (index : Nat) : Nat := ((values[index]?).getD 0).val

/-- A candidate native setup row uses the tuple's public tag and keys. -/
noncomputable def rawIndex (family : RVMachineDecoderFamily) (group : Fin 3) (values : List F) : Nat :=
  if group.val ≠ 0 then field values 0 else
    let circuit := NativeLookups.circuitFor family
    let tag := field values (circuit.generic_lookup_tables_width - 1)
    let offset := ((circuit.table_offsets[tag]?).map (·.val)).getD 0
    if family = .pooled .addSub ∨ tag = 46 then
      circuit.offset_for_decoder_table + (field values 0 + 65536 * field values 1) / 4
    else if tag = 0 then 0
    else if tag ∈ [4, 6, 7, 8, 10, 47, 48, 49, 50, 52, 53, 54] then
      offset + field values 0 * 256 + field values 1
    else if tag = 9 then
      offset + field values 0 * 65536 + field values 1 * 256 + field values 2 * 8 + field values 3
    else if tag = 34 then offset + field values 0 / 4
    else if tag = 44 then offset + 4 * (field values 0 % 4194304 / 4) +
      2 * (field values 0 / 4194304 % 2) + field values 0 / 8388608 % 2
    else if tag = 45 then offset + 8 * (field values 0 % 4194304 / 4) +
      4 * (field values 0 / 4194304 % 2) + 2 * (field values 0 / 8388608 % 2) +
      field values 0 / 16777216 % 2
    else offset + field values 0

/-- Each captured CPU circuit has a positive native trace size. -/
theorem trace_positive (family : RVMachineDecoderFamily) :
    0 < (NativeLookups.circuitFor family).trace_len := by
  cases family with
  | pooled family => cases family <;> decide +kernel
  | unified => decide +kernel

/-- Candidate indices stay inside the actual native trace domain. -/
noncomputable def candidateIndex (family : RVMachineDecoderFamily) (group : Fin 3) (values : List F) :
    NativeSetupIndex family :=
  ⟨rawIndex family group values % (NativeLookups.circuitFor family).trace_len,
    Nat.mod_lt _ (trace_positive family)⟩

/-- Every retained logical tuple equals its selected canonical public setup row. -/
noncomputable def canonicalCheck (family : RVMachineDecoderFamily) (initial : RV.State)
    (program : List RVMachineProgramEntry) (tuples : Fin 3 → List (List F)) : Bool :=
  (List.finRange 3).all fun group => (tuples group).all fun values =>
    decide (values = NativePublicSetup.rows initial program family group (candidateIndex family group values))

/-- The closed tuple check supplies exact public table membership for each retained tuple. -/
theorem canonical_members {family : RVMachineDecoderFamily} {initial : RV.State}
    {program : List RVMachineProgramEntry} {tuples : Fin 3 → List (List F)}
    (checked : canonicalCheck family initial program tuples = true) :
    ∀ group values, values ∈ tuples group →
      ∃ index, values = NativePublicSetup.rows initial program family group index := by
  intro group values member
  have groupChecked := List.all_eq_true.mp checked group (List.mem_finRange group)
  exact ⟨candidateIndex family group values,
    of_decide_eq_true (List.all_eq_true.mp groupChecked values member)⟩

/-- Nonzero operand weights retain the complete native operand list. -/
theorem requests_of_enabled {circuit : Circuit} {selectors : List NativeLookups.Selector}
    (physical : GKRAddress → F) (group : Fin 3) (operands : List NativeLookups.Operand)
    (binding : (selectors.filter (fun selector => selector.group == group)).mapM
      (NativeLookups.select circuit) = .ok operands)
    (enabled : ∀ operand ∈ operands, operand.weight.value physical ≠ 0) :
    NativeLookups.requests circuit selectors physical group = .ok (operands.map fun operand => operand.input.fields physical) := by
  have retained : operands.filter (fun operand => operand.weight.value physical != 0) = operands := by
    apply List.filter_eq_self.mpr
    intro operand member
    exact bne_iff_ne.mpr (enabled operand member)
  unfold NativeLookups.requests
  rw [binding]
  exact congrArg (fun values => Except.ok (values.map fun operand => operand.input.fields physical)) retained

/-- Canonical tuple checks and exact selector binding construct the native lookup argument. -/
noncomputable def arguments_of_checked {family : RVMachineDecoderFamily} {physical : GKRAddress → F}
    {initial : RV.State} {program : List RVMachineProgramEntry} (tuples : Fin 3 → List (List F))
    (binding : ∀ group, NativeLookups.requests (NativeLookups.circuitFor family)
      (NativeLookups.selectorsFor family) physical group = .ok (tuples group))
    (checked : canonicalCheck family initial program tuples = true) :
    NativeLookups.Arguments (NativeLookups.circuitFor family) (NativeLookups.selectorsFor family)
      physical (NativePublicSetup.rows initial program family) where
  tuples := tuples
  binding := binding
  matching group := LookupArgument.of_membership (NativePublicSetup.rows initial program family group)
    (tuples group) (canonical_members checked group)

end Airbender.Compiler.CPUWitnesses
