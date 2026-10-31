import Airbender.Import.Compiler.LogicalRows.WordMemoryCached
import Airbender.Proofs.GKRProtocol.LogicalLookup
import Airbender.Proofs.GKRProtocol.MaterializedRangeNative.WordMemoryCached
import Airbender.Proofs.GKRProtocol.PhysicalClosedNative.WordMemoryCached

namespace Airbender.Compiler.PooledRowNative.WordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option linter.unusedVariables false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- The readable physical input contract has exactly the generated arithmetic
and execute-column interpretation; this equality changes no row condition. -/
theorem input_binding : Input = PhysicalRowInput
    (fun physical => ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.artifact.gates,
    gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) = 0)
    (fun physical => (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical (fun _ _ => #[])).get
    Airbender.WordMemory.importedConstraintsTraceColumns.execute = 1) := rfl

/-- The public address projection is exactly the retained generated Clean row
interpretation. This is a definitional binding, not an execution premise. -/
theorem inputRow_binding (input : Input) :
    inputRow input = (show Trace.Row babyBearModulus Trace.PooledFamily from
      ⟨.wordMemory, (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment input.physical (fun _ _ => #[])).get⟩) := rfl

/-- Explicit public column-group selection agrees with the retained captured
lookup reduction's group ordering. -/
theorem lookupArguments_binding (input : Input) : LookupArguments input =
    ((group : Fin 3) → LookupArgument
      (Airbender.Compiler.MaterializedNative.WordMemoryCached.native.model.fields
        (Airbender.Compiler.MaterializedWitnessNative.WordMemoryCached.setupColumns group))
      (activeLookupFields (nativeRequests input group))) := rfl

/-- Native base arithmetic transports the actual expanded operands to the
source-projected logical interface; none of the field equalities is a premise. -/
private theorem native_query15 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding15.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf15.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.query15.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.WordMemoryCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.sourceField15_0 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.sourceField15_1 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.sourceField15_2 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.sourceField15_3 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.sourceField15_4 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.sourceField15_5 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.sourceField15_6 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.sourceField15_7 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.sourceField15_8 input.physical copies) rfl))))))))) rfl).symm

private theorem native_query10 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding10.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf10.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.query10.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.WordMemoryCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.sourceField10_1 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.sourceField10_2 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.sourceField10_3 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.sourceField10_4 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.sourceField10_5 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.sourceField10_6 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.sourceField10_7 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.sourceField10_8 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.sourceField10_9 input.physical copies) rfl))))))))) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.sourceField10_0 input.physical copies)).symm

private theorem native_query14 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding14.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf14.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.query14.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.WordMemoryCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.sourceField14_0 input.physical copies) rfl) rfl).symm

private theorem native_query0 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding0.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf0.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.query0.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.WordMemoryCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.sourceField0_0 input.physical copies) rfl) rfl).symm

private theorem native_query12 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding12.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf12.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.query12.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.WordMemoryCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.sourceField12_0 input.physical copies) rfl) rfl).symm

private theorem native_timestamp0 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding2.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf2.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.WordMemoryCached.native.fields).get ⟨0, by decide⟩).value (Airbender.Compiler.HelperNative.WordMemoryCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.WordMemoryCached.native.candidate2).sound
    Airbender.Compiler.HelperNative.WordMemoryCached.native.placement Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank
    Airbender.Compiler.HelperNative.WordMemoryCached.native.checked2 Airbender.Compiler.HelperNative.WordMemoryCached.native.inBank2
    input.physical (Airbender.Compiler.FunctionalLinksNative.WordMemoryCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.timestampFieldMatch0] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.WordMemoryCached.native.recipe2.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp1 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding4.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf4.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.WordMemoryCached.native.fields).get ⟨1, by decide⟩).value (Airbender.Compiler.HelperNative.WordMemoryCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.WordMemoryCached.native.candidate4).sound
    Airbender.Compiler.HelperNative.WordMemoryCached.native.placement Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank
    Airbender.Compiler.HelperNative.WordMemoryCached.native.checked4 Airbender.Compiler.HelperNative.WordMemoryCached.native.inBank4
    input.physical (Airbender.Compiler.FunctionalLinksNative.WordMemoryCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.timestampFieldMatch1] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.WordMemoryCached.native.recipe4.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp2 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding5.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf5.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.WordMemoryCached.native.fields).get ⟨2, by decide⟩).value (Airbender.Compiler.HelperNative.WordMemoryCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.WordMemoryCached.native.candidate5).sound
    Airbender.Compiler.HelperNative.WordMemoryCached.native.placement Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank
    Airbender.Compiler.HelperNative.WordMemoryCached.native.checked5 Airbender.Compiler.HelperNative.WordMemoryCached.native.inBank5
    input.physical (Airbender.Compiler.FunctionalLinksNative.WordMemoryCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.timestampFieldMatch2] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.WordMemoryCached.native.recipe5.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp3 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding6.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf6.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.WordMemoryCached.native.fields).get ⟨3, by decide⟩).value (Airbender.Compiler.HelperNative.WordMemoryCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.WordMemoryCached.native.candidate6).sound
    Airbender.Compiler.HelperNative.WordMemoryCached.native.placement Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank
    Airbender.Compiler.HelperNative.WordMemoryCached.native.checked6 Airbender.Compiler.HelperNative.WordMemoryCached.native.inBank6
    input.physical (Airbender.Compiler.FunctionalLinksNative.WordMemoryCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.timestampFieldMatch3] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.WordMemoryCached.native.recipe6.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp4 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding7.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf7.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.WordMemoryCached.native.fields).get ⟨4, by decide⟩).value (Airbender.Compiler.HelperNative.WordMemoryCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.WordMemoryCached.native.candidate7).sound
    Airbender.Compiler.HelperNative.WordMemoryCached.native.placement Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank
    Airbender.Compiler.HelperNative.WordMemoryCached.native.checked7 Airbender.Compiler.HelperNative.WordMemoryCached.native.inBank7
    input.physical (Airbender.Compiler.FunctionalLinksNative.WordMemoryCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.timestampFieldMatch4] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.WordMemoryCached.native.recipe7.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp5 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding8.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf8.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.WordMemoryCached.native.fields).get ⟨5, by decide⟩).value (Airbender.Compiler.HelperNative.WordMemoryCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.WordMemoryCached.native.candidate8).sound
    Airbender.Compiler.HelperNative.WordMemoryCached.native.placement Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank
    Airbender.Compiler.HelperNative.WordMemoryCached.native.checked8 Airbender.Compiler.HelperNative.WordMemoryCached.native.inBank8
    input.physical (Airbender.Compiler.FunctionalLinksNative.WordMemoryCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.timestampFieldMatch5] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.WordMemoryCached.native.recipe8.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp6 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding9.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf9.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.WordMemoryCached.native.fields).get ⟨6, by decide⟩).value (Airbender.Compiler.HelperNative.WordMemoryCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.WordMemoryCached.native.candidate9).sound
    Airbender.Compiler.HelperNative.WordMemoryCached.native.placement Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank
    Airbender.Compiler.HelperNative.WordMemoryCached.native.checked9 Airbender.Compiler.HelperNative.WordMemoryCached.native.inBank9
    input.physical (Airbender.Compiler.FunctionalLinksNative.WordMemoryCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.timestampFieldMatch6] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.WordMemoryCached.native.recipe9.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp7 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding13.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf13.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.WordMemoryCached.native.fields).get ⟨7, by decide⟩).value (Airbender.Compiler.HelperNative.WordMemoryCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.WordMemoryCached.native.candidate13).sound
    Airbender.Compiler.HelperNative.WordMemoryCached.native.placement Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank
    Airbender.Compiler.HelperNative.WordMemoryCached.native.checked13 Airbender.Compiler.HelperNative.WordMemoryCached.native.inBank13
    input.physical (Airbender.Compiler.FunctionalLinksNative.WordMemoryCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.timestampFieldMatch7] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.WordMemoryCached.native.recipe13.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

/-- Native base arithmetic identifies each enabled expanded payload and mask
with its source interpretation, including every timestamp helper. -/
theorem nativeRequests_source (input : Input) (group : Fin 3) :
    nativeRequests input group = physicalRequests input group := by
  fin_cases group

  · change [MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding15.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf15.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding10.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf10.weight.value input.physical)] =
      [Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.query15.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.query10.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement)]
    exact (congrArg₂ List.cons (native_query15 input) (congrArg₂ List.cons (native_query10 input) rfl))

  · change [MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding14.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf14.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding0.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf0.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding12.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf12.weight.value input.physical)] =
      [Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.query14.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.query0.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.query12.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement)]
    exact (congrArg₂ List.cons (native_query14 input) (congrArg₂ List.cons (native_query0 input) (congrArg₂ List.cons (native_query12 input) rfl)))

  · change [MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding2.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf2.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding4.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf4.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding5.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf5.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding6.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf6.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding7.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf7.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding8.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf8.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding9.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf9.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding13.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf13.weight.value input.physical)] =
      [MaterializedQuery.mk [((Airbender.Compiler.HelperNative.WordMemoryCached.native.fields).get ⟨0, by decide⟩).value (Airbender.Compiler.HelperNative.WordMemoryCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.WordMemoryCached.native.fields).get ⟨1, by decide⟩).value (Airbender.Compiler.HelperNative.WordMemoryCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.WordMemoryCached.native.fields).get ⟨2, by decide⟩).value (Airbender.Compiler.HelperNative.WordMemoryCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.WordMemoryCached.native.fields).get ⟨3, by decide⟩).value (Airbender.Compiler.HelperNative.WordMemoryCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.WordMemoryCached.native.fields).get ⟨4, by decide⟩).value (Airbender.Compiler.HelperNative.WordMemoryCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.WordMemoryCached.native.fields).get ⟨5, by decide⟩).value (Airbender.Compiler.HelperNative.WordMemoryCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.WordMemoryCached.native.fields).get ⟨6, by decide⟩).value (Airbender.Compiler.HelperNative.WordMemoryCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.WordMemoryCached.native.fields).get ⟨7, by decide⟩).value (Airbender.Compiler.HelperNative.WordMemoryCached.native.sourceValues input.physical)] 1]
    exact (congrArg₂ List.cons (native_timestamp0 input) (congrArg₂ List.cons (native_timestamp1 input) (congrArg₂ List.cons (native_timestamp2 input) (congrArg₂ List.cons (native_timestamp3 input) (congrArg₂ List.cons (native_timestamp4 input) (congrArg₂ List.cons (native_timestamp5 input) (congrArg₂ List.cons (native_timestamp6 input) (congrArg₂ List.cons (native_timestamp7 input) rfl))))))))

/-- Every native query leaf occurs once, with the single setup leaf completing
exactly the retained native reduction tree's primitive multiset. -/
theorem nativeOperands_coverage (input : Input) (group : Fin 3) :
    (((nativeOperands input group).map Prod.fst) ++ [nativeSetupLeaf group]).Perm
      (([Airbender.Compiler.LookupNative.WordMemoryCached.native.genericTree,
      Airbender.Compiler.LookupNative.WordMemoryCached.native.range16Tree,
      Airbender.Compiler.LookupNative.WordMemoryCached.native.timestampTree]).get group).leaves := by
  fin_cases group

  · change ([15,
      10,
      11] : List Nat).Perm (Airbender.Compiler.LookupNative.WordMemoryCached.native.genericTree).leaves
    exact Eq.mpr (congrArg (fun leaves : List Nat => ([15,
      10,
      11] : List Nat).Perm leaves)
      Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.genericLeavesChecked) (by decide +kernel)

  · change ([14,
      0,
      12,
      1] : List Nat).Perm (Airbender.Compiler.LookupNative.WordMemoryCached.native.range16Tree).leaves
    exact Eq.mpr (congrArg (fun leaves : List Nat => ([14,
      0,
      12,
      1] : List Nat).Perm leaves)
      Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.range16LeavesChecked) (by decide +kernel)

  · change ([2,
      4,
      5,
      6,
      7,
      8,
      9,
      13,
      3] : List Nat).Perm (Airbender.Compiler.LookupNative.WordMemoryCached.native.timestampTree).leaves
    exact Eq.mpr (congrArg (fun leaves : List Nat => ([2,
      4,
      5,
      6,
      7,
      8,
      9,
      13,
      3] : List Nat).Perm leaves)
      Airbender.Compiler.HelperNative.WordMemoryCached.native.leavesChecked) (by decide +kernel)

/-- Each designated native setup operand contains precisely the columns used
by the literal setup table in the corresponding logical argument. -/
theorem nativeSetupColumns_binding (group : Fin 3) :
    ([Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding11.columns,
      Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding1.columns,
      Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding3.columns]).get group =
      (Airbender.Compiler.MaterializedWitnessNative.WordMemoryCached.setupColumns group).map
        (fun column => AffineProgram.input (Address := GKRAddress) (R := Nat) column.address) := by
  fin_cases group
  · exact Airbender.Compiler.TableNative.WordMemoryCached.native.genericSetupColumnsPreserved
  · exact Airbender.Compiler.TableNative.WordMemoryCached.native.range16SetupColumnsPreserved
  · exact Airbender.Compiler.TableNative.WordMemoryCached.native.timestampSetupColumnsPreserved

/-- Exact native matching supplies every enabled source tuple in the supplied
setup rows. Native arithmetic proves the operand transport. -/
theorem source_member_with
    (tables : Fin 3 → Fin Airbender.Compiler.MaterializedNative.WordMemoryCached.native.model.imported.data.length →
      List Source.BaseField) (input : Input) (arguments : LookupArgumentsWith tables input)
    (group : Fin 3) (query : MaterializedQuery)
    (member : query ∈ physicalRequests input group) (enabled : query.weight ≠ 0) :
    ∃ index, query.fields = tables group index := by
  apply LookupArgument.member (arguments group)
  change query.fields ∈ activeLookupFields (nativeRequests input group)
  rw [nativeRequests_source input group]
  exact activeLookupFields.member member enabled

private noncomputable def sourceArguments (input : Input) (arguments : LookupArguments input)
    (group : Fin 3) : LookupArgument
      (Airbender.Compiler.MaterializedNative.WordMemoryCached.native.model.fields
        (Airbender.Compiler.MaterializedWitnessNative.WordMemoryCached.setupColumns group))
      (activeLookupFields (physicalRequests input group)) := by
  simpa only [nativeRequests_source input group, Airbender.Compiler.MaterializedWitnessNative.WordMemoryCached.setupColumns] using arguments group
-- End native operand transport.

private theorem physical_member (input : Input) (arguments : LookupArguments input)
    (group : Fin 3) (query : MaterializedQuery)
    (member : query ∈ physicalRequests input group) (enabled : query.weight ≠ 0) :
    Airbender.Compiler.MaterializedNative.WordMemoryCached.native.model.Contains
      (Airbender.Compiler.MaterializedWitnessNative.WordMemoryCached.setupColumns group) query.fields :=
  LookupArgument.member (sourceArguments input arguments group) (activeLookupFields.member member enabled)

/-- Authored lookup membership is proved at physical coordinates, without a
canonical source frame, using exact matching of the emitted tuples. -/
theorem authored_from_arguments (input : Input) (arguments : LookupArguments input) :
    PhysicalAuthoredLookupValid input.physical := by
  constructor
  · intro query member enabled
    apply physical_member input arguments 0 (query.materialized
      ((input.physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement)) ?_ enabled
    simpa [physicalRequests] using
      (List.mem_map.mpr ⟨query, member, rfl⟩ :
        query.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement) ∈
          Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.genericQueries.map (fun item => item.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement)))
  · intro query member enabled
    apply physical_member input arguments 1 (query.materialized
      ((input.physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement)) ?_ enabled
    simpa [physicalRequests] using
      (List.mem_map.mpr ⟨query, member, rfl⟩ :
        query.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement) ∈
          Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.range16Queries.map (fun item => item.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement)))

/-- The complete literal timestamp column, including zero padding, bounds
actual physical helper values. No canonical borrow choice is imposed. -/
theorem helpers_from_arguments (input : Input) (arguments : LookupArguments input) :
    ∀ field ∈ Airbender.Compiler.HelperNative.WordMemoryCached.native.fields,
      (field.value (Airbender.Compiler.HelperNative.WordMemoryCached.native.sourceValues input.physical)).val < 524288 := by
  intro field member
  let value := field.value (Airbender.Compiler.HelperNative.WordMemoryCached.native.sourceValues input.physical)
  have present := physical_member input arguments 2 (MaterializedQuery.mk [value] 1)
    (by simpa [physicalRequests, value, Airbender.Compiler.HelperNative.WordMemoryCached.native.sourceValues] using
          (List.mem_map.mpr ⟨field, member, rfl⟩ :
            MaterializedQuery.mk [field.value (Airbender.Compiler.HelperNative.WordMemoryCached.native.sourceValues input.physical)] 1 ∈
              Airbender.Compiler.HelperNative.WordMemoryCached.native.fields.map (fun item => MaterializedQuery.mk
                [item.value (Airbender.Compiler.HelperNative.WordMemoryCached.native.sourceValues input.physical)] 1))) one_ne_zero
  change Airbender.Compiler.MaterializedNative.WordMemoryCached.native.model.Contains [.timestamp] [value] at present
  exact Airbender.Compiler.MaterializedRangeNative.WordMemoryCached.native.timestamp_bounded value present

theorem input_active (input : Input) :
    (inputRow input).assignment (inputRow input).columns.execute = 1 := input.active

end Airbender.Compiler.PooledRowNative.WordMemoryCached
