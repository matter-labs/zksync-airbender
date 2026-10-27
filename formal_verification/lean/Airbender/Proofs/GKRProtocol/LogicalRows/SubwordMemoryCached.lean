import Airbender.Import.Compiler.LogicalRows.SubwordMemoryCached
import Airbender.Proofs.GKRProtocol.LogicalLookup
import Airbender.Proofs.GKRProtocol.MaterializedRangeNative.SubwordMemoryCached
import Airbender.Proofs.GKRProtocol.PhysicalClosedNative.SubwordMemoryCached
import Airbender.Proofs.GKRProtocol.PooledRowNative.SubwordMemoryCached

namespace Airbender.Compiler.PooledRowNative.SubwordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option linter.unusedVariables false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- The readable physical input contract has exactly the generated arithmetic
and execute-column interpretation; this equality changes no row condition. -/
theorem input_binding : Input = PhysicalRowInput
    (fun physical => ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.gates,
    gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0)
    (fun physical => (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical (fun _ _ => #[])).get
    Airbender.SubwordMemory.importedConstraintsTraceColumns.execute = 1) := rfl

/-- The public address projection is exactly the retained generated Clean row
interpretation. This is a definitional binding, not an execution premise. -/
theorem inputRow_binding (input : Input) :
    inputRow input = (show Trace.Row babyBearModulus Trace.PooledFamily from
      ⟨.subwordMemory, (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment input.physical (fun _ _ => #[])).get⟩) := rfl

/-- Explicit public column-group selection agrees with the retained captured
lookup reduction's group ordering. -/
theorem lookupArguments_binding (input : Input) : LookupArguments input =
    ((group : Fin 3) → LookupArgument
      (Airbender.Compiler.MaterializedNative.SubwordMemoryCached.native.model.fields
        (Airbender.Compiler.MaterializedWitnessNative.SubwordMemoryCached.setupColumns group))
      (activeLookupFields (nativeRequests input group))) := rfl

/-- Native base arithmetic transports the actual expanded operands to the
source-projected logical interface; none of the field equalities is a premise. -/
private theorem native_query17 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding17.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf17.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query17.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.SubwordMemoryCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField17_0 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField17_1 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField17_2 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField17_3 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField17_4 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField17_5 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField17_6 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField17_7 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField17_8 input.physical copies) rfl))))))))) rfl).symm

private theorem native_query18 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding18.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf18.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query18.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.SubwordMemoryCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField18_0 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField18_1 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField18_2 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField18_3 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField18_4 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField18_5 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField18_6 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField18_7 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField18_8 input.physical copies) rfl))))))))) rfl).symm

private theorem native_query12 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding12.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf12.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query12.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.SubwordMemoryCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField12_1 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField12_2 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField12_3 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField12_4 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField12_5 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField12_6 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField12_7 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField12_8 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField12_9 input.physical copies) rfl))))))))) (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField12_0 input.physical copies)).symm

private theorem native_query14 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding14.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf14.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query14.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.SubwordMemoryCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField14_0 input.physical copies) rfl) rfl).symm

private theorem native_query0 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding0.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf0.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query0.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.SubwordMemoryCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField0_0 input.physical copies) rfl) rfl).symm

private theorem native_query15 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding15.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf15.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query15.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.SubwordMemoryCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField15_0 input.physical copies) rfl) rfl).symm

private theorem native_query2 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding2.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf2.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query2.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.SubwordMemoryCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField2_0 input.physical copies) rfl) rfl).symm

private theorem native_query3 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding3.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf3.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query3.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.SubwordMemoryCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField3_0 input.physical copies) rfl) rfl).symm

private theorem native_timestamp0 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding4.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf4.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields).get ⟨0, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.candidate4).sound
    Airbender.Compiler.HelperNative.SubwordMemoryCached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank
    Airbender.Compiler.HelperNative.SubwordMemoryCached.native.checked4 Airbender.Compiler.HelperNative.SubwordMemoryCached.native.inBank4
    input.physical (Airbender.Compiler.FunctionalLinksNative.SubwordMemoryCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.timestampFieldMatch0] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.SubwordMemoryCached.native.recipe4.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp1 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding6.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf6.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields).get ⟨1, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.candidate6).sound
    Airbender.Compiler.HelperNative.SubwordMemoryCached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank
    Airbender.Compiler.HelperNative.SubwordMemoryCached.native.checked6 Airbender.Compiler.HelperNative.SubwordMemoryCached.native.inBank6
    input.physical (Airbender.Compiler.FunctionalLinksNative.SubwordMemoryCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.timestampFieldMatch1] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.SubwordMemoryCached.native.recipe6.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp2 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding7.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf7.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields).get ⟨2, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.candidate7).sound
    Airbender.Compiler.HelperNative.SubwordMemoryCached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank
    Airbender.Compiler.HelperNative.SubwordMemoryCached.native.checked7 Airbender.Compiler.HelperNative.SubwordMemoryCached.native.inBank7
    input.physical (Airbender.Compiler.FunctionalLinksNative.SubwordMemoryCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.timestampFieldMatch2] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.SubwordMemoryCached.native.recipe7.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp3 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding8.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf8.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields).get ⟨3, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.candidate8).sound
    Airbender.Compiler.HelperNative.SubwordMemoryCached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank
    Airbender.Compiler.HelperNative.SubwordMemoryCached.native.checked8 Airbender.Compiler.HelperNative.SubwordMemoryCached.native.inBank8
    input.physical (Airbender.Compiler.FunctionalLinksNative.SubwordMemoryCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.timestampFieldMatch3] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.SubwordMemoryCached.native.recipe8.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp4 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding9.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf9.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields).get ⟨4, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.candidate9).sound
    Airbender.Compiler.HelperNative.SubwordMemoryCached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank
    Airbender.Compiler.HelperNative.SubwordMemoryCached.native.checked9 Airbender.Compiler.HelperNative.SubwordMemoryCached.native.inBank9
    input.physical (Airbender.Compiler.FunctionalLinksNative.SubwordMemoryCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.timestampFieldMatch4] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.SubwordMemoryCached.native.recipe9.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp5 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding10.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf10.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields).get ⟨5, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.candidate10).sound
    Airbender.Compiler.HelperNative.SubwordMemoryCached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank
    Airbender.Compiler.HelperNative.SubwordMemoryCached.native.checked10 Airbender.Compiler.HelperNative.SubwordMemoryCached.native.inBank10
    input.physical (Airbender.Compiler.FunctionalLinksNative.SubwordMemoryCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.timestampFieldMatch5] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.SubwordMemoryCached.native.recipe10.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp6 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding11.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf11.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields).get ⟨6, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.candidate11).sound
    Airbender.Compiler.HelperNative.SubwordMemoryCached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank
    Airbender.Compiler.HelperNative.SubwordMemoryCached.native.checked11 Airbender.Compiler.HelperNative.SubwordMemoryCached.native.inBank11
    input.physical (Airbender.Compiler.FunctionalLinksNative.SubwordMemoryCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.timestampFieldMatch6] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.SubwordMemoryCached.native.recipe11.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp7 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding16.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf16.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields).get ⟨7, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.candidate16).sound
    Airbender.Compiler.HelperNative.SubwordMemoryCached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank
    Airbender.Compiler.HelperNative.SubwordMemoryCached.native.checked16 Airbender.Compiler.HelperNative.SubwordMemoryCached.native.inBank16
    input.physical (Airbender.Compiler.FunctionalLinksNative.SubwordMemoryCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.timestampFieldMatch7] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.SubwordMemoryCached.native.recipe16.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

/-- Native base arithmetic identifies each enabled expanded payload and mask
with its source interpretation, including every timestamp helper. -/
theorem nativeRequests_source (input : Input) (group : Fin 3) :
    nativeRequests input group = physicalRequests input group := by
  fin_cases group

  · change [MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding17.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf17.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding18.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf18.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding12.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf12.weight.value input.physical)] =
      [Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query17.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query18.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query12.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement)]
    exact (congrArg₂ List.cons (native_query17 input) (congrArg₂ List.cons (native_query18 input) (congrArg₂ List.cons (native_query12 input) rfl)))

  · change [MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding14.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf14.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding0.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf0.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding15.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf15.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding2.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf2.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding3.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf3.weight.value input.physical)] =
      [Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query14.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query0.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query15.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query2.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query3.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement)]
    exact (congrArg₂ List.cons (native_query14 input) (congrArg₂ List.cons (native_query0 input) (congrArg₂ List.cons (native_query15 input) (congrArg₂ List.cons (native_query2 input) (congrArg₂ List.cons (native_query3 input) rfl)))))

  · change [MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding4.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf4.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding6.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf6.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding7.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf7.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding8.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf8.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding9.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf9.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding10.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf10.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding11.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf11.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding16.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf16.weight.value input.physical)] =
      [MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields).get ⟨0, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields).get ⟨1, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields).get ⟨2, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields).get ⟨3, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields).get ⟨4, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields).get ⟨5, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields).get ⟨6, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields).get ⟨7, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues input.physical)] 1]
    exact (congrArg₂ List.cons (native_timestamp0 input) (congrArg₂ List.cons (native_timestamp1 input) (congrArg₂ List.cons (native_timestamp2 input) (congrArg₂ List.cons (native_timestamp3 input) (congrArg₂ List.cons (native_timestamp4 input) (congrArg₂ List.cons (native_timestamp5 input) (congrArg₂ List.cons (native_timestamp6 input) (congrArg₂ List.cons (native_timestamp7 input) rfl))))))))

/-- Every native query leaf occurs once, with the single setup leaf completing
exactly the retained native reduction tree's primitive multiset. -/
theorem nativeOperands_coverage (input : Input) (group : Fin 3) :
    (((nativeOperands input group).map Prod.fst) ++ [nativeSetupLeaf group]).Perm
      (([Airbender.Compiler.LookupNative.SubwordMemoryCached.native.genericTree,
      Airbender.Compiler.LookupNative.SubwordMemoryCached.native.range16Tree,
      Airbender.Compiler.LookupNative.SubwordMemoryCached.native.timestampTree]).get group).leaves := by
  fin_cases group

  · change ([17,
      18,
      12,
      13] : List Nat).Perm (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.genericTree).leaves
    exact Eq.mpr (congrArg (fun leaves : List Nat => ([17,
      18,
      12,
      13] : List Nat).Perm leaves)
      Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.genericLeavesChecked) (by decide +kernel)

  · change ([14,
      0,
      15,
      2,
      3,
      1] : List Nat).Perm (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.range16Tree).leaves
    exact Eq.mpr (congrArg (fun leaves : List Nat => ([14,
      0,
      15,
      2,
      3,
      1] : List Nat).Perm leaves)
      Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.range16LeavesChecked) (by decide +kernel)

  · change ([4,
      6,
      7,
      8,
      9,
      10,
      11,
      16,
      5] : List Nat).Perm (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.timestampTree).leaves
    exact Eq.mpr (congrArg (fun leaves : List Nat => ([4,
      6,
      7,
      8,
      9,
      10,
      11,
      16,
      5] : List Nat).Perm leaves)
      Airbender.Compiler.HelperNative.SubwordMemoryCached.native.leavesChecked) (by decide +kernel)

/-- Each designated native setup operand contains precisely the columns used
by the literal setup table in the corresponding logical argument. -/
theorem nativeSetupColumns_binding (group : Fin 3) :
    ([Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding13.columns,
      Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding1.columns,
      Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding5.columns]).get group =
      (Airbender.Compiler.MaterializedWitnessNative.SubwordMemoryCached.setupColumns group).map
        (fun column => AffineProgram.input (Address := GKRAddress) (R := Nat) column.address) := by
  fin_cases group
  · exact Airbender.Compiler.TableNative.SubwordMemoryCached.native.genericSetupColumnsPreserved
  · exact Airbender.Compiler.TableNative.SubwordMemoryCached.native.range16SetupColumnsPreserved
  · exact Airbender.Compiler.TableNative.SubwordMemoryCached.native.timestampSetupColumnsPreserved

private noncomputable def sourceArguments (input : Input) (arguments : LookupArguments input)
    (group : Fin 3) : LookupArgument
      (Airbender.Compiler.MaterializedNative.SubwordMemoryCached.native.model.fields
        (Airbender.Compiler.MaterializedWitnessNative.SubwordMemoryCached.setupColumns group))
      (activeLookupFields (physicalRequests input group)) := by
  simpa only [nativeRequests_source input group, Airbender.Compiler.MaterializedWitnessNative.SubwordMemoryCached.setupColumns] using arguments group
-- End native operand transport.

private theorem physical_member (input : Input) (arguments : LookupArguments input)
    (group : Fin 3) (query : MaterializedQuery)
    (member : query ∈ physicalRequests input group) (enabled : query.weight ≠ 0) :
    Airbender.Compiler.MaterializedNative.SubwordMemoryCached.native.model.Contains
      (Airbender.Compiler.MaterializedWitnessNative.SubwordMemoryCached.setupColumns group) query.fields :=
  LookupArgument.member (sourceArguments input arguments group) (activeLookupFields.member member enabled)

/-- Authored lookup membership is proved at physical coordinates, without a
canonical source frame, using exact matching of the emitted tuples. -/
theorem authored_from_arguments (input : Input) (arguments : LookupArguments input) :
    PhysicalAuthoredLookupValid input.physical := by
  constructor
  · intro query member enabled
    apply physical_member input arguments 0 (query.materialized
      ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement)) ?_ enabled
    simpa [physicalRequests] using
      (List.mem_map.mpr ⟨query, member, rfl⟩ :
        query.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement) ∈
          Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.genericQueries.map (fun item => item.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement)))
  · intro query member enabled
    apply physical_member input arguments 1 (query.materialized
      ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement)) ?_ enabled
    simpa [physicalRequests] using
      (List.mem_map.mpr ⟨query, member, rfl⟩ :
        query.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement) ∈
          Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.range16Queries.map (fun item => item.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement)))

/-- The complete literal timestamp column, including zero padding, bounds
actual physical helper values. No canonical borrow choice is imposed. -/
theorem helpers_from_arguments (input : Input) (arguments : LookupArguments input) :
    ∀ field ∈ Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields,
      (field.value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues input.physical)).val < 524288 := by
  intro field member
  let value := field.value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues input.physical)
  have present := physical_member input arguments 2 (MaterializedQuery.mk [value] 1)
    (by simpa [physicalRequests, value, Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues] using
          (List.mem_map.mpr ⟨field, member, rfl⟩ :
            MaterializedQuery.mk [field.value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues input.physical)] 1 ∈
              Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields.map (fun item => MaterializedQuery.mk
                [item.value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues input.physical)] 1))) one_ne_zero
  change Airbender.Compiler.MaterializedNative.SubwordMemoryCached.native.model.Contains [.timestamp] [value] at present
  exact Airbender.Compiler.MaterializedRangeNative.SubwordMemoryCached.native.timestamp_bounded value present

theorem input_active (input : Input) :
    (inputRow input).assignment (inputRow input).columns.execute = 1 := input.active

theorem input_constraints (input : Input) (arguments : LookupArguments input) {before : Reference.RiscV.Sail.State}
    (image : Trace.ROM.ImportedImage before) {cells : List Trace.Cell}
    {tokens : List (Trace.MemoryToken babyBearModulus)}
    (_physical : Trace.initialImage before cells = some tokens)
    (_domain : ROMNative.WordFullPublic.CoversROM cells) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (inputRow input).assignment)
      ((inputRow input).constraints (⟨Trace.ROM.table cells tokens,
        Verification.subwordTable (Trace.ROM.words before)⟩ : Trace.PooledSetup babyBearModulus)) := by
  have native := Airbender.Compiler.PhysicalClosedNative.SubwordMemoryCached.retained_clock_from_physical
    input.physical (fun _ _ => #[]) input.arithmetic (helpers_from_arguments input arguments)
    (authored_from_arguments input arguments)
  exact PublicConstraints.subword_transport _ _ _ native
    (fun _ member guard => ROMNative.SubwordPublic.public_table_refinement image member guard)

/-- Decode by transporting physical table membership directly through the
checked decoder-payload geometry. No canonical borrow frame is needed. -/
theorem input_decoded (input : Input) (arguments : LookupArguments input)
    (typed : (inputRow input).decoderQuery[0].val < 65536) :
    (Trace.decoderTable Trace.NativeDecoder.pooledProgram (inputRow input).family).Contains #[]
      (inputRow input).decoderQuery := by
  apply Airbender.Compiler.DecoderQueryNative.SubwordMemoryCached.program_from_source_membership (by decide +kernel)
    input.physical (fun _ _ => #[]) input.arithmetic typed
  apply (authored_from_arguments input arguments).1 Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query12
    Airbender.Compiler.DecoderQueryNative.SubwordMemoryCached.decoder_query_member
  rw [Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryCached.native.execute_weight input.physical (fun _ _ => #[]) input.arithmetic]
  have enabled : (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment input.physical (fun _ _ => #[])).get
      Airbender.SubwordMemory.importedConstraintsTraceColumns.execute = 1 := input.active
  have nonzero : (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment input.physical (fun _ _ => #[])).get
      Airbender.SubwordMemory.importedConstraintsTraceColumns.execute ≠ 0 :=
    fun zero => one_ne_zero (enabled.symm.trans zero)
  simpa [Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryCached.native.expression0, _root_.Expression.eval] using nonzero

end Airbender.Compiler.PooledRowNative.SubwordMemoryCached
