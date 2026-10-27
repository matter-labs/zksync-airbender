import Airbender.Import.Compiler.LogicalRows.AddSubCached
import Airbender.Proofs.GKRProtocol.LogicalLookup
import Airbender.Proofs.GKRProtocol.MaterializedRangeNative.AddSubCached
import Airbender.Proofs.GKRProtocol.PhysicalClosedNative.AddSubCached
import Airbender.Proofs.GKRProtocol.PooledRowNative.AddSubCached

namespace Airbender.Compiler.PooledRowNative.AddSubCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option linter.unusedVariables false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- The readable physical input contract has exactly the generated arithmetic
and execute-column interpretation; this equality changes no row condition. -/
theorem input_binding : Input = PhysicalRowInput
    (fun physical => ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates,
    gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0)
    (fun physical => (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical (fun _ _ => #[])).get
    Airbender.AddSub.importedConstraintsTraceColumns.execute = 1) := rfl

/-- The public address projection is exactly the retained generated Clean row
interpretation. This is a definitional binding, not an execution premise. -/
theorem inputRow_binding (input : Input) :
    inputRow input = (show Trace.Row babyBearModulus Trace.PooledFamily from
      ⟨.addSub, (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment input.physical (fun _ _ => #[])).get⟩) := rfl

/-- Explicit public column-group selection agrees with the retained captured
lookup reduction's group ordering. -/
theorem lookupArguments_binding (input : Input) : LookupArguments input =
    ((group : Fin 3) → LookupArgument
      (Airbender.Compiler.MaterializedNative.AddSubCached.native.model.fields
        (Airbender.Compiler.MaterializedWitnessNative.AddSubCached.setupColumns group))
      (activeLookupFields (nativeRequests input group))) := rfl

/-- Native base arithmetic transports the actual expanded operands to the
source-projected logical interface; none of the field equalities is a premise. -/
private theorem native_query14 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding14.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf14.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.AddSubCached.native.query14.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.AddSubCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.AddSubCached.native.sourceField14_1 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.AddSubCached.native.sourceField14_2 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.AddSubCached.native.sourceField14_3 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.AddSubCached.native.sourceField14_4 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.AddSubCached.native.sourceField14_5 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.AddSubCached.native.sourceField14_6 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.AddSubCached.native.sourceField14_7 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.AddSubCached.native.sourceField14_8 input.physical copies) rfl)))))))) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.sourceField14_0 input.physical copies)).symm

private theorem native_query0 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding0.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf0.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.AddSubCached.native.query0.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.AddSubCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.AddSubCached.native.sourceField0_0 input.physical copies) rfl) rfl).symm

private theorem native_query2 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding2.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf2.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.AddSubCached.native.query2.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.AddSubCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.AddSubCached.native.sourceField2_0 input.physical copies) rfl) rfl).symm

private theorem native_query3 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding3.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf3.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.AddSubCached.native.query3.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.AddSubCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.AddSubCached.native.sourceField3_0 input.physical copies) rfl) rfl).symm

private theorem native_query4 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding4.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf4.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.AddSubCached.native.query4.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.AddSubCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.AddSubCached.native.sourceField4_0 input.physical copies) rfl) rfl).symm

private theorem native_query5 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding5.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf5.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.AddSubCached.native.query5.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.AddSubCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.AddSubCached.native.sourceField5_0 input.physical copies) rfl) rfl).symm

private theorem native_query16 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding16.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf16.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.AddSubCached.native.query16.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.AddSubCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.AddSubCached.native.sourceField16_0 input.physical copies) rfl) rfl).symm

private theorem native_timestamp0 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding6.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf6.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.AddSubCached.native.fields).get ⟨0, by decide⟩).value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.AddSubCached.native.candidate6).sound
    Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank
    Airbender.Compiler.HelperNative.AddSubCached.native.checked6 Airbender.Compiler.HelperNative.AddSubCached.native.inBank6
    input.physical (Airbender.Compiler.FunctionalLinksNative.AddSubCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampFieldMatch0] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.AddSubCached.native.recipe6.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp1 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding8.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf8.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.AddSubCached.native.fields).get ⟨1, by decide⟩).value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.AddSubCached.native.candidate8).sound
    Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank
    Airbender.Compiler.HelperNative.AddSubCached.native.checked8 Airbender.Compiler.HelperNative.AddSubCached.native.inBank8
    input.physical (Airbender.Compiler.FunctionalLinksNative.AddSubCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampFieldMatch1] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.AddSubCached.native.recipe8.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp2 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding9.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf9.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.AddSubCached.native.fields).get ⟨2, by decide⟩).value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.AddSubCached.native.candidate9).sound
    Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank
    Airbender.Compiler.HelperNative.AddSubCached.native.checked9 Airbender.Compiler.HelperNative.AddSubCached.native.inBank9
    input.physical (Airbender.Compiler.FunctionalLinksNative.AddSubCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampFieldMatch2] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.AddSubCached.native.recipe9.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp3 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding10.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf10.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.AddSubCached.native.fields).get ⟨3, by decide⟩).value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.AddSubCached.native.candidate10).sound
    Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank
    Airbender.Compiler.HelperNative.AddSubCached.native.checked10 Airbender.Compiler.HelperNative.AddSubCached.native.inBank10
    input.physical (Airbender.Compiler.FunctionalLinksNative.AddSubCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampFieldMatch3] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.AddSubCached.native.recipe10.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp4 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding11.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf11.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.AddSubCached.native.fields).get ⟨4, by decide⟩).value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.AddSubCached.native.candidate11).sound
    Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank
    Airbender.Compiler.HelperNative.AddSubCached.native.checked11 Airbender.Compiler.HelperNative.AddSubCached.native.inBank11
    input.physical (Airbender.Compiler.FunctionalLinksNative.AddSubCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampFieldMatch4] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.AddSubCached.native.recipe11.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp5 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding12.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf12.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.AddSubCached.native.fields).get ⟨5, by decide⟩).value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.AddSubCached.native.candidate12).sound
    Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank
    Airbender.Compiler.HelperNative.AddSubCached.native.checked12 Airbender.Compiler.HelperNative.AddSubCached.native.inBank12
    input.physical (Airbender.Compiler.FunctionalLinksNative.AddSubCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampFieldMatch5] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.AddSubCached.native.recipe12.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp6 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding13.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf13.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.AddSubCached.native.fields).get ⟨6, by decide⟩).value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.AddSubCached.native.candidate13).sound
    Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank
    Airbender.Compiler.HelperNative.AddSubCached.native.checked13 Airbender.Compiler.HelperNative.AddSubCached.native.inBank13
    input.physical (Airbender.Compiler.FunctionalLinksNative.AddSubCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampFieldMatch6] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.AddSubCached.native.recipe13.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp7 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding17.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf17.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.AddSubCached.native.fields).get ⟨7, by decide⟩).value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.AddSubCached.native.candidate17).sound
    Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank
    Airbender.Compiler.HelperNative.AddSubCached.native.checked17 Airbender.Compiler.HelperNative.AddSubCached.native.inBank17
    input.physical (Airbender.Compiler.FunctionalLinksNative.AddSubCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampFieldMatch7] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.AddSubCached.native.recipe17.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

/-- Native base arithmetic identifies each enabled expanded payload and mask
with its source interpretation, including every timestamp helper. -/
theorem nativeRequests_source (input : Input) (group : Fin 3) :
    nativeRequests input group = physicalRequests input group := by
  fin_cases group

  · change [MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding14.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf14.weight.value input.physical)] =
      [Airbender.Compiler.LookupSourceNative.AddSubCached.native.query14.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement)]
    exact (congrArg₂ List.cons (native_query14 input) rfl)

  · change [MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding0.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf0.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding2.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf2.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding3.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf3.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding4.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf4.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding5.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf5.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding16.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf16.weight.value input.physical)] =
      [Airbender.Compiler.LookupSourceNative.AddSubCached.native.query0.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.AddSubCached.native.query2.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.AddSubCached.native.query3.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.AddSubCached.native.query4.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.AddSubCached.native.query5.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.AddSubCached.native.query16.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement)]
    exact (congrArg₂ List.cons (native_query0 input) (congrArg₂ List.cons (native_query2 input) (congrArg₂ List.cons (native_query3 input) (congrArg₂ List.cons (native_query4 input) (congrArg₂ List.cons (native_query5 input) (congrArg₂ List.cons (native_query16 input) rfl))))))

  · change [MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding6.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf6.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding8.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf8.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding9.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf9.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding10.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf10.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding11.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf11.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding12.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf12.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding13.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf13.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding17.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf17.weight.value input.physical)] =
      [MaterializedQuery.mk [((Airbender.Compiler.HelperNative.AddSubCached.native.fields).get ⟨0, by decide⟩).value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.AddSubCached.native.fields).get ⟨1, by decide⟩).value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.AddSubCached.native.fields).get ⟨2, by decide⟩).value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.AddSubCached.native.fields).get ⟨3, by decide⟩).value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.AddSubCached.native.fields).get ⟨4, by decide⟩).value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.AddSubCached.native.fields).get ⟨5, by decide⟩).value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.AddSubCached.native.fields).get ⟨6, by decide⟩).value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.AddSubCached.native.fields).get ⟨7, by decide⟩).value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues input.physical)] 1]
    exact (congrArg₂ List.cons (native_timestamp0 input) (congrArg₂ List.cons (native_timestamp1 input) (congrArg₂ List.cons (native_timestamp2 input) (congrArg₂ List.cons (native_timestamp3 input) (congrArg₂ List.cons (native_timestamp4 input) (congrArg₂ List.cons (native_timestamp5 input) (congrArg₂ List.cons (native_timestamp6 input) (congrArg₂ List.cons (native_timestamp7 input) rfl))))))))

/-- Every native query leaf occurs once, with the single setup leaf completing
exactly the retained native reduction tree's primitive multiset. -/
theorem nativeOperands_coverage (input : Input) (group : Fin 3) :
    (((nativeOperands input group).map Prod.fst) ++ [nativeSetupLeaf group]).Perm
      (([Airbender.Compiler.LookupNative.AddSubCached.native.genericTree,
      Airbender.Compiler.LookupNative.AddSubCached.native.range16Tree,
      Airbender.Compiler.LookupNative.AddSubCached.native.timestampTree]).get group).leaves := by
  fin_cases group

  · change ([14,
      15] : List Nat).Perm (Airbender.Compiler.LookupNative.AddSubCached.native.genericTree).leaves
    exact Eq.mpr (congrArg (fun leaves : List Nat => ([14,
      15] : List Nat).Perm leaves)
      Airbender.Compiler.LookupSourceNative.AddSubCached.native.genericLeavesChecked) (by decide +kernel)

  · change ([0,
      2,
      3,
      4,
      5,
      16,
      1] : List Nat).Perm (Airbender.Compiler.LookupNative.AddSubCached.native.range16Tree).leaves
    exact Eq.mpr (congrArg (fun leaves : List Nat => ([0,
      2,
      3,
      4,
      5,
      16,
      1] : List Nat).Perm leaves)
      Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16LeavesChecked) (by decide +kernel)

  · change ([6,
      8,
      9,
      10,
      11,
      12,
      13,
      17,
      7] : List Nat).Perm (Airbender.Compiler.LookupNative.AddSubCached.native.timestampTree).leaves
    exact Eq.mpr (congrArg (fun leaves : List Nat => ([6,
      8,
      9,
      10,
      11,
      12,
      13,
      17,
      7] : List Nat).Perm leaves)
      Airbender.Compiler.HelperNative.AddSubCached.native.leavesChecked) (by decide +kernel)

/-- Each designated native setup operand contains precisely the columns used
by the literal setup table in the corresponding logical argument. -/
theorem nativeSetupColumns_binding (group : Fin 3) :
    ([Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding15.columns,
      Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding1.columns,
      Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding7.columns]).get group =
      (Airbender.Compiler.MaterializedWitnessNative.AddSubCached.setupColumns group).map
        (fun column => AffineProgram.input (Address := GKRAddress) (R := Nat) column.address) := by
  fin_cases group
  · exact Airbender.Compiler.TableNative.AddSubCached.native.genericSetupColumnsPreserved
  · exact Airbender.Compiler.TableNative.AddSubCached.native.range16SetupColumnsPreserved
  · exact Airbender.Compiler.TableNative.AddSubCached.native.timestampSetupColumnsPreserved

private noncomputable def sourceArguments (input : Input) (arguments : LookupArguments input)
    (group : Fin 3) : LookupArgument
      (Airbender.Compiler.MaterializedNative.AddSubCached.native.model.fields
        (Airbender.Compiler.MaterializedWitnessNative.AddSubCached.setupColumns group))
      (activeLookupFields (physicalRequests input group)) := by
  simpa only [nativeRequests_source input group, Airbender.Compiler.MaterializedWitnessNative.AddSubCached.setupColumns] using arguments group
-- End native operand transport.

private theorem physical_member (input : Input) (arguments : LookupArguments input)
    (group : Fin 3) (query : MaterializedQuery)
    (member : query ∈ physicalRequests input group) (enabled : query.weight ≠ 0) :
    Airbender.Compiler.MaterializedNative.AddSubCached.native.model.Contains
      (Airbender.Compiler.MaterializedWitnessNative.AddSubCached.setupColumns group) query.fields :=
  LookupArgument.member (sourceArguments input arguments group) (activeLookupFields.member member enabled)

/-- Authored lookup membership is proved at physical coordinates, without a
canonical source frame, using exact matching of the emitted tuples. -/
theorem authored_from_arguments (input : Input) (arguments : LookupArguments input) :
    PhysicalAuthoredLookupValid input.physical := by
  constructor
  · intro query member enabled
    apply physical_member input arguments 0 (query.materialized
      ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement)) ?_ enabled
    simpa [physicalRequests] using
      (List.mem_map.mpr ⟨query, member, rfl⟩ :
        query.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement) ∈
          Airbender.Compiler.LookupSourceNative.AddSubCached.native.genericQueries.map (fun item => item.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement)))
  · intro query member enabled
    apply physical_member input arguments 1 (query.materialized
      ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement)) ?_ enabled
    simpa [physicalRequests] using
      (List.mem_map.mpr ⟨query, member, rfl⟩ :
        query.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement) ∈
          Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries.map (fun item => item.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement)))

/-- The complete literal timestamp column, including zero padding, bounds
actual physical helper values. No canonical borrow choice is imposed. -/
theorem helpers_from_arguments (input : Input) (arguments : LookupArguments input) :
    ∀ field ∈ Airbender.Compiler.HelperNative.AddSubCached.native.fields,
      (field.value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues input.physical)).val < 524288 := by
  intro field member
  let value := field.value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues input.physical)
  have present := physical_member input arguments 2 (MaterializedQuery.mk [value] 1)
    (by simpa [physicalRequests, value, Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues] using
          (List.mem_map.mpr ⟨field, member, rfl⟩ :
            MaterializedQuery.mk [field.value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues input.physical)] 1 ∈
              Airbender.Compiler.HelperNative.AddSubCached.native.fields.map (fun item => MaterializedQuery.mk
                [item.value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues input.physical)] 1))) one_ne_zero
  change Airbender.Compiler.MaterializedNative.AddSubCached.native.model.Contains [.timestamp] [value] at present
  exact Airbender.Compiler.MaterializedRangeNative.AddSubCached.native.timestamp_bounded value present

theorem input_active (input : Input) :
    (inputRow input).assignment (inputRow input).columns.execute = 1 := input.active

theorem input_constraints (input : Input) (arguments : LookupArguments input) {before : Reference.RiscV.Sail.State}
    (image : Trace.ROM.ImportedImage before) {cells : List Trace.Cell}
    {tokens : List (Trace.MemoryToken babyBearModulus)}
    (physical : Trace.initialImage before cells = some tokens)
    (domain : ROMNative.WordFullPublic.CoversROM cells) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (inputRow input).assignment)
      ((inputRow input).constraints (⟨Trace.ROM.table cells tokens,
        Verification.subwordTable (Trace.ROM.words before)⟩ : Trace.PooledSetup babyBearModulus)) := by
  have native := Airbender.Compiler.PhysicalClosedNative.AddSubCached.retained_clock_from_physical
    input.physical (fun _ _ => #[]) input.arithmetic (helpers_from_arguments input arguments)
    (authored_from_arguments input arguments)
  exact native

/-- Decode by transporting physical table membership directly through the
checked decoder-payload geometry. No canonical borrow frame is needed. -/
theorem input_decoded (input : Input) (arguments : LookupArguments input)
    (typed : (inputRow input).decoderQuery[0].val < 65536) :
    (Trace.decoderTable Trace.NativeDecoder.pooledProgram (inputRow input).family).Contains #[]
      (inputRow input).decoderQuery := by
  apply Airbender.Compiler.DecoderQueryNative.AddSubCached.program_from_source_membership (by decide +kernel)
    input.physical (fun _ _ => #[]) input.arithmetic typed
  apply (authored_from_arguments input arguments).1 Airbender.Compiler.LookupSourceNative.AddSubCached.native.query14
    Airbender.Compiler.DecoderQueryNative.AddSubCached.decoder_query_member
  rw [Airbender.Compiler.DecoderArgumentsNative.AddSubCached.native.execute_weight input.physical (fun _ _ => #[]) input.arithmetic]
  have enabled : (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment input.physical (fun _ _ => #[])).get
      Airbender.AddSub.importedConstraintsTraceColumns.execute = 1 := input.active
  have nonzero : (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment input.physical (fun _ _ => #[])).get
      Airbender.AddSub.importedConstraintsTraceColumns.execute ≠ 0 :=
    fun zero => one_ne_zero (enabled.symm.trans zero)
  simpa [Airbender.Compiler.DecoderArgumentsNative.AddSubCached.native.expression0, _root_.Expression.eval] using nonzero

end Airbender.Compiler.PooledRowNative.AddSubCached
